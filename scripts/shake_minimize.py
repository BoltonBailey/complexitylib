#!/usr/bin/env python3
"""Shrink module interfaces under the Lean module system, verifying each step.

A module's interface is what downstream modules must rebuild against. Two
things inflate it here:

  * `public import X` re-exports X to everything downstream;
  * `@[expose]` puts a definition's *body* in the interface, not just its
    signature.

Both also constrain each other: a `public` declaration's signature may only
mention names from `public` imports, and an *exposed* definition's body must
too. So de-exposing first is what makes later import demotions legal — an
unexposed body may freely use a privately-imported name.

This script runs either shrink as a queue of candidates, applying them one at
a time (or one file at a time) and running the real gate build after each,
reverting anything that breaks. Three candidate kinds:

  unexpose  `@[expose] public section`  ->  `public section`
  demote    `public import X`           ->  `import X`   (used, but privately)
  delete    `public import X`           ->  (line gone)  (not used at all)

`unexpose` candidates are enumerated straight from the source; `demote` and
`delete` come from `lake shake`. Only shake's *removals* are applied — it also
suggests *additions*, both to restore a public closure it just narrowed and to
make transitive dependencies explicit, and those are deliberately ignored so
this script can only ever shrink an interface. A change that would have needed
a compensating `add` somewhere simply fails its build and is rolled back.

Typical use, expose pass before import pass:

    python3 scripts/shake_minimize.py --state .expose-minimize.json scan-expose
    python3 scripts/shake_minimize.py --state .expose-minimize.json apply

    lake build --wfail                      # shake needs up-to-date oleans
    python3 scripts/shake_minimize.py scan  # now sees the newly-legal demotions
    python3 scripts/shake_minimize.py apply
    python3 scripts/shake_minimize.py report

`apply` is resumable: state lives in the JSON file named by --state, is
rewritten after every verified step, and re-running `apply` picks up at the
first pending candidate. Interrupting with Ctrl-C (or `kill`) leaves the tree
in the last known-good state.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

# Targets that must build for a change to be accepted: the same set CI gates
# on (see CONTRIBUTING.md). `Complexitylib` covers the public import graph; the
# validation modules are regression guards intentionally kept out of it, so a
# demotion that only breaks them would otherwise slip through.
DEFAULT_TARGETS = [
    "Complexitylib",
    "Complexitylib.Models.TuringMachine.SingleTape.Validation",
    "Complexitylib.Models.TuringMachine.Repetition.Validation",
    "Complexitylib.Circuits.Encoding.Validation",
    "Complexitylib.SAT.Tseitin.Machine.Validation",
]

DEFAULT_STATE = ".shake-minimize.json"

# `  remove #[public import A, import B]`
SUGGESTION_RE = re.compile(r"^\s+(remove|add) #\[(.*)\]\s*$")
# One entry inside those brackets.
ENTRY_RE = re.compile(r"^(public )?(meta )?import ([A-Za-z0-9_.À-￿]+)$")
# A file heading in shake output: an absolute path followed by a colon.
HEADING_RE = re.compile(r"^(/.*\.lean):\s*$")

# A whole import statement. The module name may sit on a continuation line,
# since the 100-column style limit forces long imports to wrap.
IMPORT_STMT_RE = re.compile(
    r"^(?P<public>public[ \t]+)?(?P<meta>meta[ \t]+)?import"
    r"(?P<gap>[ \t]*\n?[ \t]*)(?P<mod>[A-Za-z0-9_.À-￿]+)(?P<trail>[^\n]*)$",
    re.MULTILINE,
)

MAX_COLS = 100

# The one interface-widening attribute this project uses, always in this exact
# form: a single blanket `@[expose] public section` per file.
EXPOSE_LINE = "@[expose] public section"
UNEXPOSED_LINE = "public section"


def render_import(module: str, gap: str, trail: str) -> str:
    """Render a private `import`, keeping the source's wrapping when needed."""
    flat = f"import {module}{trail}"
    if len(flat.rstrip()) <= MAX_COLS:
        return flat
    # Reuse the original continuation indent, or default to two spaces.
    indent = gap.split("\n")[-1] if "\n" in gap else "  "
    return f"import\n{indent}{module}{trail}"


@dataclass
class Candidate:
    file: str  # repo-relative
    module: str  # the imported module ("" for unexpose)
    action: str  # "unexpose" | "demote" | "delete"
    status: str = "pending"  # pending | applied | reverted | skipped
    note: str = ""
    seconds: float = 0.0

    def key(self) -> str:
        return f"{self.file}::{self.module}::{self.action}"

    def label(self) -> str:
        return f"{self.action} {self.module}".rstrip()


@dataclass
class State:
    targets: list[str] = field(default_factory=lambda: list(DEFAULT_TARGETS))
    candidates: list[Candidate] = field(default_factory=list)

    @staticmethod
    def load(path: Path) -> "State":
        raw = json.loads(path.read_text())
        return State(
            targets=raw.get("targets", list(DEFAULT_TARGETS)),
            candidates=[Candidate(**c) for c in raw["candidates"]],
        )

    def save(self, path: Path) -> None:
        tmp = path.with_suffix(path.suffix + ".tmp")
        tmp.write_text(
            json.dumps(
                {"targets": self.targets, "candidates": [asdict(c) for c in self.candidates]},
                indent=2,
            )
            + "\n"
        )
        tmp.replace(path)


def carry_over(candidates: list[Candidate], state_path: Path, args) -> None:
    """Preserve per-candidate results from an existing state file."""
    if not state_path.exists() or getattr(args, "reset", False):
        return
    old = {c.key(): c for c in State.load(state_path).candidates}
    for c in candidates:
        prev = old.get(c.key())
        if prev is None or prev.status == "pending":
            continue
        if getattr(args, "retry_reverted", False) and prev.status == "reverted":
            continue  # leave pending so this pass tries it again
        c.status, c.note, c.seconds = prev.status, prev.note, prev.seconds


# --------------------------------------------------------------------------
# import graph
# --------------------------------------------------------------------------


def module_name(rel: str) -> str:
    return rel[: -len(".lean")].replace("/", ".")


def source_files() -> list[str]:
    out = []
    for p in sorted(REPO_ROOT.rglob("*.lean")):
        if ".lake" in p.parts or "docbuild" in p.parts or "scripts" in p.parts:
            continue
        out.append(str(p.relative_to(REPO_ROOT)))
    return out


def dependent_counts(files: list[str]) -> dict[str, int]:
    """Map each file to the number of modules that transitively import it.

    De-exposing a module can only break things downstream of it, and the size
    of that cone is also what an accepted change costs to rebuild — so this
    doubles as a "try the cheap, certain wins first" ordering key.
    """
    owner = {module_name(f): f for f in files}
    importers: dict[str, set[str]] = {f: set() for f in files}
    for f in files:
        text = (REPO_ROOT / f).read_text()
        for m in IMPORT_STMT_RE.finditer(text):
            dep = owner.get(m.group("mod"))
            if dep is not None:
                importers[dep].add(f)

    counts: dict[str, int] = {}
    for f in files:
        seen: set[str] = set()
        stack = list(importers[f])
        while stack:
            g = stack.pop()
            if g in seen:
                continue
            seen.add(g)
            stack.extend(importers[g] - seen)
        counts[f] = len(seen)
    return counts


def file_sort_key(rel: str) -> tuple:
    """Order files most-downstream-first, so early builds rebuild the least."""
    parts = Path(rel).parts
    return (-len(parts), rel)


# --------------------------------------------------------------------------
# scan
# --------------------------------------------------------------------------


def parse_shake(text: str) -> list[tuple[str, str, str]]:
    """Parse shake output into (abs_file, module, action) removal candidates.

    A `public import X` that shake wants removed *and* re-added as a plain
    `import X` is a demotion; one it wants gone entirely is a deletion. An
    `import X` that shake wants promoted to `public import X` is not a removal
    and is dropped.
    """
    per_file: dict[str, dict[str, list[tuple[bool, str]]]] = {}
    current: str | None = None

    for line in text.splitlines():
        heading = HEADING_RE.match(line)
        if heading:
            current = heading.group(1)
            per_file.setdefault(current, {"remove": [], "add": []})
            continue
        suggestion = SUGGESTION_RE.match(line)
        if not suggestion or current is None:
            continue
        kind, body = suggestion.group(1), suggestion.group(2)
        for entry in (e.strip() for e in body.split(",") if e.strip()):
            m = ENTRY_RE.match(entry)
            if m:
                per_file[current][kind].append((bool(m.group(1)), m.group(3)))

    out: list[tuple[str, str, str]] = []
    for path, groups in per_file.items():
        added = {mod: is_public for is_public, mod in groups["add"]}
        for is_public, mod in groups["remove"]:
            if mod in added:
                if is_public and not added[mod]:
                    out.append((path, mod, "demote"))
                # public->public or private->public: not a removal.
            else:
                out.append((path, mod, "delete"))
    return out


def run_shake(extra_args: list[str], modules: list[str]) -> str:
    # Passing the targets explicitly makes shake cover the validation modules
    # too; without arguments it only walks the package's default targets.
    cmd = ["lake", "shake", *extra_args, *modules]
    print(f"$ {' '.join(cmd)}", flush=True)
    proc = subprocess.run(cmd, cwd=REPO_ROOT, capture_output=True, text=True)
    # shake exits non-zero when it has suggestions, which is the normal case.
    return proc.stdout + proc.stderr


def cmd_scan_expose(args: argparse.Namespace) -> int:
    state_path = REPO_ROOT / args.state
    targets = args.target or list(DEFAULT_TARGETS)

    files = [f for f in source_files() if EXPOSE_LINE in (REPO_ROOT / f).read_text()]
    cone = dependent_counts(source_files())
    files.sort(key=lambda f: (cone.get(f, 0), f))

    candidates = [Candidate(file=f, module="", action="unexpose") for f in files]
    carry_over(candidates, state_path, args)
    State(targets=targets, candidates=candidates).save(state_path)

    leaves = sum(1 for f in files if cone.get(f, 0) == 0)
    print(
        f"{len(candidates)} `{EXPOSE_LINE}` blanket(s) to try removing "
        f"({leaves} in modules nothing imports, so they cannot break anything downstream)."
    )
    print(f"state written to {state_path.relative_to(REPO_ROOT)}")
    return 0


def cmd_scan(args: argparse.Namespace) -> int:
    state_path = REPO_ROOT / args.state
    targets = args.target or list(DEFAULT_TARGETS)

    if args.from_file:
        text = Path(args.from_file).read_text()
    else:
        text = run_shake(args.shake_arg, targets)
        if args.save_output:
            Path(args.save_output).write_text(text)

    raw = parse_shake(text)
    if not raw:
        print("shake reported no removable imports.")

    candidates: list[Candidate] = []
    seen: set[str] = set()
    for abs_path, module, action in raw:
        try:
            rel = str(Path(abs_path).resolve().relative_to(REPO_ROOT))
        except ValueError:
            continue  # a file outside this package (e.g. a dependency)
        c = Candidate(file=rel, module=module, action=action)
        if c.key() in seen:
            continue
        seen.add(c.key())
        candidates.append(c)

    candidates.sort(key=lambda c: (file_sort_key(c.file), c.module))
    carry_over(candidates, state_path, args)
    State(targets=targets, candidates=candidates).save(state_path)

    demotes = sum(1 for c in candidates if c.action == "demote")
    deletes = sum(1 for c in candidates if c.action == "delete")
    files = len({c.file for c in candidates})
    carried = sum(1 for c in candidates if c.status != "pending")
    print(
        f"{len(candidates)} removal candidates across {files} files "
        f"({demotes} public->private demotions, {deletes} deletions)."
    )
    if carried:
        print(f"{carried} carried over from the previous state file.")
    print(f"state written to {state_path.relative_to(REPO_ROOT)}")
    return 0


# --------------------------------------------------------------------------
# apply
# --------------------------------------------------------------------------


class FileEditor:
    """Applies and reverts edits, keeping originals for rollback."""

    def __init__(self) -> None:
        self._originals: dict[str, str] = {}

    def snapshot(self, rel: str) -> None:
        if rel not in self._originals:
            self._originals[rel] = (REPO_ROOT / rel).read_text()

    def rollback(self, rel: str) -> None:
        if rel in self._originals:
            (REPO_ROOT / rel).write_text(self._originals.pop(rel))

    def commit(self, rel: str) -> None:
        self._originals.pop(rel, None)

    def rollback_all(self) -> None:
        for rel in list(self._originals):
            self.rollback(rel)

    def apply(self, c: Candidate) -> str | None:
        """Edit the file for candidate `c`. Returns a reason on skip, else None."""
        path = REPO_ROOT / c.file
        if not path.exists():
            return "file missing"
        text = path.read_text()

        if c.action == "unexpose":
            if text.count(EXPOSE_LINE) != 1:
                return f"expected exactly one `{EXPOSE_LINE}`"
            self.snapshot(c.file)
            path.write_text(text.replace(EXPOSE_LINE, UNEXPOSED_LINE, 1))
            return None

        matches = [m for m in IMPORT_STMT_RE.finditer(text) if m.group("mod") == c.module]
        if not matches:
            return "import statement not found"
        # A module can be imported both plainly and as `meta`; shake's
        # suggestion refers to the ordinary one, so never touch `meta` lines.
        plain = [m for m in matches if not m.group("meta")]
        if not plain:
            return "only a `meta import` statement matches"
        if len(plain) > 1:
            return "ambiguous: multiple import statements"

        m = plain[0]
        trail = m.group("trail") or ""
        if "shake: keep" in trail:
            return "annotated `-- shake: keep`"
        if not m.group("public") and c.action == "demote":
            return "already a private import"

        self.snapshot(c.file)
        start, end = m.start(), m.end()
        if c.action == "delete":
            # Also swallow the statement's trailing newline.
            replacement = ""
            if end < len(text) and text[end] == "\n":
                end += 1
        else:
            replacement = render_import(c.module, m.group("gap") or " ", trail)
        path.write_text(text[:start] + replacement + text[end:])
        return None


def build(targets: list[str], log: Path | None) -> tuple[bool, str]:
    cmd = ["lake", "build", "--wfail", *targets]
    proc = subprocess.run(cmd, cwd=REPO_ROOT, capture_output=True, text=True)
    output = proc.stdout + proc.stderr
    if log is not None:
        log.write_text(output)
    return proc.returncode == 0, output


def failure_excerpt(output: str, limit: int = 6) -> str:
    lines = [l for l in output.splitlines() if "error:" in l or l.startswith("✖")]
    if not lines:
        lines = output.strip().splitlines()[-limit:]
    return " | ".join(lines[:limit])[:500] or "(build failed with no output)"


def cmd_apply(args: argparse.Namespace) -> int:
    state_path = REPO_ROOT / args.state
    if not state_path.exists():
        print(f"no state file at {args.state}; run `scan` first.", file=sys.stderr)
        return 2
    state = State.load(state_path)
    targets = args.target or state.targets
    log = REPO_ROOT / args.build_log if args.build_log else None

    pending = [c for c in state.candidates if c.status == "pending"]
    if not pending:
        print("nothing pending.")
        return 0

    print(f"verifying baseline build of {' '.join(targets)} ...", flush=True)
    ok, output = build(targets, log)
    if not ok:
        print("baseline build FAILED; fix the tree before minimizing.", file=sys.stderr)
        print(failure_excerpt(output), file=sys.stderr)
        return 2
    print("baseline green.\n")

    # A plain `kill` would otherwise skip the rollback below and leave an
    # unverified edit in the tree; turn it into the same clean stop as Ctrl-C.
    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(KeyboardInterrupt))

    editor = FileEditor()
    # Group by file so `--granularity file` can batch, preserving queue order.
    groups: list[tuple[str, list[Candidate]]] = []
    for c in pending:
        if groups and groups[-1][0] == c.file:
            groups[-1][1].append(c)
        else:
            groups.append((c.file, [c]))
    if args.limit:
        if args.granularity == "file":
            groups = groups[: args.limit]
        else:
            flat, budget = [], args.limit
            for f, cs in groups:
                take = cs[:budget]
                if take:
                    flat.append((f, take))
                budget -= len(take)
                if budget <= 0:
                    break
            groups = flat

    applied = reverted = skipped = 0
    started = time.time()
    deadline = started + args.time_budget * 60 if args.time_budget else None

    def finish(c: Candidate, status: str, note: str, elapsed: float) -> None:
        nonlocal applied, reverted, skipped
        c.status, c.note, c.seconds = status, note, round(elapsed, 1)
        state.save(state_path)
        if status == "applied":
            applied += 1
        elif status == "reverted":
            reverted += 1
        else:
            skipped += 1

    def try_batch(batch: list[Candidate]) -> bool:
        """Apply a batch and build. True if kept; on failure everything reverts."""
        staged = []
        for c in batch:
            reason = editor.apply(c)
            if reason:
                finish(c, "skipped", reason, 0.0)
                print(f"  skip   {c.label()}  ({reason})")
            else:
                staged.append(c)
        if not staged:
            return True
        t0 = time.time()
        ok, _ = build(targets, log)
        elapsed = time.time() - t0
        if ok:
            for c in staged:
                editor.commit(c.file)
                finish(c, "applied", "", elapsed / len(staged))
            return True
        editor.rollback_all()
        return False

    try:
        for gi, (rel, batch) in enumerate(groups, 1):
            if deadline and time.time() > deadline:
                print(f"\ntime budget of {args.time_budget} min reached; stopping.")
                break
            done = applied + reverted
            eta = ""
            if done and deadline is None:
                rate = (time.time() - started) / done
                eta = f"  ~{rate * (len(pending) - done) / 3600:.1f}h left"
            head = f"[{gi}/{len(groups)}] {rel}{eta}"
            if args.granularity == "file" and len(batch) > 1:
                print(f"{head}: {len(batch)} changes (batched)", flush=True)
                if try_batch(batch):
                    kept = [c for c in batch if c.status == "applied"]
                    if kept:
                        print(f"  ok     {len(kept)} kept ({kept[0].seconds * len(kept):.0f}s)")
                    continue
                print("  batch failed; retrying one at a time", flush=True)
            else:
                print(f"{head}: {len(batch)} change(s)", flush=True)

            for c in batch:
                if c.status != "pending":
                    continue
                reason = editor.apply(c)
                if reason:
                    finish(c, "skipped", reason, 0.0)
                    print(f"  skip   {c.label()}  ({reason})")
                    continue
                t0 = time.time()
                ok, output = build(targets, log)
                elapsed = time.time() - t0
                if ok:
                    editor.commit(c.file)
                    finish(c, "applied", "", elapsed)
                    print(f"  ok     {c.label()}  ({elapsed:.0f}s)")
                else:
                    editor.rollback(c.file)
                    finish(c, "reverted", failure_excerpt(output), elapsed)
                    print(f"  revert {c.label()}  ({elapsed:.0f}s)")
                    print(f"         {c.note[:160]}")
    except KeyboardInterrupt:
        editor.rollback_all()
        state.save(state_path)
        print("\ninterrupted; uncommitted edits rolled back.", file=sys.stderr)
    finally:
        editor.rollback_all()
        state.save(state_path)

    total = time.time() - started
    print(
        f"\napplied {applied}, reverted {reverted}, skipped {skipped} "
        f"in {total / 60:.1f} min. "
        f"{sum(1 for c in state.candidates if c.status == 'pending')} still pending."
    )
    return 0


# --------------------------------------------------------------------------
# report
# --------------------------------------------------------------------------


def cmd_report(args: argparse.Namespace) -> int:
    state_path = REPO_ROOT / args.state
    if not state_path.exists():
        print(f"no state file at {args.state}; run `scan` first.", file=sys.stderr)
        return 2
    state = State.load(state_path)
    counts: dict[str, int] = {}
    for c in state.candidates:
        counts[c.status] = counts.get(c.status, 0) + 1
    print("candidates by status:")
    for k in ("applied", "reverted", "skipped", "pending"):
        if counts.get(k):
            print(f"  {k:9} {counts[k]}")
    print(f"  {'total':9} {len(state.candidates)}")

    if args.verbose:
        for status in ("reverted", "skipped"):
            rows = [c for c in state.candidates if c.status == status]
            if not rows:
                continue
            print(f"\n{status}:")
            for c in rows:
                print(f"  {c.file}: {c.label()}\n      {c.note[:200]}")
    return 0


def main() -> int:
    p = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    p.add_argument("--state", default=DEFAULT_STATE, help=f"state file (default {DEFAULT_STATE})")
    sub = p.add_subparsers(dest="cmd", required=True)

    s = sub.add_parser("scan", help="run lake shake and build the candidate queue")
    s.add_argument("--from-file", help="parse a saved `lake shake` output instead of running it")
    s.add_argument("--save-output", help="write raw shake output here")
    s.add_argument("--shake-arg", action="append", default=[], help="extra arg for `lake shake`")
    s.add_argument("--target", action="append", default=[], help="build target to verify against")
    s.add_argument("--reset", action="store_true", help="discard previous per-candidate results")
    s.add_argument(
        "--retry-reverted",
        action="store_true",
        help="re-queue candidates a previous pass reverted (e.g. after an expose pass)",
    )
    s.set_defaults(func=cmd_scan)

    e = sub.add_parser(
        "scan-expose",
        help=f"queue every blanket `{EXPOSE_LINE}` for removal (run this pass before `scan`)",
    )
    e.add_argument("--target", action="append", default=[], help="build target to verify against")
    e.add_argument("--reset", action="store_true", help="discard previous per-candidate results")
    e.add_argument(
        "--retry-reverted", action="store_true", help="re-queue candidates a previous pass reverted"
    )
    e.set_defaults(func=cmd_scan_expose)

    a = sub.add_parser("apply", help="apply pending candidates, verifying each with a build")
    a.add_argument(
        "--granularity",
        choices=["import", "file"],
        default="file",
        help="one build per import, or one build per file with per-import retry on failure "
        "(default: file)",
    )
    a.add_argument("--limit", type=int, help="stop after this many files (or imports)")
    a.add_argument(
        "--time-budget",
        type=float,
        default=0.0,
        help="stop cleanly after this many minutes (0 = no limit); the run is resumable",
    )
    a.add_argument("--target", action="append", default=[], help="override build targets")
    a.add_argument("--build-log", default="", help="write the last build's output here")
    a.set_defaults(func=cmd_apply)

    r = sub.add_parser("report", help="summarize the state file")
    r.add_argument("-v", "--verbose", action="store_true", help="list reverted/skipped candidates")
    r.set_defaults(func=cmd_report)

    args = p.parse_args()
    if shutil.which("lake") is None:
        print("`lake` not found on PATH.", file=sys.stderr)
        return 2
    os.chdir(REPO_ROOT)
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
