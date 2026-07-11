#!/usr/bin/env python3
"""Style linter for Complexitylib.

Checks every `.lean` file under `Complexitylib/` for:

  copyright   — a Mathlib-style copyright header at the top of the file
  moduleDoc   — a module docstring (`/-! ... -/`)
  lineLength  — no line longer than 100 characters (lines containing URLs exempt)
  trailingWs  — no trailing whitespace
  finalNl     — file ends with exactly one newline
  rootEscape  — no `_root_.` escapes; they signal a nested namespace shadowing
                a root namespace (e.g. `SAT.TM` vs `TM`) or a declaration made
                outside its home namespace — fix the structure instead

Violations are compared against the baseline in `scripts/style-exceptions.txt`,
one `path : check` entry per line. A violation not in the baseline fails the
run; a baseline entry whose violation no longer exists also fails the run (so
the baseline only ever shrinks). Regenerate with `--update`.

Usage:
  python3 scripts/lint_style.py            # check
  python3 scripts/lint_style.py --update   # rewrite the baseline
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIBRARY = ROOT / "Complexitylib"
BASELINE = ROOT / "scripts" / "style-exceptions.txt"
MAX_LINE = 100

COPYRIGHT_RE = re.compile(
    r"\A/-\n"
    r"Copyright \(c\) \d{4} .*\. All rights reserved\.\n"
    r"Released under Apache 2\.0 license as described in the file LICENSE\.\n"
    r"Authors: .*\n"
    r"-/\n"
)
MODULE_DOC_RE = re.compile(r"^/-!", re.MULTILINE)
URL_RE = re.compile(r"https?://")


def check_file(path: Path) -> set[str]:
    """Return the set of check names that `path` violates."""
    text = path.read_text(encoding="utf-8")
    violations = set()
    if not COPYRIGHT_RE.match(text):
        violations.add("copyright")
    if not MODULE_DOC_RE.search(text):
        violations.add("moduleDoc")
    lines = text.split("\n")
    if any(len(line) > MAX_LINE and not URL_RE.search(line) for line in lines):
        violations.add("lineLength")
    if any(line != line.rstrip() for line in lines):
        violations.add("trailingWs")
    if not text.endswith("\n") or text.endswith("\n\n"):
        violations.add("finalNl")
    if "_root_." in text:
        violations.add("rootEscape")
    return violations


def collect() -> set[str]:
    """Return all current violations as `path : check` strings."""
    found = set()
    for path in sorted(LIBRARY.rglob("*.lean")) + [ROOT / "Complexitylib.lean"]:
        rel = path.relative_to(ROOT)
        for check in check_file(path):
            found.add(f"{rel} : {check}")
    return found


def read_baseline() -> set[str]:
    if not BASELINE.exists():
        return set()
    entries = set()
    for line in BASELINE.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if line and not line.startswith("#"):
            entries.add(line)
    return entries


def main() -> int:
    found = collect()
    if "--update" in sys.argv:
        header = (
            "# Style-lint baseline: pre-existing violations grandfathered during\n"
            "# the quality refactor. This file only shrinks; regenerate with\n"
            "#   python3 scripts/lint_style.py --update\n"
        )
        BASELINE.write_text(header + "\n".join(sorted(found)) + "\n", encoding="utf-8")
        print(f"style lint: baseline updated with {len(found)} entries")
        return 0

    baseline = read_baseline()
    new = sorted(found - baseline)
    stale = sorted(baseline - found)
    for entry in new:
        print(f"style lint: new violation: {entry}")
    for entry in stale:
        print(f"style lint: fixed but still in baseline (remove it): {entry}")
    if new or stale:
        return 1
    print(f"style lint: OK ({len(found)} grandfathered violations remain)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
