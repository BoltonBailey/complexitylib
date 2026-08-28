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
  rootImport  — every non-Internal, non-Validation module is reachable from
                the public `Complexitylib` root import

This is a hard gate: any violation fails the run. The quality refactor cleared
every grandfathered violation, so there is no baseline to maintain.

Usage:
  python3 scripts/lint_style.py
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIBRARY = ROOT / "Complexitylib"
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
IMPORT_RE = re.compile(
    r"^(?:public |private )?import(?: all)?\s+([A-Za-z0-9_.]+)",
    re.MULTILINE,
)
NON_PUBLIC_COMPONENTS = {"Internal", "Validation"}


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


def module_name(path: Path) -> str:
    """Return the Lean module name corresponding to `path`."""
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def imported_modules(path: Path) -> set[str]:
    """Return the module names imported by `path`."""
    text = path.read_text(encoding="utf-8")
    header = text.split("/-!", 1)[0]
    return set(IMPORT_RE.findall(header))


def check_root_imports(paths: list[Path]) -> set[str]:
    """Return surface modules missing from the `Complexitylib` import graph."""
    modules = {module_name(path): path for path in paths}
    imports = {
        name: imported_modules(path) & modules.keys()
        for name, path in modules.items()
    }

    reachable = set()
    pending = ["Complexitylib"]
    while pending:
        name = pending.pop()
        if name in reachable:
            continue
        reachable.add(name)
        pending.extend(imports.get(name, set()))

    violations = set()
    for name, path in modules.items():
        components = set(path.relative_to(ROOT).with_suffix("").parts)
        if name not in reachable and components.isdisjoint(NON_PUBLIC_COMPONENTS):
            violations.add(f"{path.relative_to(ROOT)} : rootImport")
    return violations


def collect() -> set[str]:
    """Return all current violations as `path : check` strings."""
    paths = sorted(LIBRARY.rglob("*.lean")) + [ROOT / "Complexitylib.lean"]
    found = set()
    for path in paths:
        rel = path.relative_to(ROOT)
        for check in check_file(path):
            found.add(f"{rel} : {check}")
    found.update(check_root_imports(paths))
    return found


def main() -> int:
    found = sorted(collect())
    for entry in found:
        print(f"style lint: {entry}")
    if found:
        print(f"style lint: FAILED ({len(found)} violation(s))")
        return 1
    print("style lint: OK (no violations)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
