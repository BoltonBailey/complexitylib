#!/usr/bin/env python3
"""Drive and validate Complexitylib's Lean module-system migration.

This script is intentionally narrow: it updates the library sources, not the
standalone axiom-audit script.  The compatibility phase preserves declarations
that refer to private helpers in the same file.  After that compatibility build,
`lake shake` minimizes the migrated import graph before the temporary bridge is
removed:

Usage:
  python3 scripts/migrate_modules.py
  python3 scripts/migrate_modules.py --compat
  python3 scripts/migrate_modules.py --strict
  python3 scripts/migrate_modules.py --run
  python3 scripts/migrate_modules.py --check
  python3 scripts/migrate_modules.py --validate

On an unmigrated tree, `--run` checks the legacy build, applies the compatibility
migration, builds the module graph, minimizes imports, removes the compatibility
options, and runs every required project gate.  On an already migrated tree it
is an idempotent strict validation run.
"""

import argparse
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
LIBRARY = ROOT / "Complexitylib"
ROOT_MODULE = ROOT / "Complexitylib.lean"

COPYRIGHT_RE = re.compile(
    r"\A/-\n"
    r"Copyright \(c\) \d{4} .*\. All rights reserved\.\n"
    r"Released under Apache 2\.0 license as described in the file LICENSE\.\n"
    r"Authors: .*\n"
    r"-/\n"
)
MODULE_RE = re.compile(r"^module(?:\s+--.*)?$", re.MULTILINE)
LEGACY_IMPORT_RE = re.compile(
    r"^(?P<meta>meta\s+)?import(?!\s+all)(?=\s)",
    re.MULTILINE,
)
EXPOSE_SECTION = "@[expose] public section"
PRIVATE_IN_PUBLIC = "set_option backward.privateInPublic true"
PRIVATE_IN_PUBLIC_WARN = "set_option backward.privateInPublic.warn false"
VALIDATION_MODULES = [
    "Complexitylib.Classes.P.Cobham.Validation",
    "Complexitylib.Models.TuringMachine.SingleTape.Validation",
    "Complexitylib.Models.TuringMachine.Repetition.Validation",
    "Complexitylib.Circuits.Encoding.Validation",
    "Complexitylib.SAT.Tseitin.Machine.Validation",
]


def library_files() -> list[Path]:
    """Return every source file belonging to the public Lean library."""
    return [ROOT_MODULE, *sorted(LIBRARY.rglob("*.lean"))]


def block_comment_end(text: str, start: int) -> int:
    """Return the byte after a possibly nested Lean block comment."""
    depth = 0
    cursor = start
    while cursor < len(text):
        if text.startswith("/-", cursor):
            depth += 1
            cursor += 2
        elif text.startswith("-/", cursor):
            depth -= 1
            cursor += 2
            if depth == 0:
                return cursor
        else:
            cursor += 1
    raise ValueError("unterminated block comment")


def canonical_imports(header: str) -> str:
    """Canonicalize imports without discarding pre-docstring commands."""
    lines = header.splitlines()
    module_line = next(
        index
        for index, line in enumerate(lines)
        if MODULE_RE.fullmatch(line)
    )
    imports: list[tuple[bool, bool, bool, str]] = []
    seen = set()
    final_import_line = module_line
    cursor = module_line + 1
    while cursor < len(lines):
        stripped = lines[cursor].strip()
        public = False
        meta = False
        import_all = False
        imported = None
        if stripped.startswith(("public import", "public meta import", "import", "meta import")):
            tokens = stripped.split()
            if "import" in tokens:
                import_index = tokens.index("import")
                public = "public" in tokens[:import_index]
                meta = "meta" in tokens[:import_index]
                remainder = tokens[import_index + 1 :]
                if remainder and remainder[0] == "all":
                    import_all = True
                    remainder = remainder[1:]
                if remainder:
                    imported = remainder[0]
                elif cursor + 1 < len(lines):
                    continuation = lines[cursor + 1].strip()
                    if continuation and continuation[0].isupper():
                        imported = continuation
                        cursor += 1

        if imported is not None:
            imported = imported.split("--", 1)[0].strip()
            key = (public, meta, import_all, imported)
            if key not in seen:
                imports.append(key)
                seen.add(key)
            final_import_line = cursor
        cursor += 1

    rebuilt = lines[: module_line + 1]
    for public, meta, import_all, imported in imports:
        public_prefix = "public " if public else ""
        meta_prefix = "meta " if meta else ""
        all_suffix = " all" if import_all else ""
        import_command = f"{public_prefix}{meta_prefix}import{all_suffix}"
        import_line = f"{import_command} {imported}"
        if len(import_line) <= 100:
            rebuilt.append(import_line)
        else:
            indent = "  " if len(imported) + 2 <= 100 else ""
            rebuilt.extend([import_command, f"{indent}{imported}"])

    suffix = lines[final_import_line + 1 :]
    while suffix and not suffix[0].strip():
        suffix.pop(0)
    while suffix and not suffix[-1].strip():
        suffix.pop()
    if suffix:
        rebuilt.extend(["", *suffix])
    return "\n".join(rebuilt) + "\n\n"


def add_compatibility(text: str) -> str:
    """Allow public declarations to use private helpers from their own file."""
    module_doc = text.find("/-!")
    text = canonical_imports(text[:module_doc]) + text[module_doc:]
    if PRIVATE_IN_PUBLIC not in text:
        module_doc = text.find("/-!")
        module_doc_end = block_comment_end(text, module_doc)
        options = f"\n\n{PRIVATE_IN_PUBLIC}\n{PRIVATE_IN_PUBLIC_WARN}"
        text = text[:module_doc_end] + options + text[module_doc_end:]
    return text


def remove_compatibility(text: str) -> str:
    """Remove the temporary private-in-public migration bridge."""
    lines = text.splitlines()
    lines = [
        line
        for line in lines
        if line not in {PRIVATE_IN_PUBLIC, PRIVATE_IN_PUBLIC_WARN}
    ]
    return "\n".join(lines) + "\n"


def place_expose_section(text: str) -> str:
    """Place the public section outside any namespace opened before the doc."""
    module_doc = text.find("/-!")
    if module_doc < 0:
        raise ValueError("missing module docstring")
    scope = re.search(r"^(?:namespace|section)(?:\s|$)", text[:module_doc], re.MULTILINE)
    marker = text.find(EXPOSE_SECTION)

    if marker >= 0 and scope is not None and marker > scope.start():
        line_start = text.rfind("\n", 0, marker) + 1
        line_end = text.find("\n", marker)
        if line_end < 0:
            line_end = len(text)
        else:
            line_end += 1
        text = text[:line_start] + text[line_end:]
        module_doc = text.find("/-!")
        scope = re.search(
            r"^(?:namespace|section)(?:\s|$)",
            text[:module_doc],
            re.MULTILINE,
        )
        marker = -1

    if marker < 0:
        if scope is not None:
            text = (
                text[: scope.start()]
                + f"{EXPOSE_SECTION}\n\n"
                + text[scope.start() :]
            )
        else:
            doc_end = block_comment_end(text, module_doc)
            if text[doc_end:].strip():
                text = text[:doc_end] + f"\n\n{EXPOSE_SECTION}" + text[doc_end:]
    return text


def migrate(
    path: Path,
    compatibility: bool = False,
    strict: bool = False,
) -> str:
    """Return the compatibility-first module-system form of `path`."""
    text = path.read_text(encoding="utf-8")
    header = COPYRIGHT_RE.match(text)
    if header is None:
        raise ValueError("missing canonical copyright header")

    was_module = MODULE_RE.search(text) is not None
    if not was_module:
        text = text[: header.end()] + "\nmodule\n" + text[header.end() :]

    module_doc = text.find("/-!")
    if not was_module:
        text = (
            LEGACY_IMPORT_RE.sub(
                lambda match: f"public {match.group('meta') or ''}import",
                text[:module_doc],
            )
            + text[module_doc:]
        )

    text = place_expose_section(text)

    if compatibility:
        module_doc = text.find("/-!")
        doc_end = block_comment_end(text, module_doc)
        if text[doc_end:].strip():
            text = add_compatibility(text)
        else:
            text = canonical_imports(text[:module_doc]) + text[module_doc:]

    if strict:
        text = remove_compatibility(text)

    return text


def violations(
    path: Path,
    text: str,
    compatibility: bool = False,
    strict: bool = False,
) -> list[str]:
    """Return module-system migration invariants violated by `text`."""
    found = []
    if MODULE_RE.search(text) is None:
        found.append("missing module header")
    module_doc = text.find("/-!")
    if module_doc < 0:
        found.append("missing module docstring")
    else:
        doc_end = block_comment_end(text, module_doc)
        has_declarations = bool(text[doc_end:].strip())
        if has_declarations and EXPOSE_SECTION not in text:
            found.append("declarations are not in an exposed public section")
        if compatibility and has_declarations:
            if PRIVATE_IN_PUBLIC not in text or PRIVATE_IN_PUBLIC_WARN not in text:
                found.append("missing private-in-public compatibility options")
    if compatibility and module_doc >= 0 and has_declarations:
        if re.search(
            r"^public\s+(?:meta\s+)?import\s+all(?:\s|$)",
            text[:module_doc],
            re.MULTILINE,
        ):
            found.append("invalid combined `public import all`")
    if strict and (
        PRIVATE_IN_PUBLIC in text or PRIVATE_IN_PUBLIC_WARN in text
    ):
        found.append("temporary private-in-public compatibility option remains")
    return found


def update_sources(
    compatibility: bool,
    strict: bool = False,
) -> tuple[int, list[str]]:
    """Update all library files and return `(changed, errors)`."""
    changed = 0
    errors = []
    for path in library_files():
        try:
            old = path.read_text(encoding="utf-8")
            new = migrate(path, compatibility, strict)
            if new != old:
                path.write_text(new, encoding="utf-8")
                changed += 1
            for violation in violations(path, new, compatibility, strict):
                errors.append(f"{path.relative_to(ROOT)}: {violation}")
        except ValueError as error:
            errors.append(f"{path.relative_to(ROOT)}: {error}")
    return changed, errors


def run(command: list[str]) -> None:
    """Run one migration phase from the repository root."""
    print(f"+ {' '.join(command)}", flush=True)
    subprocess.run(command, cwd=ROOT, check=True)


def run_validation(include_full_build: bool = True) -> None:
    """Run every build, lint, and axiom gate required by AGENTS.md."""
    if include_full_build:
        run(["lake", "build", "--wfail"])
    for module in VALIDATION_MODULES:
        run(["lake", "build", "--wfail", module])
    run([sys.executable, "scripts/lint_style.py"])
    run(["lake", "exe", "runLinter", "Complexitylib", *VALIDATION_MODULES])
    run(["lake", "env", "lean", "scripts/AxiomGuard.lean"])


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--check",
        action="store_true",
        help="verify the migration invariants without editing files",
    )
    mode.add_argument(
        "--compat",
        action="store_true",
        help="also restore legacy visibility for the first complete build",
    )
    mode.add_argument(
        "--strict",
        action="store_true",
        help="remove temporary private-in-public compatibility options",
    )
    mode.add_argument(
        "--run",
        action="store_true",
        help="migrate when needed, then run every required project gate",
    )
    mode.add_argument(
        "--validate",
        action="store_true",
        help="run every required project gate without editing sources",
    )
    args = parser.parse_args()

    needs_migration = any(
        MODULE_RE.search(path.read_text(encoding="utf-8")) is None
        for path in library_files()
    )
    compatibility = args.compat or (args.run and needs_migration)
    if args.run and needs_migration:
        try:
            run(["lake", "build", "--wfail"])
        except subprocess.CalledProcessError as error:
            print(
                "module migration: the pre-migration build must pass before "
                "dependencies can be recovered",
                file=sys.stderr,
            )
            return error.returncode

    if args.validate:
        try:
            run_validation()
        except subprocess.CalledProcessError as error:
            print(
                f"module migration: command failed with exit code {error.returncode}",
                file=sys.stderr,
            )
            return error.returncode
        return 0

    if args.check:
        changed = 0
        errors = []
        for path in library_files():
            current = path.read_text(encoding="utf-8")
            try:
                for violation in violations(path, current, strict=True):
                    errors.append(f"{path.relative_to(ROOT)}: {violation}")
            except ValueError as error:
                errors.append(f"{path.relative_to(ROOT)}: {error}")
    else:
        changed, errors = update_sources(compatibility, args.strict)

    for error in errors:
        print(f"module migration: {error}")
    if errors:
        print(f"module migration: FAILED ({len(errors)} violation(s))")
        return 1

    if args.check:
        print(f"module migration: OK ({len(library_files())} modules)")
    else:
        print(f"module migration: updated {changed}/{len(library_files())} files")

    if args.run:
        try:
            if needs_migration:
                run(["lake", "build", "--wfail"])
                run(["lake", "shake", "--fix", "--add-public"])
                changed, errors = update_sources(
                    compatibility=False,
                    strict=True,
                )
                print(
                    f"module migration: strictified "
                    f"{changed}/{len(library_files())} files"
                )
                if errors:
                    for error in errors:
                        print(f"module migration: {error}")
                    return 1
            run(["lake", "build", "--wfail"])
            run_validation(include_full_build=False)
        except subprocess.CalledProcessError as error:
            print(
                f"module migration: command failed with exit code {error.returncode}",
                file=sys.stderr,
            )
            return error.returncode
    return 0


if __name__ == "__main__":
    sys.exit(main())
