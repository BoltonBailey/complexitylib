# Complexitylib — Agent Guide

## Project Overview

A Lean 4 library formalizing computational complexity theory, built on Mathlib. The definitions follow Arora and Barak's *Computational Complexity: A Modern Approach*, using a concrete 4-symbol alphabet and separate deterministic/nondeterministic machine types. NTMs and PTMs share the same structure (two transition functions); they differ only in acceptance semantics (existential vs counting).

## Build

```bash
lake build
```

Always verify the build passes with **no errors and no warnings** before considering a change complete. (The sole exception is the `sorry` warning from `TM.toNTM_accepts_iff`, which is an explicitly stated stub.)

## Architecture

### Module Structure

```
Complexitylib.lean               — root import (re-exports everything)
Complexitylib/Models.lean        — aggregation import for computation models
Complexitylib/Models/TuringMachine.lean — Γ, Dir3, TM, NTM, Cfg, step/trace, acceptance, Language
```

Aggregation files (`Complexitylib.lean`, `Models.lean`) contain only `import` statements — no definitions.

### Key Design Decisions

- **Arora-Barak style**: Fixed alphabet `Γ = {0, 1, □, ▷}`, three-way directions (`Dir3`), explicit `qstart`/`qhalt` states.
- **Named tapes**: `Cfg` has separate `input : Tape`, `work : Fin n → Tape`, `output : Tape` fields. This avoids degenerate `Fin k` indexing and makes the read-only/read-write distinction structural.
- **DTM (`TM`)**: Single deterministic transition function `δ`. Execution via `step` (computable) and relational `stepRel`/`reaches`/`reachesIn`.
- **NTM (`NTM`)**: Two transition functions `δ₀, δ₁` selected by a `Bool`. Execution via `trace` (canonical, takes a fixed choice sequence). No parallel relational hierarchy — `trace` is the single source of truth.
- **Acceptance vs deciding**: `Accepts`/`AcceptsInTime` are existential. `DecidesInTime` requires halting on all inputs (DTM) or all paths (NTM) and correct output.
- **PTM counting**: `acceptCount` and `acceptProb` count/measure accepting paths over `Fin T → Bool`. Meaningful only when all paths halt within `T` steps.
- **Custom one-sided tapes**: `Tape` has `head : ℕ` and `cells : ℕ → Γ`. Cell 0 is leftmost and permanently `▷` (write is a no-op at cell 0). Moving left at position 0 is a no-op (Nat subtraction). Output is read from `cells 1` (first cell after `▷`). No dependency on `Mathlib.Computability.Tape`.
- **Read vs write alphabet**: `δ` reads `Γ = {0, 1, □, ▷}` but writes `Γw = {0, 1, □}`, structurally preventing writing `▷`. Combined with immutable cell 0, `▷` uniquely marks position 0 on every tape.
- **Finite state**: `TM` and `NTM` carry `[Fintype Q]`, matching AB's finite state requirement.

### Naming Conventions

Follow Mathlib style:
- `camelCase` for term-level definitions (`stepRel`, `initCfg`, `halted`, `trace`)
- `PascalCase` for types and Prop-valued definitions (`TM`, `NTM`, `Cfg`, `Accepts`, `DecidesInTime`)
- Namespace-qualified names for definitions that operate on a type (`TM.stepRel`, `NTM.trace`)

### Common Pitfalls

- **No `module` keyword** in aggregation files — they import files with definitions, and `module` files can only import other `module` files.
- **`List.get?` removed**: Use `l[i]?` (GetElem? syntax) instead of `l.get? i` in Lean 4 v4.28.0+.
- **Lambda expressions in conjunction chains** need explicit parens: `c'.work = (fun i => ...) ∧ ...`
- **`open` scoping**: `open Turing` is wrapped in a `section`/`end` block, not at module level.
- **`DecidableEq Q` and `Fintype Q`**: The `TM` and `NTM` structures carry these as instance fields, exposed via `attribute [instance]`. `DecidableEq` is needed for `if c.state = tm.qhalt` in `step`/`trace`; `Fintype` matches AB's finite state requirement.
- **Existential binders**: Use `∃ (T : ℕ) (choices : Fin T → Bool), ...` with explicit type annotations — omitting them causes parse errors.

## Commit Format

See CONTRIBUTING.md. Use `<type>(<scope>): <summary>` format with imperative mood.

## Dependencies

- **Lean**: `leanprover/lean4:v4.28.0` (see `lean-toolchain`)
- **Mathlib**: `v4.28.0` (see `lakefile.toml`)

When updating either, both must be updated in lockstep.
