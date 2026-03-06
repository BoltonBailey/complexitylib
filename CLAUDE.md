# Complexitylib — Agent Guide

## Project Overview

A Lean 4 library formalizing computational complexity theory, built on Mathlib. The central abstraction is a multi-tape monadic Turing machine parameterized over a monad with a `Possible` typeclass, allowing the same definitions to express deterministic, nondeterministic, and probabilistic computation.

## Build

```bash
lake build
```

Always verify the build passes with **no errors and no warnings** before considering a change complete.

## Architecture

### Module Structure

```
Complexitylib.lean               — root import (re-exports everything)
Complexitylib/Models.lean        — aggregation import for computation models
Complexitylib/Models/TuringMachine.lean — MultiTapeTM, Cfg, step relation, reachability
Complexitylib/Possible.lean      — Possible typeclass, Id, SetM, and PMF instances
```

Aggregation files (`Complexitylib.lean`, `Models.lean`) contain only `import` statements — no definitions.

### Key Design Decisions

- **Monad-parameterized TMs**: `MultiTapeTM` takes `(M : Type u → Type v) [Possible M]`. Use `Id` for deterministic, `SetM` for nondeterministic, `PMF` for probabilistic machines.
- **`Possible` typeclass**: Extracts a step *relation* from monadic computations via `possible : M α → α → Prop`. Laws ensure it respects `pure` and `>>=`.
- **Read-only input, write-only output**: The input tape only supports directional movement (no write). The output tape gets a `TapeAction` (write + move). This is enforced structurally in `stepRel`.
- **Universe polymorphism**: `Possible` uses `universe u v`. `MultiTapeTM`, `Cfg`, and `TapeAction` use `universe u v` matching `Possible`. `State` lives in `Type u` alongside `Symbol`.

### Naming Conventions

Follow Mathlib style:
- `camelCase` for term-level definitions (`stepRel`, `initCfg`, `halted`)
- `PascalCase` for types and Prop-valued definitions (`MultiTapeTM`, `Outputs`, `OutputsWithinTime`)
- Namespace-qualified names for definitions that operate on a type (`MultiTapeTM.stepRel`, `MultiTapeTM.reaches`)

### Common Pitfalls

- **No `module` keyword** in aggregation files — they import files with definitions, and `module` files can only import other `module` files.
- **`ListBlank.mk`** (not `List.toListBlank`) creates a `ListBlank` from a `List`.
- **Lambda expressions in conjunction chains** need explicit parens: `c'.work = (fun i => ...) ∧ ...`
- **Name shadowing in namespaces**: Inside `namespace MultiTapeTM`, `State` resolves to the `MultiTapeTM.State` projection. Use a different name (e.g. `S`) for fresh type variables that would otherwise shadow it.
- **`open` scoping**: `open Turing` is wrapped in a `section`/`end` block, not at module level.

## Commit Format

See CONTRIBUTING.md. Use `<type>(<scope>): <summary>` format with imperative mood.

## Dependencies

- **Lean**: `leanprover/lean4:v4.28.0` (see `lean-toolchain`)
- **Mathlib**: `v4.28.0` (see `lakefile.toml`)

When updating either, both must be updated in lockstep.
