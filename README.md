# Complexitylib

Complexitylib is a Lean 4 formalization of computational complexity theory,
built on [Mathlib](https://github.com/leanprover-community/mathlib4). Its
machine definitions follow Arora and Barak's *Computational Complexity: A
Modern Approach*, while the library also develops Boolean circuit complexity,
randomized classes, reductions, universal simulation, and concrete languages.

The project aims for textbook-faithful, human-auditable statements backed by
fully checked constructions. The Lean modules contain no proof placeholders or
custom axioms.

## Current highlights

- Deterministic, nondeterministic, and probabilistic multi-tape Turing
  machines over a concrete four-symbol alphabet.
- Time, space, randomized, nonuniform, function, and search classes, including
  `P`, `PPoly` (`P/poly`), `NP`, `CoNP` (`coNP`), `PSPACE`, `BPP`, `RP`,
  `ZPP`, `PP`, `FNP`, and `TFNP`.
- Standard containments such as `P ⊆ NP`, `P ⊆ PSPACE`, `P ⊆ BPP`,
  `RP ⊆ NP`, and `BPP ⊆ PP`.
- A quadratic multi-tape-to-single-tape simulation and a fixed universal
  Turing machine with an explicit time bound.
- A weak deterministic time hierarchy theorem and concrete strict polynomial
  time separations.
- A machine-checked Cook–Levin development, including a polynomial-time SAT
  verifier and `SAT.NPComplete_L_SAT`.
- A finite Boolean-circuit model with circuit families, `P/poly`, canonical
  proof-free serialization and evaluation, normal forms, Shannon bounds,
  gate-elimination bounds, Schnorr's XOR lower bound, nondeterministic
  quantification, and depth-reduction results.
- Worked language deciders, including parity, `0ⁿ1ⁿ`, balanced strings,
  divisibility of length, and palindromes.

## Library map

| Area | Entry point | Contents |
| --- | --- | --- |
| Machine models | `Complexitylib.Models` | Tapes, configurations, TM/NTM semantics, subroutines, combinators, single-tape simulation, encodings, and universal machines |
| Asymptotics | `Complexitylib.Asymptotics` | Natural-valued big-O/little-o adapters and polynomial bounds |
| Complexity classes | `Complexitylib.Classes` | Time, space, randomized, function/search classes, containments, reductions, and hierarchy results |
| SAT | `Complexitylib.SAT` | CNF semantics and encoding, verifier machines, Cook–Levin, and NP-completeness |
| Circuits | `Complexitylib.Circuits` | Circuit semantics, fixed-length/list bridges, families, canonical encodings, bases, normal forms, lower bounds, AC⁰ definitions, and depth reduction |
| Examples | `Complexitylib.Languages` | Concrete languages with verified deciders and class memberships |

Import `Complexitylib` for the complete public development, or use an area
entry point to keep dependencies smaller.

## Machine model

The base model uses the fixed alphabet `Γ = {0, 1, □, ▷}` and a writable
subalphabet that excludes `▷`. Tapes are one-sided: cell `0` is the immutable
left-end marker, and moving left from it is a no-op. A configuration has a
read-only input tape, finitely many named work tapes, and a separate output
tape. Deterministic machines have one transition function; nondeterministic
and probabilistic machines share a two-branch transition structure and differ
in their acceptance semantics.

Definitions, internal proof machinery, and public theorem statements are
separated where the dependency graph warrants it. See [AGENTS.md](AGENTS.md)
for the architecture and proof-development conventions.

## Building and checking

Install [elan](https://github.com/leanprover/elan); the repository pins both
Lean and Mathlib, currently at v4.30.0.

```bash
lake build --wfail
```

The single-tape simulator also has an executable regression module. It is
kept out of the public import graph, so run it explicitly:

```bash
lake build --wfail Complexitylib.Models.TuringMachine.SingleTape.Validation
```

The encoded-circuit parser and evaluator have an analogous malformed-input
regression module:

```bash
lake build --wfail Complexitylib.Circuits.Encoding.Validation
```

The first build downloads and compiles Mathlib. Later builds are incremental.
CI runs the library and both regression modules, treating warnings as failures.

## Contributing

The project welcomes contributions at several scales:

- Small: foundational API lemmas, deduplication, documentation, executable
  regression cases, and additional concrete language deciders.
- Medium: closure properties, reductions, alternative machine simulations,
  circuit constructions, and reusable finite-combinatorics infrastructure.
- Large: uniform circuit characterizations, derandomization and nonuniformity,
  algebraic branching programs, interactive proofs, and formalized barriers.

The detailed [roadmap](ROADMAP.md) orders these programs by dependency and
breaks them into intermediate milestones suitable for future contributors and
coding agents. See [CONTRIBUTING.md](CONTRIBUTING.md) for style, validation,
and commit-message conventions.

## Design notes

The `docs/` directory contains construction notes for the universal machine,
single-tape simulation, SAT verifier, Cook–Levin emitter, and ongoing uniform
circuit bridge. Some documents are retained as historical implementation plans;
each such document is marked with its completion status.

## License

Licensed under the [Apache License, Version 2.0](LICENSE).
