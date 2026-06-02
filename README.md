# Complexitylib

A Lean 4 formalization of computational complexity theory, built on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Motivation

Complexity theory studies the resources required to solve computational problems — time, space, nondeterminism, randomness, and more. Despite its mathematical maturity, surprisingly little of the theory has been machine-checked. This library aims to build verified foundations for complexity classes, reductions, and the relationships between them.

## Approach

The definitions follow Arora and Barak's *Computational Complexity: A Modern Approach*:

- A concrete 4-symbol alphabet `{0, 1, □, ▷}`
- Deterministic TMs with a single transition function (AB Definition 1.1)
- Nondeterministic/probabilistic TMs with two transition functions `δ₀, δ₁` (AB Definition 2.1 / Section 7.1) — same machine structure, different acceptance semantics

Tapes are custom one-sided infinite (cell 0 is leftmost, head cannot move left of it), matching AB exactly. Configurations use named tapes (read-only input, read-write work tapes, read-write output), making the read-only/read-write distinction structural.

## Contents

| Module | Description |
|--------|-------------|
| `Complexitylib.Models.TuringMachine` | Alphabet, directions, TM, NTM, configurations, step/trace, acceptance, deciding, PTM counting, language type |

## Building

Requires [elan](https://github.com/leanprover/elan) (the Lean version manager).

```bash
lake build
```

The first build will download and compile Mathlib, which takes a while. Subsequent builds are incremental.

## Roadmap

- [x] Deterministic multi-tape Turing machine (AB Definition 1.1)
- [x] Nondeterministic TM with two transition functions (AB Definition 2.1)
- [x] Acceptance and deciding predicates (`Accepts`, `DecidesInTime`)
- [x] PTM counting primitives (`acceptCount`, `acceptProb`)
- [x] DTM-to-NTM embedding (`TM.toNTM`)
- [ ] Complexity classes (P, NP, BPP, PSPACE, ...)
- [ ] Reductions and completeness
- [ ] Simulation theorems
- [ ] Hierarchy theorems

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for commit format, code style, and guidelines.

## License

Licensed under the [Apache License, Version 2.0](LICENSE).
