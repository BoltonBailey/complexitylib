# Complexitylib

A Lean 4 formalization of computational complexity theory, built on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Motivation

Complexity theory studies the resources required to solve computational problems — time, space, nondeterminism, randomness, and more. Despite its mathematical maturity, surprisingly little of the theory has been machine-checked. This library aims to build verified foundations for complexity classes, reductions, and the relationships between them.

## Approach

The library begins with formal models of computation and builds upward toward complexity classes and reductions. The Turing machine model uses a monadic transition function constrained by a `Possible` typeclass, so that the same definitions cover both deterministic and nondeterministic computation.

## Contents

| Module | Description |
|--------|-------------|
| `Complexitylib.Possible` | `Possible` typeclass with `Id` (deterministic) and `SetM` (nondeterministic) instances |
| `Complexitylib.Models.TuringMachine` | Multi-tape Turing machine with step relation, reachability, and output predicates |

## Building

Requires [elan](https://github.com/leanprover/elan) (the Lean version manager).

```bash
lake build
```

The first build will download and compile Mathlib, which takes a while. Subsequent builds are incremental.

## Roadmap

- [x] Multi-tape Turing machine model (deterministic and nondeterministic)
- [ ] Time and space complexity measures
- [ ] Complexity classes (P, NP, PSPACE, ...)
- [ ] Reductions and completeness
- [ ] Hierarchy theorems

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for commit format, code style, and guidelines.

## License

TBD
