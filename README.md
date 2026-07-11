# Complexitylib

A Lean 4 formalization of computational complexity theory, built on
[Mathlib](https://github.com/leanprover-community/mathlib4). The machine
model takes its shape from Arora and Barak's *Computational Complexity: A
Modern Approach*, but the library sets its own conventions — stated
precisely where they're used, with literature references where they help,
and unafraid to diverge from any one text when a cleaner formalization
exists.

## Ethos

**Statements you can audit, proofs you don't have to.** Every public theorem
is stated so a reader can check it means what it claims — concrete machine
model, explicit resource bounds, honest encodings — while the proof machinery
lives out of sight in `Internal` modules whose correctness is the type
checker's job, not yours.

**Concrete over abstract.** Machines, circuits, reductions, and encoders are
executable definitions, not existence claims. Complexity is measured on real
encodings; parsing, malformed inputs, and output conventions are explicit.
Constructions expose an exact resource bound first and an asymptotic
corollary second.

**Nothing on faith.** The library has no `sorry` and no custom axioms:
`scripts/AxiomGuard.lean` mechanically asserts that the headline theorems
depend only on Lean's three standard axioms, and CI enforces it — along with
Mathlib's style and environment linters — on every push.

## How to read the library

Everything lives in the `Complexity` root namespace and splits into areas,
each with its own entry module:

| Area | Import | What it is |
| --- | --- | --- |
| Machine models | `Complexitylib.Models` | Arora–Barak multi-tape Turing machines — deterministic, nondeterministic, probabilistic — and everything built from them: combinators, simulations, universal machines |
| Asymptotics | `Complexitylib.Asymptotics` | `=O`/`=o` notation on `ℕ → ℕ`, bridging to Mathlib's asymptotics |
| Complexity classes | `Complexitylib.Classes` | `P`, `NP`, `BPP`, `PSPACE`, and friends; containments, closure properties, reductions, and the time-hierarchy theorem |
| SAT | `Complexitylib.SAT` | CNF semantics and encoding, a verified SAT verifier, and the Cook–Levin theorem: `SAT` is NP-complete |
| Circuits | `Complexitylib.Circuits` | Boolean circuits with size and depth, circuit families, `P/poly`, normal forms, and classical lower bounds |
| Languages | `Complexitylib.Languages` | Concrete decidable languages exercising the machine API end to end |
| Mathlib prelude | `Complexitylib.Mathlib` | Extensions to Mathlib types in their home namespaces; candidates for upstreaming |

Within an area, modules follow one discipline:

- **`Foo/Defs.lean`** — definitions. Short, minimally-imported, auditable.
- **`Foo.lean`** — the surface: theorem statements worth reading.
- **`Foo/Internal…`** — proof machinery. Skip it; the type checker read it.

So: import `Complexitylib` (or one area), read `Defs` and surface files, and
trust the kernel for the rest. Headline results — Cook–Levin, universal-machine
simulation with explicit overhead, the deterministic time hierarchy — are
indexed in the root module `Complexitylib.lean` and mechanically guarded in `scripts/AxiomGuard.lean`.

## Building

Install [elan](https://github.com/leanprover/elan); Lean and Mathlib versions
are pinned (currently v4.30.0).

```bash
lake build --wfail
```

CI additionally runs two executable regression suites and three quality gates;
see [CONTRIBUTING.md](CONTRIBUTING.md) for the full list and the style guide.
API documentation builds with doc-gen4 from `docbuild/`.

## Contributing

[ROADMAP.md](ROADMAP.md) orders the open research programs by dependency —
from core API consolidation through uniform circuits, interactive proofs, and
formalized barriers — and breaks each into review-sized steps.
[CONTRIBUTING.md](CONTRIBUTING.md) covers style, layering, naming, and commit
conventions. Design notes for the larger completed constructions live in
`docs/`.

## License

Licensed under the [Apache License, Version 2.0](LICENSE).
