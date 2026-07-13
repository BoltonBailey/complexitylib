/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.SAT.Semantics
import Complexitylib.SAT.Rename
import Complexitylib.SAT.ThreeCNF
import Complexitylib.SAT.ThreeSAT
import Complexitylib.SAT.ThreeSAT.Completeness
import Complexitylib.SAT.ThreeSAT.Syntax
import Complexitylib.SAT.Tseitin
import Complexitylib.SAT.Tseitin.Machine
import Complexitylib.SAT.QBF
import Complexitylib.SAT.Resolution
import Complexitylib.SAT.Encoding
import Complexitylib.SAT.Language
import Complexitylib.SAT.Verifier
import Complexitylib.SAT.Headline
import Complexitylib.SAT.ThreeSAT.Headline
import Complexitylib.SAT.CookLevin
import Complexitylib.SAT.CookLevin.Assembly

/-!
# SAT: Boolean satisfiability

This module formalizes the language **SAT** and the semantic/encoding
infrastructure used by the polynomial-time verifier.

## Submodules

- `Semantics` — `Lit`, `Clause`, `CNF`, `Assignment`, and the pure-recursive
  `CNF.eval`. This is the audit surface: whatever the verifier actually
  computes will be proved equal to `CNF.eval α φ`.
- `Encoding`  — `CNF.encode : CNF → List Bool`, the bit-level format the
  verifier parses.
- `ThreeSAT` / `Tseitin` — the exact-3 language, its linear-time syntax
  checker, total encoded reduction, equisatisfiability, and quadratic
  encoding-size bound; `Tseitin.Machine` proves the concrete reduction is in
  `FP`, and `ThreeSAT.Completeness` proves 3SAT is NP-complete.
- `Language`  — `language`, the witness relation `Witness`, and the proofs
  `mem_language_iff_witness` / `polyBalanced_witness`.
- `Verifier` — executable decoding and checking for `pair(z, α)`.
- `VerifierTM` — deterministic TM components for the machine-level verifier.
- `GuessVerify` — the proved SAT-specialized NTM composition for counter
  setup, bounded guessing, pair construction, and verifier simulation.
- `Headline` / `CookLevin.Assembly` — `SAT ∈ NP` and the final
  NP-completeness theorem.
-/
