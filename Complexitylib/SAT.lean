import Complexitylib.SAT.Semantics
import Complexitylib.SAT.Encoding
import Complexitylib.SAT.Language

/-!
# SAT: Boolean satisfiability

This module formalizes the language **SAT** and a polynomial-time Turing
machine verifier for it.

## Submodules

- `Semantics` — `Lit`, `Clause`, `CNF`, `Assignment`, and the pure-recursive
  `CNF.eval`. This is the audit surface: whatever the verifier actually
  computes will be proved equal to `CNF.eval α φ`.
- `Encoding`  — `CNF.encode : CNF → List Bool`, the bit-level format the
  verifier parses.
- `Language`  — `L_SAT`, the witness relation `R_SAT`, and the proofs
  `L_SAT_iff_witness` / `R_SAT_polyBalanced` that reduce SAT ∈ NP to the
  decidability of the verifier's pair language.
-/
