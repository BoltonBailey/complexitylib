import Complexitylib.SAT.Semantics
import Complexitylib.SAT.Encoding
import Complexitylib.SAT.Language
import Complexitylib.SAT.Verifier
import Complexitylib.SAT.VerifierTM
import Complexitylib.SAT.GuessVerify
import Complexitylib.SAT.Headline
import Complexitylib.SAT.CookLevin

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
- `Language`  — `L_SAT`, the witness relation `R_SAT`, and the proofs
  `L_SAT_iff_witness` / `R_SAT_polyBalanced`.
- `Verifier` — executable decoding and checking for `pair(z, α)`.
- `VerifierTM` — deterministic TM components for the machine-level verifier.
- `GuessVerify` — the SAT-specialized composed NTM skeleton for
  counter setup, bounded guessing, pair construction, and verifier
  simulation.
-/
