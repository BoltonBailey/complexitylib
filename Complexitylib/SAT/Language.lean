import Complexitylib.SAT.Semantics
import Complexitylib.SAT.Encoding
import Complexitylib.Classes.Pairing
import Complexitylib.Classes.FNP

/-!
# SAT: Language and Witness Relation

This file defines the formal SAT language `L_SAT` and the NP witness
relation `R_SAT`, and proves the two core bridge theorems:

- `L_SAT_iff_witness` — `z ∈ L_SAT ↔ ∃ α, R_SAT z α`
  (a CNF is satisfiable iff it admits a short satisfying assignment)
- `R_SAT_polyBalanced` — witness length is bounded by `|z| + 1`
  (satisfying assignments can always be truncated to length `φ.maxVar + 1`,
  and `φ.maxVar ≤ |φ.encode|` from the unary encoding)

Together, these reduce `SAT ∈ NP` to showing `pairLang R_SAT ∈ P` —
i.e., that the *verifier* (decode φ, decode α, run CNF.eval) is
poly-time. The TM construction for that verifier is developed in the
subsequent phases (`SAT/Verifier.lean`).
-/

namespace SAT

/-- **The SAT language.** A bitstring `z` is in `L_SAT` iff it encodes
    some satisfiable CNF formula.

    Note: `encode` is injective on well-formed CNFs, but we don't need
    injectivity for any of the downstream theorems — we only need
    "there exists some `φ` …". -/
def L_SAT : Language := {z | ∃ φ : CNF, z = φ.encode ∧ φ.Satisfiable}

/-- **The SAT witness relation.** `R_SAT z α` holds when `z` encodes
    some CNF `φ`, `α` is a bit-string of length at most `|z| + 1`, and
    `α` satisfies `φ`.

    The `|z| + 1` length bound is what gives `PolyBalanced R_SAT`. It's
    always achievable because any satisfying assignment can be truncated
    to length `φ.maxVar + 1 ≤ |φ.encode| + 1 = |z| + 1`
    (`satisfiable_iff_short_witness` + `CNF.maxVar_le_encode_length`). -/
def R_SAT (z α : List Bool) : Prop :=
  ∃ φ : CNF, z = φ.encode ∧ α.length ≤ z.length + 1 ∧ CNF.eval α φ = true

-- ════════════════════════════════════════════════════════════════════════
-- Witness characterization: L_SAT iff ∃ witness
-- ════════════════════════════════════════════════════════════════════════

/-- **Witness characterization of `L_SAT`.** A string `z` is in `L_SAT`
    iff there exists a witness `α` with `R_SAT z α`.

    The forward direction uses `CNF.satisfiable_iff_short_witness` to
    produce a truncated witness, then applies `CNF.maxVar_le_encode_length`
    to bound its length by `|z| + 1`.

    The reverse direction is immediate: any `α` satisfying `φ` proves
    `φ.Satisfiable`. -/
theorem L_SAT_iff_witness (z : List Bool) :
    z ∈ L_SAT ↔ ∃ α, R_SAT z α := by
  constructor
  · rintro ⟨φ, hz, hsat⟩
    -- Extract a short witness using truncation lemma.
    rw [CNF.satisfiable_iff_short_witness] at hsat
    obtain ⟨α, hlen, heval⟩ := hsat
    refine ⟨α, φ, hz, ?_, heval⟩
    -- α.length ≤ φ.maxVar + 1 ≤ |φ.encode| + 1 = |z| + 1
    have : α.length ≤ φ.encode.length + 1 :=
      le_trans hlen (by have := CNF.maxVar_le_encode_length φ; omega)
    rw [hz]; exact this
  · rintro ⟨α, φ, hz, _, heval⟩
    exact ⟨φ, hz, α, heval⟩

-- ════════════════════════════════════════════════════════════════════════
-- PolyBalanced: witness length is bounded by a polynomial in |z|
-- ════════════════════════════════════════════════════════════════════════

/-- **Short-witness property for SAT.** The witness relation `R_SAT` is
    polynomially balanced: every valid witness has length at most
    `|z| + 1`, which is bounded by the degree-1 polynomial `X + 1`.

    This is the key structural fact that makes `SAT` a candidate for NP:
    we never need to guess more than linearly many bits. -/
theorem R_SAT_polyBalanced : PolyBalanced R_SAT := by
  refine ⟨Polynomial.X + Polynomial.C 1, ?_⟩
  intro z α hR
  obtain ⟨_, _, hlen, _⟩ := hR
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  exact hlen

-- ════════════════════════════════════════════════════════════════════════
-- Route to SAT ∈ NP
-- ════════════════════════════════════════════════════════════════════════
--
-- With `R_SAT_polyBalanced` in hand, SAT ∈ NP reduces to the single
-- remaining obligation: the verifier's pair language `pairLang R_SAT`
-- is in P. That is, there is a poly-time deterministic TM that, given
-- `pair(z, α)`, decides whether `R_SAT z α` holds — equivalently, that
-- parses `z` as a CNF and evaluates it at `α`.
--
-- Once that is proved, `R_SAT ∈ FNP` by definition; combined with a
-- generic NP-witness theorem (`L ∈ NP ↔ ∃ R ∈ FNP, L = {z | ∃ y, R z y}`),
-- this gives `L_SAT ∈ NP`. See `Complexitylib/SAT/Verifier.lean`
-- (forthcoming) for the TM construction.

/-- **SAT is in FNP modulo the verifier.** If the verifier's pair language
    is in P, then `R_SAT` is an FNP relation — and hence a candidate NP
    witness relation for `L_SAT`. The only nontrivial content is
    `R_SAT_polyBalanced`. -/
theorem R_SAT_in_FNP_of_verifier (h : pairLang R_SAT ∈ P) : R_SAT ∈ FNP :=
  ⟨R_SAT_polyBalanced, h⟩

-- ════════════════════════════════════════════════════════════════════════
-- Worked examples: end-to-end sanity check of the semantic layer
-- ════════════════════════════════════════════════════════════════════════

/-- `[[x₀]]` is satisfiable. Checked by the `decide` tactic using
    `CNF.decidableSatisfiable`. -/
example : CNF.Satisfiable [[{sign := true, var := 0}]] := by decide

/-- `[[x₀], [¬x₀]]` is unsatisfiable: no assignment can make both clauses true. -/
example : ¬ CNF.Satisfiable [[{sign := true, var := 0}], [{sign := false, var := 0}]] := by
  decide

/-- `[[x₀, ¬x₁], [x₁]]` is satisfiable: `α = [true, true]` works. -/
example : CNF.Satisfiable [[{sign := true, var := 0}, {sign := false, var := 1}],
                           [{sign := true, var := 1}]] := by decide

end SAT
