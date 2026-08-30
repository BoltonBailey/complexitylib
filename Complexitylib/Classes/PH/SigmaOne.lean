/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PH
public import Complexitylib.Classes.NP.CoNP
public import Complexitylib.Classes.PCP.Internal.GuessVerifyGeneric
public import Complexitylib.SAT.CookLevin.Assembly
public import Complexitylib.SAT.Headline
public import Complexitylib.Classes.Containments.Internal.FPBridge

/-!
# The first level of the hierarchy is `NP`

⚠️ Unreviewed by Bolton

`SigmaP 1` is the bounded existential closure of `P` — the certificate form of
`NP` — while `NP` itself is defined by nondeterministic machines. The two agree:

- `polyExistsClass P ⊆ NP` is guess-and-verify (`mem_NP_of_poly_witness`),
  once the witness bound is folded into the verifier as a length check.
- `NP ⊆ polyExistsClass P` goes through Cook–Levin: reduce to `SAT`, whose
  members are exactly the formulas with a short satisfying assignment, and
  check the assignment with the polynomial-time pair verifier.

## Main results

- `polyBoundLang_mem_P` — the length check `|snd z| ≤ p |fst z|` is in `P`
- `polyExistsClass_P_subset_NP`, `NP_subset_polyExistsClass_P`
- `SigmaP_one_eq_NP` — `SigmaP 1 = NP`
- `PiP_one_eq_coNP` — `PiP 1 = coNP`
- `NP_subset_PH`
-/

@[expose] public section

namespace Complexity

/-! ## The length check -/

/-- The pairs whose second component has length at most `p` of the first's. -/
noncomputable def polyBoundLang (p : Polynomial ℕ) : Language :=
  {z | (pairSnd z).length ≤ p.eval (pairFst z).length}

/-- The length check is polynomial-time: lay down a ruler of length
`p |fst z|` and compare lengths. -/
theorem polyBoundLang_mem_P (p : Polynomial ℕ) : polyBoundLang p ∈ P := by
  refine mem_P_of_decisionFn
    (lenLeFlagFn_mem_FP (polyRulerFn_mem_FP p Cobham.fstBlock_mem_FP) Cobham.sndBlock_mem_FP)
    fun z => ?_
  have key : (∃ b ∈ Cobham.lenLeFlag (polyRuler p (pairFst z)) (pairSnd z), b = true) ↔
      Cobham.lenLeFlag (polyRuler p (pairFst z)) (pairSnd z) = [true] := by
    rcases Cobham.lenLeFlag_flag (polyRuler p (pairFst z)) (pairSnd z) with h | h <;> simp [h]
  rw [key, Cobham.lenLeFlag_eq_true_iff, polyRuler_length]
  rfl

/-! ## The two inclusions -/

/-- **Certificates give `NP`**: a bounded existential over `P` is decided by
guessing the witness and running the verifier with the length check. -/
theorem polyExistsClass_P_subset_NP : polyExistsClass P ⊆ NP := by
  rintro L ⟨p, L', hL', rfl⟩
  refine mem_NP_of_poly_witness p (P_inter hL' (polyBoundLang_mem_P p)) ?_ ?_
  · intro x y hy
    simpa [polyBoundLang] using hy.2
  · intro x
    simp only [mem_polyExistsLang, Set.mem_inter_iff, polyBoundLang, Set.mem_setOf_eq,
      pairFst_pair, pairSnd_pair]
    exact ⟨fun ⟨w, h1, h2⟩ => ⟨w, h2, h1⟩, fun ⟨w, h1, h2⟩ => ⟨w, h2, h1⟩⟩

/-- **`NP` has certificates**: reduce to `SAT` by Cook–Levin and take a short
satisfying assignment of the image formula as the certificate. -/
theorem NP_subset_polyExistsClass_P : NP ⊆ polyExistsClass P := by
  intro L hL
  obtain ⟨f, hf, hiff⟩ := SAT.NPHard_language L hL
  obtain ⟨q, hq⟩ := Cobham.output_length_poly_of_mem_FP hf
  refine ⟨q + 1, (fun z => pair (f (pairFst z)) (pairSnd z)) ⁻¹' pairLang SAT.Witness,
    mem_P_preimage
      (Cobham.pairFn_mem_FP (mem_FP_comp Cobham.fstBlock_mem_FP hf) Cobham.sndBlock_mem_FP)
      SAT.pairLang_witness_mem_P, ?_⟩
  ext x
  rw [hiff x, SAT.mem_language_iff_witness, mem_polyExistsLang]
  simp only [Set.mem_preimage, pairFst_pair, pairSnd_pair, mem_pairLang_pair,
    Polynomial.eval_add, Polynomial.eval_one]
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨α, ?_, hα⟩
    obtain ⟨_, _, hlen, _⟩ := hα
    have := hq x
    omega
  · rintro ⟨w, _, hw⟩
    exact ⟨w, hw⟩

/-! ## The hierarchy levels -/

/-- **`SigmaP 1 = NP`.** -/
theorem SigmaP_one_eq_NP : SigmaP 1 = NP := by
  rw [SigmaP_one]
  exact subset_antisymm polyExistsClass_P_subset_NP NP_subset_polyExistsClass_P

/-- **`PiP 1 = coNP`.** -/
theorem PiP_one_eq_coNP : PiP 1 = coNP := by
  rw [PiP, SigmaP_one_eq_NP]
  rfl

/-- `NP` sits inside the polynomial hierarchy. -/
theorem NP_subset_PH : NP ⊆ PH :=
  SigmaP_one_eq_NP ▸ SigmaP_subset_PH 1

end Complexity
