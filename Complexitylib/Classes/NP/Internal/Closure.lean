/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.NP
public import Complexitylib.Classes.P.Internal.NormalForm
public import Complexitylib.Models.TuringMachine.Composition.Nondeterministic.Decides
public import Complexitylib.Languages.Trivial

/-!
# Closure of NP under polynomial-time preimages — proof internals

The preprocessing function is normalized to a natural-polynomial time bound
and composed with a polynomial-time nondeterministic decider through
`NTM.compositionNTM`. The degenerate decider that starts halted accepts
nothing, so its language is empty and the preimage is decided without
running the composite.
-/


public section

namespace Complexity

/-- Internal proof that `NP` membership is equivalent to nondeterministic
decision within the evaluation of a natural-coefficient polynomial. -/
theorem mem_NP_iff_decidesInTime_polynomial_internal {L : Language} :
    L ∈ NP ↔ ∃ (k : ℕ) (N : NTM k) (p : Polynomial ℕ),
      N.DecidesInTime L p.eval := by
  constructor
  · intro hL
    obtain ⟨d, k, N, T, hdec, hbig⟩ := Set.mem_iUnion.mp hL
    obtain ⟨p, hp⟩ := BigO.pow_polynomial_bound hbig
    exact ⟨k, N, p, hdec.mono hp⟩
  · rintro ⟨k, N, p, hdec⟩
    apply Set.mem_iUnion.mpr
    refine ⟨p.natDegree, k, N, p.eval, hdec, ?_⟩
    exact BigO.of_polynomial_bound p fun _ => le_rfl

/-- A nondeterministic decider that starts halted decides only the empty
language: its frozen trace leaves the output tape blank. -/
theorem language_eq_empty_of_decider_start_halted {k : ℕ} {N : NTM k}
    {L : Language} {T : ℕ → ℕ} (hN : N.DecidesInTime L T)
    (hstart : N.qstart = N.qhalt) : L = ∅ := by
  ext z
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hz
  obtain ⟨ch, hhalt, hout⟩ := (hN.2 z).mp hz
  rw [N.trace_halted _ _ (show (N.initCfg z).state = N.qhalt from hstart)] at hout
  simp [Tape.init] at hout

/-- Internal proof that polynomial-time nondeterministic languages are closed
under preimages of polynomial-time string functions. -/
theorem mem_NP_preimage_internal {f : List Bool → List Bool} {L : Language}
    (hf : f ∈ FP) (hL : L ∈ NP) : f ⁻¹' L ∈ NP := by
  obtain ⟨nf, tmF, p, hF⟩ :=
    mem_FP_iff_computesInTime_polynomial_internal.mp hf
  obtain ⟨ng, N, q, hN⟩ := mem_NP_iff_decidesInTime_polynomial_internal.mp hL
  by_cases hstart : N.qstart = N.qhalt
  · rw [language_eq_empty_of_decider_start_halted hN hstart]
    simpa [Language.empty] using empty_mem_NP
  · apply mem_NP_iff_decidesInTime_polynomial_internal.mpr
    refine ⟨_, NTM.compositionNTM tmF N,
      Polynomial.C 4 * p + Polynomial.C 11 + q.comp p, ?_⟩
    simpa [Polynomial.eval_comp] using
      NTM.compositionNTM_decidesInTime hF hN (polynomial_eval_mono_nat q) hstart

end Complexity
