/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.StatisticalTest.Prediction.Defs

/-!
# The finite next-bit prediction experiment -- proof internals
-/


public section

namespace Complexity

namespace NextBitPrediction

private theorem indicator_identity (target atFalse atTrue : Bool) :
    (if predictFromTest atTrue true = target then (1 : ℚ) else 0) +
        (if predictFromTest atFalse false = target then (1 : ℚ) else 0) =
      1 + 2 * (if (if target then atTrue else atFalse) = true then 1 else 0) -
        ((if atTrue = true then 1 else 0) +
          (if atFalse = true then 1 else 0)) := by
  cases target <;> cases atFalse <;> cases atTrue <;>
    norm_num [predictFromTest, Bool.xor]

private theorem card_filter_cast_eq_sum_indicator {sample : Type*}
    [Fintype sample] (predicate : sample → Prop) [DecidablePred predicate] :
    (((Finset.univ.filter predicate).card : ℕ) : ℚ) =
      ∑ value : sample, if predicate value then 1 else 0 := by
  rw [Finset.card_filter]
  norm_cast

theorem successProbability_eq_half_add_gap_internal
    {background : Type*} [Fintype background] [Nonempty background]
    (target : background → Bool) (testAt : background → Bool → Bool) :
    successProbability target testAt =
      1 / 2 + targetAcceptanceProbability target testAt -
        candidateAcceptanceProbability testAt := by
  classical
  unfold successProbability targetAcceptanceProbability
    candidateAcceptanceProbability uniformProbability
  rw [card_filter_cast_eq_sum_indicator,
    card_filter_cast_eq_sum_indicator,
    card_filter_cast_eq_sum_indicator]
  rw [Fintype.card_prod, Fintype.card_bool]
  push_cast
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  have hpoint (omega : background) :
      (if predictFromTest (testAt omega true) true = target omega then
          (1 : ℚ) else 0) +
          (if predictFromTest (testAt omega false) false = target omega then
            (1 : ℚ) else 0) =
        1 + 2 * (if testAt omega (target omega) = true then 1 else 0) -
          ((if testAt omega true = true then 1 else 0) +
            (if testAt omega false = true then 1 else 0)) := by
    have hidentity := indicator_identity
      (target omega) (testAt omega false) (testAt omega true)
    cases htarget : target omega <;> simpa [htarget] using hidentity
  have hsum :
      (∑ omega : background,
        ((if predictFromTest (testAt omega true) true = target omega then
            (1 : ℚ) else 0) +
          (if predictFromTest (testAt omega false) false = target omega then
            (1 : ℚ) else 0))) =
        ∑ omega : background,
          (1 + 2 * (if testAt omega (target omega) = true then 1 else 0) -
            ((if testAt omega true = true then 1 else 0) +
              (if testAt omega false = true then 1 else 0))) := by
    apply Finset.sum_congr rfl
    intro omega _
    exact hpoint omega
  rw [hsum]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  have hcard : ((Fintype.card background : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

end NextBitPrediction

end Complexity
