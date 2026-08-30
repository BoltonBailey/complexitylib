/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Approximation.Defs
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Counting.Internal

/-!
# Relative survivor-count approximation -- proof internals
-/


public section

namespace Complexity

namespace AntiChecker

theorem isRelativeApproximation_exact_internal
    {precision actual : ℕ} (hprecision : 0 < precision) :
    IsRelativeApproximation precision actual actual := by
  unfold IsRelativeApproximation
  constructor
  · exact hprecision
  constructor
  · exact Nat.mul_le_mul_right actual (Nat.sub_le precision 1)
  · exact Nat.mul_le_mul_right actual (Nat.le_add_right precision 1)

theorem IsRelativeApproximation.estimate_eq_zero_of_actual_eq_zero_internal
    {precision actual estimate : ℕ}
    (happrox : IsRelativeApproximation precision actual estimate)
    (hactual : actual = 0) : estimate = 0 := by
  unfold IsRelativeApproximation at happrox
  have hzero : precision * estimate = 0 :=
    Nat.eq_zero_of_le_zero (by simpa [hactual] using happrox.2.2)
  exact (Nat.mul_eq_zero.mp hzero).resolve_left
    (Nat.ne_of_gt happrox.1)

theorem IsRelativeApproximation.actual_eq_zero_of_estimate_eq_zero_internal
    {precision actual estimate : ℕ} (hprecision : 1 < precision)
    (happrox : IsRelativeApproximation precision actual estimate)
    (hestimate : estimate = 0) : actual = 0 := by
  unfold IsRelativeApproximation at happrox
  have hzero : (precision - 1) * actual = 0 :=
    Nat.eq_zero_of_le_zero (by simpa [hestimate] using happrox.2.1)
  exact (Nat.mul_eq_zero.mp hzero).resolve_left (by omega)

theorem IsRelativeApproximation.estimate_eq_zero_iff_actual_eq_zero_internal
    {precision actual estimate : ℕ} (hprecision : 1 < precision)
    (happrox : IsRelativeApproximation precision actual estimate) :
    estimate = 0 ↔ actual = 0 := by
  constructor
  · exact happrox.actual_eq_zero_of_estimate_eq_zero_internal hprecision
  · exact happrox.estimate_eq_zero_of_actual_eq_zero_internal

theorem IsRelativeApproximation.actual_le_scaled_of_estimate_le_internal
    {precision firstActual firstEstimate secondActual secondEstimate : ℕ}
    (hfirst :
      IsRelativeApproximation precision firstActual firstEstimate)
    (hsecond :
      IsRelativeApproximation precision secondActual secondEstimate)
    (hestimate : firstEstimate ≤ secondEstimate) :
    (precision - 1) * firstActual ≤
      (precision + 1) * secondActual := by
  exact hfirst.2.1.trans <|
    (Nat.mul_le_mul_left precision hestimate).trans hsecond.2.2

theorem approximatesCandidateSurvivorCount_exact_internal
    {arity precision threshold : ℕ} (hprecision : 0 < precision)
    (target : BitString arity → Bool)
    (inputs : List (BitString arity)) :
    ApproximatesCandidateSurvivorCount precision target threshold inputs
      (candidateSurvivorCount target threshold inputs) := by
  exact isRelativeApproximation_exact_internal hprecision

theorem estimate_eq_zero_iff_isFor_internal
    {arity precision threshold estimate : ℕ} [NeZero arity]
    (hprecision : 1 < precision) (target : BitString arity → Bool)
    (inputs : List (BitString arity))
    (happrox :
      ApproximatesCandidateSurvivorCount precision target threshold inputs
        estimate) :
    estimate = 0 ↔ IsFor target threshold inputs := by
  rw [
    happrox.estimate_eq_zero_iff_actual_eq_zero_internal hprecision,
    candidateSurvivorCount_eq_zero_iff_isFor_internal]

end AntiChecker

end Complexity
