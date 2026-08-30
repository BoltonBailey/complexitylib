/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Approximation.Defs
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Approximation.Internal

/-!
# Relative survivor-count approximation

This module gives the relative approximate counter in the constructive
Anti-Checker Lemma an exact natural-number contract. Relative error
`1 / precision` is encoded by cross-multiplied inequalities, avoiding rational
rounding in the counter output.

The comparison theorem captures the reason approximate minimization works: if
the estimate for one candidate is no larger than another's, then their true
counts are ordered up to the two relative-error factors. Precision greater than
one also preserves whether the count is zero, hence whether a canonical sample
prefix is already an anti-checker.
-/


public section

namespace Complexity

namespace AntiChecker

/-- The exact count is a relative approximation at every positive
precision. -/
theorem isRelativeApproximation_exact
    {precision actual : ℕ} (hprecision : 0 < precision) :
    IsRelativeApproximation precision actual actual :=
  isRelativeApproximation_exact_internal hprecision

/-- A relative estimate of a zero count is zero. -/
theorem IsRelativeApproximation.estimate_eq_zero_of_actual_eq_zero
    {precision actual estimate : ℕ}
    (happrox : IsRelativeApproximation precision actual estimate)
    (hactual : actual = 0) : estimate = 0 :=
  happrox.estimate_eq_zero_of_actual_eq_zero_internal hactual

/-- At precision greater than one, a zero relative estimate has zero true
count. -/
theorem IsRelativeApproximation.actual_eq_zero_of_estimate_eq_zero
    {precision actual estimate : ℕ} (hprecision : 1 < precision)
    (happrox : IsRelativeApproximation precision actual estimate)
    (hestimate : estimate = 0) : actual = 0 :=
  happrox.actual_eq_zero_of_estimate_eq_zero_internal
    hprecision hestimate

/-- At precision greater than one, relative approximation preserves zero
exactly. -/
theorem IsRelativeApproximation.estimate_eq_zero_iff_actual_eq_zero
    {precision actual estimate : ℕ} (hprecision : 1 < precision)
    (happrox : IsRelativeApproximation precision actual estimate) :
    estimate = 0 ↔ actual = 0 :=
  happrox.estimate_eq_zero_iff_actual_eq_zero_internal hprecision

/-- Choosing no larger an estimate orders the true counts up to the lower and
upper relative-error factors. -/
theorem IsRelativeApproximation.actual_le_scaled_of_estimate_le
    {precision firstActual firstEstimate secondActual secondEstimate : ℕ}
    (hfirst :
      IsRelativeApproximation precision firstActual firstEstimate)
    (hsecond :
      IsRelativeApproximation precision secondActual secondEstimate)
    (hestimate : firstEstimate ≤ secondEstimate) :
    (precision - 1) * firstActual ≤
      (precision + 1) * secondActual :=
  hfirst.actual_le_scaled_of_estimate_le_internal hsecond hestimate

/-- The exact canonical survivor count satisfies the approximation contract at
every positive precision. -/
theorem approximatesCandidateSurvivorCount_exact
    {arity precision threshold : ℕ} (hprecision : 0 < precision)
    (target : BitString arity → Bool)
    (inputs : List (BitString arity)) :
    ApproximatesCandidateSurvivorCount precision target threshold inputs
      (candidateSurvivorCount target threshold inputs) :=
  approximatesCandidateSurvivorCount_exact_internal
    hprecision target inputs

/-- At precision greater than one, a canonical relative estimate is zero
exactly when the sample prefix is an anti-checker. -/
theorem estimate_eq_zero_iff_isFor
    {arity precision threshold estimate : ℕ} [NeZero arity]
    (hprecision : 1 < precision) (target : BitString arity → Bool)
    (inputs : List (BitString arity))
    (happrox :
      ApproximatesCandidateSurvivorCount precision target threshold inputs
        estimate) :
    estimate = 0 ↔ IsFor target threshold inputs :=
  estimate_eq_zero_iff_isFor_internal
    hprecision target inputs happrox

end AntiChecker

end Complexity
