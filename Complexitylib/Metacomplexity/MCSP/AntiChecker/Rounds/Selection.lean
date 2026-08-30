/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Rounds.Selection.Defs
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Rounds.Selection.Internal

/-!
# Approximate-selection round traces

Finite minimization generates a trace of any prescribed length from an
extension estimator. When that estimator relatively approximates every prefix
and every prefix has a genuinely shrinking extension, the trace satisfies the
composed shrink contract, including the factor-two loss from approximation.
-/


public section

namespace Complexity

namespace AntiChecker

/-- The empty list is a valid estimate-selection trace. -/
@[simp] theorem isEstimateSelectionTrace_nil {arity : ℕ}
    (estimator : List (BitString arity) → BitString arity → ℕ) :
    IsEstimateSelectionTrace estimator [] :=
  isEstimateSelectionTrace_nil_internal estimator

/-- Consing an input extends an estimate-selection trace exactly when it
minimizes the estimates for extensions of the existing tail. -/
@[simp] theorem isEstimateSelectionTrace_cons_iff {arity : ℕ}
    (estimator : List (BitString arity) → BitString arity → ℕ)
    (input : BitString arity) (inputs : List (BitString arity)) :
    IsEstimateSelectionTrace estimator (input :: inputs) ↔
      IsEstimateSelectionTrace estimator inputs ∧
        IsEstimateMinimizer (estimator inputs) input :=
  isEstimateSelectionTrace_cons_iff_internal estimator input inputs

/-- Repeated finite minimization produces an estimate-selection trace of any
requested length. -/
theorem exists_isEstimateSelectionTrace_length {arity : ℕ}
    (estimator : List (BitString arity) → BitString arity → ℕ)
    (rounds : ℕ) :
    ∃ inputs : List (BitString arity),
      inputs.length = rounds ∧ IsEstimateSelectionTrace estimator inputs :=
  exists_isEstimateSelectionTrace_length_internal estimator rounds

/-- Accurate approximate minimization turns every genuine `1/d` extension
into a composed `1/(2d)` shrink trace. -/
theorem IsEstimateSelectionTrace.isShrinkTrace
    {arity precision denominator threshold : ℕ}
    {target : BitString arity → Bool}
    {estimator : List (BitString arity) → BitString arity → ℕ}
    {inputs : List (BitString arity)}
    (hprecision : 1 < precision)
    (hdenominator : 0 < denominator)
    (hbound : 4 * denominator ≤ precision + 3)
    (happrox :
      ApproximatesEveryRound precision target threshold estimator)
    (hgood :
      ∀ samplePrefix : List (BitString arity),
        HasShrinkExtension denominator target threshold samplePrefix)
    (htrace : IsEstimateSelectionTrace estimator inputs) :
    IsShrinkTrace (2 * denominator) target threshold inputs :=
  htrace.isShrinkTrace_internal
    hprecision hdenominator hbound happrox hgood

/-- An accurate global estimator and genuine shrink at every prefix produce a
shrink trace of any requested length. -/
theorem exists_isShrinkTrace_length_of_approximatesEveryRound
    {arity precision denominator threshold : ℕ}
    {target : BitString arity → Bool}
    (estimator : List (BitString arity) → BitString arity → ℕ)
    (rounds : ℕ)
    (hprecision : 1 < precision)
    (hdenominator : 0 < denominator)
    (hbound : 4 * denominator ≤ precision + 3)
    (happrox :
      ApproximatesEveryRound precision target threshold estimator)
    (hgood :
      ∀ samplePrefix : List (BitString arity),
        HasShrinkExtension denominator target threshold samplePrefix) :
    ∃ inputs : List (BitString arity),
      inputs.length = rounds ∧
        IsShrinkTrace (2 * denominator) target threshold inputs :=
  exists_isShrinkTrace_length_of_approximatesEveryRound_internal
    estimator rounds hprecision hdenominator hbound happrox hgood

end AntiChecker

end Complexity
