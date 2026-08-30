/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Selection.Defs
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Selection.Internal

/-!
# Approximate-count selection

This module formalizes one selection round in the constructive Anti-Checker
Lemma. A minimum estimated extension exists because the input domain is finite.
If all estimates satisfy the relative-count contract, minimizing them transfers
a genuinely good input's survivor-count shrinkage to the chosen input.

The quantitative theorem is exact over natural numbers: when the relative
precision `p` and shrink denominator `d` satisfy `4 * d ≤ p + 3`, an existing
`1 / d` shrink gives the approximate minimizer a `1 / (2 * d)` shrink. At the
paper's parameters this is the passage from `1 / (2n)` to `1 / (4n)`.
-/


public section

namespace Complexity

namespace AntiChecker

/-- A minimum natural-valued estimate exists over the finite Boolean input
domain. -/
theorem exists_isEstimateMinimizer {arity : ℕ}
    (estimate : BitString arity → ℕ) :
    ∃ chosen, IsEstimateMinimizer estimate chosen :=
  exists_isEstimateMinimizer_internal estimate

/-- An approximate minimizer's true extension count is bounded by any other
extension's count, up to the relative-error factors. -/
theorem IsEstimateMinimizer.candidateSurvivorCount_le_scaled
    {arity precision threshold : ℕ}
    {target : BitString arity → Bool}
    {inputs : List (BitString arity)}
    {estimate : BitString arity → ℕ}
    {chosen other : BitString arity}
    (happrox :
      ApproximatesAllExtensions precision target threshold inputs estimate)
    (hminimum : IsEstimateMinimizer estimate chosen) :
    (precision - 1) *
        candidateSurvivorCount target threshold (chosen :: inputs) ≤
      (precision + 1) *
        candidateSurvivorCount target threshold (other :: inputs) :=
  hminimum.candidateSurvivorCount_le_scaled_internal happrox

/-- If some extension shrinks by `1 / denominator`, approximate minimization
gives the following exact scaled survivor-count bound. -/
theorem IsEstimateMinimizer.scaledShrink_of_hasShrinkExtension
    {arity precision denominator threshold : ℕ}
    {target : BitString arity → Bool}
    {inputs : List (BitString arity)}
    {estimate : BitString arity → ℕ}
    {chosen : BitString arity}
    (happrox :
      ApproximatesAllExtensions precision target threshold inputs estimate)
    (hminimum : IsEstimateMinimizer estimate chosen)
    (hgood : HasShrinkExtension denominator target threshold inputs) :
    denominator * (precision - 1) *
        candidateSurvivorCount target threshold (chosen :: inputs) ≤
      (precision + 1) * (denominator - 1) *
        candidateSurvivorCount target threshold inputs :=
  hminimum.scaledShrink_of_hasShrinkExtension_internal happrox hgood

/-- The arithmetic condition that makes relative error consume at most half of
the available shrinkage. -/
theorem relativeApproximation_coefficient_le
    {precision denominator : ℕ} (hprecision : 1 < precision)
    (hdenominator : 0 < denominator)
    (hbound : 4 * denominator ≤ precision + 3) :
    2 * (precision + 1) * (denominator - 1) ≤
      (precision - 1) * (2 * denominator - 1) :=
  relativeApproximation_coefficient_le_internal
    hprecision hdenominator hbound

/-- A minimum relative estimate inherits an existing `1 / denominator` shrink
as a `1 / (2 * denominator)` shrink. -/
theorem IsEstimateMinimizer.isShrinkExtension_double
    {arity precision denominator threshold : ℕ}
    {target : BitString arity → Bool}
    {inputs : List (BitString arity)}
    {estimate : BitString arity → ℕ}
    {chosen : BitString arity}
    (hprecision : 1 < precision)
    (hdenominator : 0 < denominator)
    (hbound : 4 * denominator ≤ precision + 3)
    (happrox :
      ApproximatesAllExtensions precision target threshold inputs estimate)
    (hminimum : IsEstimateMinimizer estimate chosen)
    (hgood : HasShrinkExtension denominator target threshold inputs) :
    IsShrinkExtension (2 * denominator) target threshold inputs chosen :=
  hminimum.isShrinkExtension_double_internal
    hprecision hdenominator hbound happrox hgood

end AntiChecker

end Complexity
