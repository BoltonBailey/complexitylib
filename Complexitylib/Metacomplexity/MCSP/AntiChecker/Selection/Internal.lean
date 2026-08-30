/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Selection.Defs
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Approximation.Internal

/-!
# Approximate-count selection -- proof internals
-/


public section

namespace Complexity

namespace AntiChecker

theorem exists_isEstimateMinimizer_internal {arity : ℕ}
    (estimate : BitString arity → ℕ) :
    ∃ chosen, IsEstimateMinimizer estimate chosen := by
  classical
  let values := (Finset.univ : Finset (BitString arity)).image estimate
  have hvalues : values.Nonempty := by
    simp [values]
  have hminimum := Finset.min'_mem values hvalues
  rw [Finset.mem_image] at hminimum
  obtain ⟨chosen, _, hchosen⟩ := hminimum
  refine ⟨chosen, ?_⟩
  intro input
  rw [hchosen]
  exact Finset.min'_le values (estimate input) (by simp [values])

theorem IsEstimateMinimizer.candidateSurvivorCount_le_scaled_internal
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
        candidateSurvivorCount target threshold (other :: inputs) := by
  exact (happrox chosen).actual_le_scaled_of_estimate_le_internal
    (happrox other) (hminimum other)

theorem IsEstimateMinimizer.scaledShrink_of_hasShrinkExtension_internal
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
        candidateSurvivorCount target threshold inputs := by
  obtain ⟨other, hother⟩ := hgood
  have hcomparison :=
    hminimum.candidateSurvivorCount_le_scaled_internal
      happrox (other := other)
  calc
    denominator * (precision - 1) *
          candidateSurvivorCount target threshold (chosen :: inputs) =
        denominator *
          ((precision - 1) *
            candidateSurvivorCount target threshold (chosen :: inputs)) := by
      ring
    _ ≤ denominator *
          ((precision + 1) *
            candidateSurvivorCount target threshold (other :: inputs)) :=
      Nat.mul_le_mul_left denominator hcomparison
    _ = (precision + 1) *
          (denominator *
            candidateSurvivorCount target threshold (other :: inputs)) := by
      ring
    _ ≤ (precision + 1) *
          ((denominator - 1) *
            candidateSurvivorCount target threshold inputs) :=
      Nat.mul_le_mul_left (precision + 1) hother
    _ = (precision + 1) * (denominator - 1) *
          candidateSurvivorCount target threshold inputs := by
      ring

theorem relativeApproximation_coefficient_le_internal
    {precision denominator : ℕ} (hprecision : 1 < precision)
    (hdenominator : 0 < denominator)
    (hbound : 4 * denominator ≤ precision + 3) :
    2 * (precision + 1) * (denominator - 1) ≤
      (precision - 1) * (2 * denominator - 1) := by
  have hlinear :
      4 * (denominator - 1) ≤ precision - 1 := by
    omega
  have hpplus : precision + 1 = (precision - 1) + 2 := by
    omega
  have hdouble :
      2 * denominator - 1 = 2 * (denominator - 1) + 1 := by
    omega
  rw [hpplus, hdouble]
  ring_nf
  omega

theorem IsEstimateMinimizer.isShrinkExtension_double_internal
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
    IsShrinkExtension (2 * denominator) target threshold inputs chosen := by
  have hscaled :=
    hminimum.scaledShrink_of_hasShrinkExtension_internal happrox hgood
  have hcoefficient := relativeApproximation_coefficient_le_internal
    hprecision hdenominator hbound
  unfold IsShrinkExtension
  apply Nat.le_of_mul_le_mul_left (c := precision - 1) _ (by omega)
  calc
    (precision - 1) *
          ((2 * denominator) *
            candidateSurvivorCount target threshold (chosen :: inputs)) =
        2 *
          (denominator * (precision - 1) *
            candidateSurvivorCount target threshold (chosen :: inputs)) := by
      ring
    _ ≤ 2 *
          ((precision + 1) * (denominator - 1) *
            candidateSurvivorCount target threshold inputs) :=
      Nat.mul_le_mul_left 2 hscaled
    _ = (2 * (precision + 1) * (denominator - 1)) *
          candidateSurvivorCount target threshold inputs := by
      ring
    _ ≤ ((precision - 1) * (2 * denominator - 1)) *
          candidateSurvivorCount target threshold inputs :=
      Nat.mul_le_mul_right
        (candidateSurvivorCount target threshold inputs) hcoefficient
    _ = (precision - 1) *
          ((2 * denominator - 1) *
            candidateSurvivorCount target threshold inputs) := by
      ring

end AntiChecker

end Complexity
