/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.ApproximateCounting.Power.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-!
# Cartesian powers for approximate counting -- proof internals
-/


public section

namespace Complexity

namespace ApproximateCounting

theorem mem_cartesianPower_iff_internal {domainWidth copies : ℕ}
    {set : Finset (BitString domainWidth)}
    {input : BitString (copies * domainWidth)} :
    input ∈ cartesianPower set copies ↔
      ∀ copy, blocksEquiv copies domainWidth input copy ∈ set := by
  classical
  simp [cartesianPower]

theorem card_cartesianPower_internal {domainWidth : ℕ}
    (set : Finset (BitString domainWidth)) (copies : ℕ) :
    (cartesianPower set copies).card = set.card ^ copies := by
  classical
  simp [cartesianPower]

private theorem two_mul_pow_le_add_one_pow (precision : ℕ)
    (hprecision : 0 < precision) :
    2 * precision ^ precision ≤ (precision + 1) ^ precision := by
  have hterm : precision * precision ^ (precision - 1) =
      precision ^ precision := by
    calc
      precision * precision ^ (precision - 1) =
          precision ^ (precision - 1) * precision := by ac_rfl
      _ = precision ^ (precision - 1 + 1) := by rw [pow_succ]
      _ = precision ^ precision := by
        congr 1
        omega
  have h := pow_add_mul_le_add_pow (R := ℕ) (a := precision) (b := 1)
    (by omega) (by omega) precision
  simpa [hterm, two_mul] using h

theorem relativeCopies_separates_sixteen_internal (precision : ℕ)
    (hprecision : 0 < precision) :
    16 ^ 2 * precision ^ relativeCopies precision ≤
      (precision + 1) ^ relativeCopies precision := by
  have hbase := two_mul_pow_le_add_one_pow precision hprecision
  have hpow := Nat.pow_le_pow_left hbase 8
  simpa [relativeCopies, mul_pow, pow_mul, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc] using hpow

theorem upperRootEstimate_isRelativeApproximation_internal
    {factor copies precision actual weakEstimate : ℕ}
    (hcopies : 0 < copies) (hprecision : 0 < precision)
    (hseparation :
      factor ^ 2 * precision ^ copies ≤ (precision + 1) ^ copies)
    (hweak : IsFactorApproximation factor (actual ^ copies) weakEstimate) :
    IsRelativeApproximation precision actual
      (upperRootEstimate factor copies weakEstimate) := by
  have hcopiesNe : copies ≠ 0 := Nat.ne_of_gt hcopies
  have hlower :
      actual ≤ upperRootEstimate factor copies weakEstimate := by
    rw [upperRootEstimate, Nat.le_nthRoot_iff hcopiesNe]
    exact hweak.2
  have hrootPow :
      (upperRootEstimate factor copies weakEstimate) ^ copies ≤
        factor ^ 2 * actual ^ copies := by
    calc
      (upperRootEstimate factor copies weakEstimate) ^ copies ≤
          factor * weakEstimate := by
        exact Nat.pow_nthRoot_le (.inl hcopiesNe)
      _ ≤ factor * (factor * actual ^ copies) :=
        Nat.mul_le_mul_left factor hweak.1
      _ = factor ^ 2 * actual ^ copies := by
        rw [pow_two]
        ac_rfl
  refine ⟨hprecision, ?_, ?_⟩
  · exact (Nat.mul_le_mul_left (precision - 1) hlower).trans <|
      Nat.mul_le_mul_right _ (Nat.sub_le precision 1)
  · by_contra hupper
    have hstrict :
        (precision + 1) * actual <
          precision * upperRootEstimate factor copies weakEstimate := by
      omega
    have hstrictPow :
        ((precision + 1) * actual) ^ copies <
          (precision * upperRootEstimate factor copies weakEstimate) ^ copies :=
      Nat.pow_lt_pow_left hstrict hcopiesNe
    have hcontradiction :
        ((precision + 1) * actual) ^ copies <
          ((precision + 1) * actual) ^ copies := by
      calc
        ((precision + 1) * actual) ^ copies <
            (precision * upperRootEstimate factor copies weakEstimate) ^ copies :=
          hstrictPow
        _ = precision ^ copies *
            (upperRootEstimate factor copies weakEstimate) ^ copies := by
          rw [mul_pow]
        _ ≤ precision ^ copies * (factor ^ 2 * actual ^ copies) :=
          Nat.mul_le_mul_left _ hrootPow
        _ = (factor ^ 2 * precision ^ copies) * actual ^ copies := by
          rw [pow_two]
          ac_rfl
        _ ≤ (precision + 1) ^ copies * actual ^ copies :=
          Nat.mul_le_mul_right _ hseparation
        _ = ((precision + 1) * actual) ^ copies := by
          rw [mul_pow]
    exact Nat.lt_irrefl _ hcontradiction

theorem boostedEstimate_isRelativeApproximation_internal
    {precision actual weakEstimate : ℕ} (hprecision : 0 < precision)
    (hweak : IsFactorApproximation 16
      (actual ^ relativeCopies precision) weakEstimate) :
    IsRelativeApproximation precision actual
      (boostedEstimate precision weakEstimate) := by
  apply upperRootEstimate_isRelativeApproximation_internal
  · simp [relativeCopies, hprecision]
  · exact hprecision
  · exact relativeCopies_separates_sixteen_internal precision hprecision
  · exact hweak

theorem boostedEstimate_cartesianPower_isRelativeApproximation_internal
    {domainWidth precision weakEstimate : ℕ}
    (set : Finset (BitString domainWidth)) (hprecision : 0 < precision)
    (hweak : IsFactorApproximation 16
      (cartesianPower set (relativeCopies precision)).card weakEstimate) :
    IsRelativeApproximation precision set.card
      (boostedEstimate precision weakEstimate) := by
  apply boostedEstimate_isRelativeApproximation_internal hprecision
  rwa [card_cartesianPower_internal] at hweak

end ApproximateCounting

end Complexity
