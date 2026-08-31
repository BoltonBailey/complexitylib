/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.ApproximateCounting.Relative.Defs
import Complexitylib.Classes.Randomized.ApproximateCounting.Power
import Complexitylib.Classes.Randomized.ApproximateCounting.Weak.Hashing

/-!
# Relative approximate counting -- proof internals
-/


public section

namespace Complexity

namespace ApproximateCounting

namespace Relative

private theorem factorApproximationEvent_subset_successEvent
    {domainWidth precision failureBits : ℕ}
    (set : Finset (BitString domainWidth))
    (hprecision : 0 < precision) :
    Weak.factorApproximationEvent
        (errorBits := errorBits domainWidth precision failureBits)
        (cartesianPower set (relativeCopies precision)) ⊆
      successEvent precision failureBits set := by
  intro seed hseed
  simp only [Weak.factorApproximationEvent, Finset.mem_filter,
    Finset.mem_univ, true_and] at hseed
  unfold successEvent
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact boostedEstimate_cartesianPower_isRelativeApproximation
    set hprecision hseed

private theorem add_four_le_two_pow_add_two (n : ℕ) :
    n + 4 ≤ 2 ^ (n + 2) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega, Nat.pow_succ]
      have hp : 1 ≤ 2 ^ (n + 2) := Nat.one_le_two_pow
      omega

private theorem add_four_div_two_pow_errorBits_le
    (n failureBits : ℕ) :
    (n + 4 : ℚ) / (2 : ℚ) ^ (n + 2 + failureBits) ≤
      1 / (2 : ℚ) ^ failureBits := by
  calc
    (n + 4 : ℚ) / (2 : ℚ) ^ (n + 2 + failureBits) ≤
        (2 : ℚ) ^ (n + 2) / (2 : ℚ) ^ (n + 2 + failureBits) := by
      gcongr
      exact_mod_cast add_four_le_two_pow_add_two n
    _ = 1 / (2 : ℚ) ^ failureBits := by
      have hdenominator :
          (2 : ℚ) ^ (n + 2 + failureBits) =
            (2 : ℚ) ^ (n + 2) * (2 : ℚ) ^ failureBits := by
        rw [show n + 2 + failureBits = (n + 2) + failureBits by omega,
          pow_add]
      rw [hdenominator]
      field_simp

theorem one_sub_two_pow_le_eventProb_successEvent_internal
    {domainWidth precision failureBits : ℕ}
    (set : Finset (BitString domainWidth)) (hprecision : 0 < precision) :
    1 - 1 / (2 : ℚ) ^ failureBits ≤
      eventProb (successEvent precision failureBits set) := by
  let width := poweredWidth domainWidth precision
  have herror := add_four_div_two_pow_errorBits_le width failureBits
  calc
    1 - 1 / (2 : ℚ) ^ failureBits ≤
        1 - (width + 4 : ℚ) /
          (2 : ℚ) ^ (width + 2 + failureBits) := by
      linarith
    _ ≤ eventProb
        (Weak.factorApproximationEvent
          (errorBits := errorBits domainWidth precision failureBits)
          (cartesianPower set (relativeCopies precision))) := by
      simpa [width, errorBits, poweredWidth] using
        Weak.one_sub_error_le_eventProb_factorApproximationEvent
          (errorBits := errorBits domainWidth precision failureBits)
          (cartesianPower set (relativeCopies precision))
    _ ≤ eventProb (successEvent precision failureBits set) :=
      eventProb_mono
        (factorApproximationEvent_subset_successEvent set hprecision)

theorem eventProb_failureEvent_le_two_pow_internal
    {domainWidth precision failureBits : ℕ}
    (set : Finset (BitString domainWidth)) (hprecision : 0 < precision) :
    eventProb (failureEvent precision failureBits set) ≤
      1 / (2 : ℚ) ^ failureBits := by
  rw [failureEvent, eventProb_compl]
  linarith [one_sub_two_pow_le_eventProb_successEvent_internal
    (failureBits := failureBits) set hprecision]

theorem three_fourths_le_eventProb_successEvent_internal
    {domainWidth precision : ℕ} (set : Finset (BitString domainWidth))
    (hprecision : 0 < precision) :
    3 / 4 ≤ eventProb (successEvent precision 2 set) := by
  calc
    3 / 4 = 1 - 1 / (2 : ℚ) ^ 2 := by norm_num
    _ ≤ eventProb (successEvent precision 2 set) :=
      one_sub_two_pow_le_eventProb_successEvent_internal set hprecision

end Relative

end ApproximateCounting

end Complexity
