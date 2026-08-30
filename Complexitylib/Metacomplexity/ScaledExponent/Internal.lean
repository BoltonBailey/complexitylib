/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.ScaledExponent.Defs

/-!
# Positive rational exponent scales -- proof internals
-/


public section

namespace Complexity

namespace PositiveRationalScale

private def commonLower (first second : PositiveRationalScale) :
    PositiveRationalScale where
  numerator := 1
  denominator := first.denominator * second.denominator
  numerator_pos := by decide
  denominator_pos := Nat.mul_pos first.denominator_pos second.denominator_pos

private theorem commonLower_le_left (first second : PositiveRationalScale) :
    commonLower first second ≤ first := by
  change value (commonLower first second) ≤ value first
  simp only [value, commonLower, Nat.cast_one, Nat.cast_mul]
  apply (div_le_div_iff₀
    (mul_pos (Nat.cast_pos.mpr first.denominator_pos)
      (Nat.cast_pos.mpr second.denominator_pos))
    (Nat.cast_pos.mpr first.denominator_pos)).mpr
  simp only [one_mul]
  have hnat :
      first.denominator ≤
        first.numerator * (first.denominator * second.denominator) := by
    calc
      first.denominator = 1 * first.denominator * 1 := by simp
      _ ≤ first.numerator * first.denominator * 1 :=
        Nat.mul_le_mul_right 1
          (Nat.mul_le_mul_right first.denominator first.numerator_pos)
      _ ≤ first.numerator * first.denominator * second.denominator :=
        Nat.mul_le_mul_left (first.numerator * first.denominator)
          second.denominator_pos
      _ = first.numerator * (first.denominator * second.denominator) := by
        simp [Nat.mul_assoc]
  simpa only [Nat.cast_mul] using (Nat.cast_le.mpr hnat :
    (first.denominator : ℚ) ≤
      (first.numerator * (first.denominator * second.denominator) : ℕ))

private theorem commonLower_le_right (first second : PositiveRationalScale) :
    commonLower first second ≤ second := by
  change value (commonLower first second) ≤ value second
  simp only [value, commonLower, Nat.cast_one, Nat.cast_mul]
  apply (div_le_div_iff₀
    (mul_pos (Nat.cast_pos.mpr first.denominator_pos)
      (Nat.cast_pos.mpr second.denominator_pos))
    (Nat.cast_pos.mpr second.denominator_pos)).mpr
  simp only [one_mul]
  have hnat :
      second.denominator ≤
        second.numerator * (first.denominator * second.denominator) := by
    calc
      second.denominator = 1 * second.denominator * 1 := by simp
      _ ≤ second.numerator * second.denominator * 1 :=
        Nat.mul_le_mul_right 1
          (Nat.mul_le_mul_right second.denominator second.numerator_pos)
      _ ≤ second.numerator * second.denominator * first.denominator :=
        Nat.mul_le_mul_left (second.numerator * second.denominator)
          first.denominator_pos
      _ = second.numerator *
          (first.denominator * second.denominator) := by
        ac_rfl
  simpa only [Nat.cast_mul] using (Nat.cast_le.mpr hnat :
    (second.denominator : ℚ) ≤
      (second.numerator * (first.denominator * second.denominator) : ℕ))

local instance : Nonempty PositiveRationalScale :=
  ⟨⟨1, 1, by decide, by decide⟩⟩

local instance : IsCodirectedOrder PositiveRationalScale where
  directed first second :=
    ⟨commonLower first second, commonLower_le_left first second,
      commonLower_le_right first second⟩

theorem value_pos_internal (scale : PositiveRationalScale) :
    0 < scale.value := by
  exact div_pos (Nat.cast_pos.mpr scale.numerator_pos)
    (Nat.cast_pos.mpr scale.denominator_pos)

theorem eventually_atZeroFromPositive_iff_internal
    {predicate : PositiveRationalScale → Prop} :
    (∀ᶠ scale in atZeroFromPositive, predicate scale) ↔
      ∃ cutoff, ∀ scale ≤ cutoff, predicate scale := by
  exact Filter.eventually_atBot

theorem floorMul_zero_internal (scale : PositiveRationalScale) :
    scale.floorMul 0 = 0 := by
  simp [floorMul]

theorem ceilMul_zero_internal (scale : PositiveRationalScale) :
    scale.ceilMul 0 = 0 := by
  simp [ceilMul]

theorem floorMul_mono_internal (scale : PositiveRationalScale) :
    Monotone scale.floorMul := by
  intro first second hle
  exact Nat.div_le_div_right (Nat.mul_le_mul_left scale.numerator hle)

theorem ceilMul_mono_internal (scale : PositiveRationalScale) :
    Monotone scale.ceilMul := by
  intro first second hle
  exact (gc_mul_ceilDiv scale.denominator_pos).monotone_l
    (Nat.mul_le_mul_left scale.numerator hle)

theorem denominator_mul_floorMul_le_internal
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.denominator * scale.floorMul n ≤ scale.numerator * n := by
  simpa [floorMul, Nat.mul_comm] using
    Nat.div_mul_le_self (scale.numerator * n) scale.denominator

theorem numerator_mul_le_denominator_mul_ceilMul_internal
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.numerator * n ≤ scale.denominator * scale.ceilMul n := by
  exact (ceilDiv_le_iff_le_mul scale.denominator_pos).mp le_rfl

theorem floorMul_le_ceilMul_internal
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.floorMul n ≤ scale.ceilMul n := by
  change (scale.numerator * n ⌊/⌋ scale.denominator) ≤
    (scale.numerator * n ⌈/⌉ scale.denominator)
  exact floorDiv_le_ceilDiv

theorem ceilMul_le_floorMul_add_one_internal
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.ceilMul n ≤ scale.floorMul n + 1 := by
  apply (ceilDiv_le_iff_le_mul scale.denominator_pos).mpr
  exact (Nat.lt_mul_div_succ (scale.numerator * n)
    scale.denominator_pos).le

theorem floorMul_pos_of_denominator_le_numerator_mul_internal
    (scale : PositiveRationalScale) {n : ℕ}
    (hlarge : scale.denominator ≤ scale.numerator * n) :
    0 < scale.floorMul n := by
  exact Nat.div_pos hlarge scale.denominator_pos

theorem powFloor_pos_internal (scale : PositiveRationalScale) (n : ℕ) :
    0 < scale.powFloor n := by
  exact Nat.two_pow_pos _

theorem powCeil_pos_internal (scale : PositiveRationalScale) (n : ℕ) :
    0 < scale.powCeil n := by
  exact Nat.two_pow_pos _

theorem powFloor_mono_internal (scale : PositiveRationalScale) :
    Monotone scale.powFloor := by
  intro first second hle
  exact Nat.pow_le_pow_right (by decide)
    (floorMul_mono_internal scale hle)

theorem powCeil_mono_internal (scale : PositiveRationalScale) :
    Monotone scale.powCeil := by
  intro first second hle
  exact Nat.pow_le_pow_right (by decide)
    (ceilMul_mono_internal scale hle)

theorem powFloor_le_powCeil_internal
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.powFloor n ≤ scale.powCeil n := by
  exact Nat.pow_le_pow_right (by decide)
    (floorMul_le_ceilMul_internal scale n)

theorem powCeil_le_two_mul_powFloor_internal
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.powCeil n ≤ 2 * scale.powFloor n := by
  calc
    scale.powCeil n ≤ 2 ^ (scale.floorMul n + 1) :=
      Nat.pow_le_pow_right (by decide)
        (ceilMul_le_floorMul_add_one_internal scale n)
    _ = 2 * scale.powFloor n := by
      simp [powFloor, pow_succ, Nat.mul_comm]

theorem onePlusCeilPow_eq_mul_internal
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.onePlusCeilPow n = 2 ^ n * scale.powCeil n := by
  simp [onePlusCeilPow, onePlusCeilExponent, pow_add, powCeil]

theorem two_pow_le_onePlusCeilPow_internal
    (scale : PositiveRationalScale) (n : ℕ) :
    2 ^ n ≤ scale.onePlusCeilPow n := by
  rw [onePlusCeilPow_eq_mul_internal]
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 ^ n)
    (Nat.succ_le_iff.mpr (powCeil_pos_internal scale n))

theorem onePlusCeilPowAtLength_pow_internal
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.onePlusCeilPowAtLength (2 ^ n) = scale.onePlusCeilPow n := by
  simp [onePlusCeilPowAtLength,
    Nat.log_pow (show 1 < (2 : ℕ) by decide)]

end PositiveRationalScale

end Complexity
