/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.ScaledExponent.Defs
public import Complexitylib.Metacomplexity.ScaledExponent.Internal

/-!
# Positive rational exponent scales

This module exposes natural-number versions of the rational exponents used in
hardness magnification. Floor and ceiling differ by at most one in the exponent,
so their powers of two differ by at most a factor of two. It also provides the
exact power-of-two input-length identity for a rounded `N^(1+epsilon)` bound.
-/


public section

namespace Complexity

namespace PositiveRationalScale

/-- Scaling zero gives zero under floor rounding. -/
@[simp] theorem floorMul_zero (scale : PositiveRationalScale) :
    scale.floorMul 0 = 0 :=
  floorMul_zero_internal scale

/-- Scaling zero gives zero under ceiling rounding. -/
@[simp] theorem ceilMul_zero (scale : PositiveRationalScale) :
    scale.ceilMul 0 = 0 :=
  ceilMul_zero_internal scale

/-- Floor-scaled multiplication is monotone in the natural argument. -/
theorem floorMul_mono (scale : PositiveRationalScale) :
    Monotone scale.floorMul :=
  floorMul_mono_internal scale

/-- Ceiling-scaled multiplication is monotone in the natural argument. -/
theorem ceilMul_mono (scale : PositiveRationalScale) :
    Monotone scale.ceilMul :=
  ceilMul_mono_internal scale

/-- Floor rounding never exceeds the exact scaled numerator after restoring the
denominator. -/
theorem denominator_mul_floorMul_le
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.denominator * scale.floorMul n ≤ scale.numerator * n :=
  denominator_mul_floorMul_le_internal scale n

/-- Ceiling rounding covers the exact scaled numerator after restoring the
denominator. -/
theorem numerator_mul_le_denominator_mul_ceilMul
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.numerator * n ≤ scale.denominator * scale.ceilMul n :=
  numerator_mul_le_denominator_mul_ceilMul_internal scale n

/-- Floor rounding is no larger than ceiling rounding. -/
theorem floorMul_le_ceilMul (scale : PositiveRationalScale) (n : ℕ) :
    scale.floorMul n ≤ scale.ceilMul n :=
  floorMul_le_ceilMul_internal scale n

/-- Floor and ceiling rounding differ by at most one. -/
theorem ceilMul_le_floorMul_add_one
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.ceilMul n ≤ scale.floorMul n + 1 :=
  ceilMul_le_floorMul_add_one_internal scale n

/-- Once the unrounded numerator reaches the denominator, its floor-scaled
value is positive. -/
theorem floorMul_pos_of_denominator_le_numerator_mul
    (scale : PositiveRationalScale) {n : ℕ}
    (hlarge : scale.denominator ≤ scale.numerator * n) :
    0 < scale.floorMul n :=
  floorMul_pos_of_denominator_le_numerator_mul_internal scale hlarge

/-- Rounded-down powers of two are positive. -/
theorem powFloor_pos (scale : PositiveRationalScale) (n : ℕ) :
    0 < scale.powFloor n :=
  powFloor_pos_internal scale n

/-- Rounded-up powers of two are positive. -/
theorem powCeil_pos (scale : PositiveRationalScale) (n : ℕ) :
    0 < scale.powCeil n :=
  powCeil_pos_internal scale n

/-- Rounded-down powers are monotone in the natural argument. -/
theorem powFloor_mono (scale : PositiveRationalScale) :
    Monotone scale.powFloor :=
  powFloor_mono_internal scale

/-- Rounded-up powers are monotone in the natural argument. -/
theorem powCeil_mono (scale : PositiveRationalScale) :
    Monotone scale.powCeil :=
  powCeil_mono_internal scale

/-- Rounding the exponent down gives no larger a power than rounding it up. -/
theorem powFloor_le_powCeil (scale : PositiveRationalScale) (n : ℕ) :
    scale.powFloor n ≤ scale.powCeil n :=
  powFloor_le_powCeil_internal scale n

/-- Changing floor to ceiling costs at most a factor of two for binary
exponentials. -/
theorem powCeil_le_two_mul_powFloor
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.powCeil n ≤ 2 * scale.powFloor n :=
  powCeil_le_two_mul_powFloor_internal scale n

/-- The rounded `N^(1+scale)` bound factors into its linear and fractional
binary powers. -/
@[simp] theorem onePlusCeilPow_eq_mul
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.onePlusCeilPow n = 2 ^ n * scale.powCeil n :=
  onePlusCeilPow_eq_mul_internal scale n

/-- The rounded `N^(1+scale)` bound is at least the raw input length `N`. -/
theorem two_pow_le_onePlusCeilPow
    (scale : PositiveRationalScale) (n : ℕ) :
    2 ^ n ≤ scale.onePlusCeilPow n :=
  two_pow_le_onePlusCeilPow_internal scale n

/-- On an exact `2^n`-bit input, recovering arity from length gives the intended
rounded `N^(1+scale)` bound exactly. -/
@[simp] theorem onePlusCeilPowAtLength_pow
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.onePlusCeilPowAtLength (2 ^ n) = scale.onePlusCeilPow n :=
  onePlusCeilPowAtLength_pow_internal scale n

end PositiveRationalScale

end Complexity
