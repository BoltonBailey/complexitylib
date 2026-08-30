/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Positive rational exponent scales -- definitions

Quantitative metacomplexity theorems use expressions such as `2^(beta*n)` and
`N^(1+epsilon)`, although circuit sizes and clocks are natural numbers. This
module represents a positive rational scale by an explicit numerator and
denominator, with separate floor and ceiling multiplication. It thereby keeps
rounding choices visible and avoids real-valued resource bounds.
-/


@[expose] public section

namespace Complexity

/-- An explicit positive rational scale `numerator / denominator`.

No coprimality condition is imposed: unreduced presentations are useful when a
proof needs to retain the constants appearing in a source theorem. -/
structure PositiveRationalScale where
  /-- Positive numerator of the scale. -/
  numerator : ℕ
  /-- Positive denominator of the scale. -/
  denominator : ℕ
  /-- The numerator is nonzero. -/
  numerator_pos : 0 < numerator
  /-- The denominator is nonzero. -/
  denominator_pos : 0 < denominator

namespace PositiveRationalScale

/-- The rational value represented by a positive scale.

Different unreduced numerator/denominator pairs may have the same value. The
induced order is therefore intentionally a preorder rather than a partial
order. -/
def value (scale : PositiveRationalScale) : ℚ :=
  (scale.numerator : ℚ) / scale.denominator

/-- Compare positive scales by their represented rational values. -/
instance : Preorder PositiveRationalScale :=
  Preorder.lift (value : PositiveRationalScale → ℚ)

/-- The filter of positive rational scales approaching zero from above.

Because zero itself is excluded structurally, `atBot` for the value preorder
is exactly the small-positive-parameter convention used in magnification
statements. -/
def atZeroFromPositive : Filter PositiveRationalScale :=
  Filter.atBot

/-- Floor of `scale * n`, computed entirely in natural numbers. -/
def floorMul (scale : PositiveRationalScale) (n : ℕ) : ℕ :=
  scale.numerator * n / scale.denominator

/-- Ceiling of `scale * n`, computed entirely in natural numbers. -/
def ceilMul (scale : PositiveRationalScale) (n : ℕ) : ℕ :=
  scale.numerator * n ⌈/⌉ scale.denominator

/-- The rounded-down binary exponential `2^floor(scale*n)`. -/
def powFloor (scale : PositiveRationalScale) (n : ℕ) : ℕ :=
  2 ^ scale.floorMul n

/-- The rounded-up binary exponential `2^ceil(scale*n)`. -/
def powCeil (scale : PositiveRationalScale) (n : ℕ) : ℕ :=
  2 ^ scale.ceilMul n

/-- Natural exponent representing `(2^n)^(1+scale)` with the fractional term
rounded upward. -/
def onePlusCeilExponent (scale : PositiveRationalScale) (n : ℕ) : ℕ :=
  n + scale.ceilMul n

/-- Slightly-superlinear bound at raw truth-table arity `n`. -/
def onePlusCeilPow (scale : PositiveRationalScale) (n : ℕ) : ℕ :=
  2 ^ scale.onePlusCeilExponent n

/-- Slightly-superlinear bound as a function of raw input length.

The intended domain is power-of-two lengths. Other lengths receive a total
value through base-two logarithm but will lie outside the raw MCSP promise. -/
def onePlusCeilPowAtLength
    (scale : PositiveRationalScale) (inputLength : ℕ) : ℕ :=
  scale.onePlusCeilPow (Nat.log 2 inputLength)

end PositiveRationalScale

end Complexity
