/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Raw.Defs
public import Complexitylib.Metacomplexity.ScaledExponent.Defs

/-!
# GapMCSP hardness-magnification parameters -- definitions

This module instantiates the finite parameters from Oliveira--Pich--Santhanam's
GapMCSP magnification theorem. For a positive rational `beta` and positive
constant `c`, the yes threshold is

`2^floor(beta*n) / (c*n)`

and the no threshold is `2^floor(beta*n)`. A separate positive rational
`epsilon` gives the rounded natural size bound corresponding to
`N^(1+epsilon)` on raw input length `N = 2^n`.
-/


@[expose] public section

namespace Complexity

namespace GapMCSP

namespace Magnification

/-- Finite GapMCSP thresholds corresponding to the published magnification
frontier. -/
structure Parameters where
  /-- Positive rational exponent `beta`. -/
  beta : PositiveRationalScale
  /-- Universal denominator constant `c`. -/
  constant : ℕ
  /-- The constant is at least one. -/
  constant_pos : 0 < constant

namespace Parameters

/-- Small-circuit cutoff `2^floor(beta*n)/(c*n)`. -/
def yesThreshold (parameters : Parameters) (arity : ℕ) : ℕ :=
  parameters.beta.powFloor arity / (parameters.constant * arity)

/-- Large-circuit cutoff `2^floor(beta*n)`. -/
def noThreshold (parameters : Parameters) (arity : ℕ) : ℕ :=
  parameters.beta.powFloor arity

/-- The arity-indexed raw GapMCSP slice at the selected finite parameters. -/
def sliceParameters (parameters : Parameters) : SliceParameters where
  yesThreshold := parameters.yesThreshold
  noThreshold := parameters.noThreshold

end Parameters

/-- Rounded natural circuit bound corresponding to `N^(1+epsilon)`. -/
def circuitBound (epsilon : PositiveRationalScale) : ℕ → ℕ :=
  epsilon.onePlusCeilPowAtLength

/-- The same circuit bound written at raw truth-table arity `n`. -/
def circuitBoundAtArity (epsilon : PositiveRationalScale) (arity : ℕ) : ℕ :=
  epsilon.onePlusCeilPow arity

end Magnification

end GapMCSP

end Complexity
