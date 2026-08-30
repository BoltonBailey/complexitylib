/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Parameters.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Parameters.Internal

/-!
# Anti-Checker Lemma parameters

This module exposes the rounded finite parameters for the selected
Oliveira--Pich--Santhanam Anti-Checker Lemma. It does not assert the lemma or
the existence of its multi-output generator circuit.
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

@[simp] theorem gapParameters_beta (beta : PositiveRationalScale) :
    (gapParameters beta).beta = beta :=
  gapParameters_beta_internal beta

@[simp] theorem gapParameters_constant (beta : PositiveRationalScale) :
    (gapParameters beta).constant = fixedConstant :=
  gapParameters_constant_internal beta

/-- The hard-function threshold is the existing floor-rounded exponential. -/
theorem hardThreshold_eq_powFloor
    (beta : PositiveRationalScale) (arity : ℕ) :
    hardThreshold beta arity = beta.powFloor arity :=
  hardThreshold_eq_powFloor_internal beta arity

/-- The small-circuit threshold uses the published denominator `10*n`. -/
theorem smallThreshold_eq_div
    (beta : PositiveRationalScale) (arity : ℕ) :
    smallThreshold beta arity =
      beta.powFloor arity / (fixedConstant * arity) :=
  smallThreshold_eq_div_internal beta arity

/-- The small-circuit threshold never exceeds the hard-function threshold. -/
theorem smallThreshold_le_hardThreshold
    (beta : PositiveRationalScale) (arity : ℕ) :
    smallThreshold beta arity ≤ hardThreshold beta arity :=
  smallThreshold_le_hardThreshold_internal beta arity

/-- The small-circuit threshold is positive at every sufficiently large
arity. -/
theorem eventually_smallThreshold_pos (beta : PositiveRationalScale) :
    ∀ᶠ arity in Filter.atTop, 0 < smallThreshold beta arity :=
  eventually_smallThreshold_pos_internal beta

/-- The floor-rounded sample count is always positive. -/
theorem sampleCount_pos (beta : PositiveRationalScale) (arity : ℕ) :
    0 < sampleCount beta arity :=
  sampleCount_pos_internal beta arity

/-- The sample count is monotone in the truth-table arity. -/
theorem sampleCount_mono (beta : PositiveRationalScale) :
    Monotone (sampleCount beta) :=
  sampleCount_mono_internal beta

/-- Floor rounding gives no more samples than ceiling rounding. -/
theorem sampleCount_le_upper
    (beta : PositiveRationalScale) (arity : ℕ) :
    sampleCount beta arity ≤ sampleCountUpper beta arity :=
  sampleCount_le_upper_internal beta arity

/-- Ceiling rounding increases the sample count by at most a factor of two. -/
theorem sampleCountUpper_le_two_mul
    (beta : PositiveRationalScale) (arity : ℕ) :
    sampleCountUpper beta arity ≤ 2 * sampleCount beta arity :=
  sampleCountUpper_le_two_mul_internal beta arity

/-- At positive arity, the generator's packed output width is positive. -/
theorem outputBitCount_pos (beta : PositiveRationalScale) (arity : ℕ)
    [NeZero arity] :
    0 < outputBitCount beta arity :=
  outputBitCount_pos_internal beta arity

/-- The generator bound is the ceiling-rounded natural version of
`2^(n + k*beta*n)`. -/
theorem generatorSizeBound_eq_pow (overhead : ℕ)
    (beta : PositiveRationalScale) (arity : ℕ) :
    generatorSizeBound overhead beta arity =
      2 ^ (arity + beta.ceilMul (overhead * arity)) :=
  generatorSizeBound_eq_pow_internal overhead beta arity

/-- The rounded generator bound is at least its truth-table input length. -/
theorem truthTableLength_le_generatorSizeBound (overhead : ℕ)
    (beta : PositiveRationalScale) (arity : ℕ) :
    2 ^ arity ≤ generatorSizeBound overhead beta arity :=
  truthTableLength_le_generatorSizeBound_internal overhead beta arity

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
