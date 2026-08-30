/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Parameters.Defs
import Complexitylib.Metacomplexity.MCSP.Magnification.Parameters

/-!
# Anti-Checker Lemma parameters -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

theorem gapParameters_beta_internal (beta : PositiveRationalScale) :
    (gapParameters beta).beta = beta := rfl

theorem gapParameters_constant_internal (beta : PositiveRationalScale) :
    (gapParameters beta).constant = fixedConstant := rfl

theorem hardThreshold_eq_powFloor_internal
    (beta : PositiveRationalScale) (arity : ℕ) :
    hardThreshold beta arity = beta.powFloor arity := rfl

theorem smallThreshold_eq_div_internal
    (beta : PositiveRationalScale) (arity : ℕ) :
    smallThreshold beta arity =
      beta.powFloor arity / (fixedConstant * arity) := rfl

theorem smallThreshold_le_hardThreshold_internal
    (beta : PositiveRationalScale) (arity : ℕ) :
    smallThreshold beta arity ≤ hardThreshold beta arity :=
  Parameters.yesThreshold_le_noThreshold (gapParameters beta) arity

theorem eventually_smallThreshold_pos_internal
    (beta : PositiveRationalScale) :
    ∀ᶠ arity in Filter.atTop, 0 < smallThreshold beta arity :=
  Parameters.eventually_yesThreshold_pos (gapParameters beta)

theorem sampleCount_pos_internal
    (beta : PositiveRationalScale) (arity : ℕ) :
    0 < sampleCount beta arity :=
  PositiveRationalScale.powFloor_pos beta (fixedConstant * arity)

theorem sampleCount_mono_internal (beta : PositiveRationalScale) :
    Monotone (sampleCount beta) := by
  intro first second hle
  apply PositiveRationalScale.powFloor_mono beta
  exact Nat.mul_le_mul_left fixedConstant hle

theorem sampleCount_le_upper_internal
    (beta : PositiveRationalScale) (arity : ℕ) :
    sampleCount beta arity ≤ sampleCountUpper beta arity :=
  PositiveRationalScale.powFloor_le_powCeil
    beta (fixedConstant * arity)

theorem sampleCountUpper_le_two_mul_internal
    (beta : PositiveRationalScale) (arity : ℕ) :
    sampleCountUpper beta arity ≤ 2 * sampleCount beta arity :=
  PositiveRationalScale.powCeil_le_two_mul_powFloor
    beta (fixedConstant * arity)

theorem outputBitCount_pos_internal
    (beta : PositiveRationalScale) (arity : ℕ) [NeZero arity] :
    0 < outputBitCount beta arity :=
  NeZero.pos (outputBitCount beta arity)

theorem generatorSizeBound_eq_pow_internal (overhead : ℕ)
    (beta : PositiveRationalScale) (arity : ℕ) :
    generatorSizeBound overhead beta arity =
      2 ^ (arity + beta.ceilMul (overhead * arity)) := by
  simp [generatorSizeBound, PositiveRationalScale.powCeil, pow_add]

theorem truthTableLength_le_generatorSizeBound_internal (overhead : ℕ)
    (beta : PositiveRationalScale) (arity : ℕ) :
    2 ^ arity ≤ generatorSizeBound overhead beta arity := by
  rw [generatorSizeBound]
  simpa using Nat.mul_le_mul_left (2 ^ arity)
    (PositiveRationalScale.powCeil_pos beta (overhead * arity))

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
