/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.Parameters.Defs
public import Complexitylib.Metacomplexity.ScaledExponent.Internal
import Complexitylib.Metacomplexity.MCSP.Internal

/-!
# GapMCSP hardness-magnification parameters -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace Parameters

theorem yesThreshold_zero_internal (parameters : Parameters) :
    parameters.yesThreshold 0 = 0 := by
  simp [yesThreshold]

theorem noThreshold_zero_internal (parameters : Parameters) :
    parameters.noThreshold 0 = 1 := by
  simp [noThreshold, PositiveRationalScale.powFloor,
    PositiveRationalScale.floorMul_zero_internal]

theorem yesThreshold_le_noThreshold_internal
    (parameters : Parameters) (arity : ℕ) :
    parameters.yesThreshold arity ≤ parameters.noThreshold arity := by
  exact Nat.div_le_self _ _

theorem sliceParameters_isGap_internal (parameters : Parameters) :
    parameters.sliceParameters.IsGap := by
  intro arity
  exact yesThreshold_le_noThreshold_internal parameters arity

theorem yesThreshold_mul_denominator_le_noThreshold_internal
    (parameters : Parameters) (arity : ℕ) :
    parameters.yesThreshold arity * (parameters.constant * arity) ≤
      parameters.noThreshold arity := by
  exact Nat.div_mul_le_self _ _

theorem noThreshold_pos_internal (parameters : Parameters) (arity : ℕ) :
    0 < parameters.noThreshold arity := by
  exact PositiveRationalScale.powFloor_pos_internal parameters.beta arity

theorem yesThreshold_pos_of_denominator_le_internal
    (parameters : Parameters) {arity : ℕ} (harity : 0 < arity)
    (hdenominator : parameters.constant * arity ≤
      parameters.beta.powFloor arity) :
    0 < parameters.yesThreshold arity := by
  exact Nat.div_pos hdenominator (Nat.mul_pos parameters.constant_pos harity)

theorem noThreshold_le_powCeil_internal
    (parameters : Parameters) (arity : ℕ) :
    parameters.noThreshold arity ≤ parameters.beta.powCeil arity := by
  exact PositiveRationalScale.powFloor_le_powCeil_internal
    parameters.beta arity

theorem powCeil_le_two_mul_noThreshold_internal
    (parameters : Parameters) (arity : ℕ) :
    parameters.beta.powCeil arity ≤ 2 * parameters.noThreshold arity := by
  exact PositiveRationalScale.powCeil_le_two_mul_powFloor_internal
    parameters.beta arity

end Parameters

theorem circuitBound_pow_internal
    (epsilon : PositiveRationalScale) (arity : ℕ) :
    circuitBound epsilon (2 ^ arity) = circuitBoundAtArity epsilon arity := by
  exact PositiveRationalScale.onePlusCeilPowAtLength_pow_internal
    epsilon arity

theorem circuitBound_tableBits_internal
    (epsilon : PositiveRationalScale) (inst : MCSP.Instance) :
    circuitBound epsilon inst.tableBits.length =
      circuitBoundAtArity epsilon inst.arity := by
  rw [MCSP.Instance.length_tableBits_internal, circuitBound_pow_internal]

theorem truthTableLength_le_circuitBoundAtArity_internal
    (epsilon : PositiveRationalScale) (arity : ℕ) :
    2 ^ arity ≤ circuitBoundAtArity epsilon arity := by
  exact PositiveRationalScale.two_pow_le_onePlusCeilPow_internal
    epsilon arity

end Magnification

end GapMCSP

end Complexity
