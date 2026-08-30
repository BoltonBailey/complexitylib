/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.Defs
public import Complexitylib.Metacomplexity.MINCKT.Gap.Internal

/-!
# Difference estimators for conditional gap MinKT -- proof internals
-/


public section

namespace Complexity

private theorem adjustedDifference_le_of_le_add_internal
    (minuend subtrahend correction : ℕ) (upper : WithTop ℕ)
    (hbound : (minuend : WithTop ℕ) ≤
      upper + (subtrahend + correction : ℕ)) :
    (minuend - subtrahend - correction : ℕ) ≤ upper := by
  induction upper using WithTop.recTopCoe with
  | top => exact le_top
  | coe upperValue =>
      change (minuend : WithTop ℕ) ≤
        ((upperValue + (subtrahend + correction) : ℕ) : WithTop ℕ) at hbound
      have hvalue : minuend ≤ upperValue + (subtrahend + correction) := by
        exact WithTop.coe_le_coe.mp hbound
      have hresult : minuend - subtrahend - correction ≤ upperValue := by
        omega
      exact WithTop.coe_le_coe.mpr hresult

private theorem le_adjustedDifference_add_of_add_le_internal
    (minuend subtrahend correction slack : ℕ) (lower : WithTop ℕ)
    (hbound : lower + (subtrahend + correction : ℕ) ≤
      (minuend + slack : ℕ)) :
    lower ≤ (minuend - subtrahend - correction + slack : ℕ) := by
  induction lower using WithTop.recTopCoe with
  | top =>
      exfalso
      rw [WithTop.top_add] at hbound
      exact WithTop.not_top_le_coe _ hbound
  | coe lowerValue =>
      change ((lowerValue + (subtrahend + correction) : ℕ) : WithTop ℕ) ≤
        ((minuend + slack : ℕ) : WithTop ℕ) at hbound
      have hvalue : lowerValue + (subtrahend + correction) ≤
          minuend + slack := by
        exact WithTop.coe_le_coe.mp hbound
      have hresult : lowerValue ≤
          minuend - subtrahend - correction + slack := by
        omega
      exact WithTop.coe_le_coe.mpr hresult

namespace GapMINCKT

namespace DifferenceEstimator

theorem estimate_apply_internal (components : DifferenceEstimator)
    (inst : MINCKT.Instance) :
    components.estimate inst =
      components.minuend inst - components.subtrahend inst -
        components.correction inst := rfl

theorem SatisfiesAccounting.satisfiesBounds_internal
    {ordinaryTapes conditionalTapes : ℕ}
    {components : DifferenceEstimator}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : Parameters}
    (haccounting : components.SatisfiesAccounting ordinaryMachine
      conditionalMachine parameters) :
    components.estimate.SatisfiesBounds ordinaryMachine conditionalMachine
      parameters := by
  intro inst
  constructor
  · exact adjustedDifference_le_of_le_add_internal
      (components.minuend inst) (components.subtrahend inst)
        (components.correction inst)
        (inst.complexity conditionalMachine +
          ordinaryMachine.computationalDepthBetween inst.condition inst.time
            (parameters.transformedTime inst))
        (haccounting.upper inst)
  · exact le_adjustedDifference_add_of_add_le_internal
      (components.minuend inst) (components.subtrahend inst)
        (components.correction inst) (parameters.logarithmicSlack inst)
        ((inst.withTime (parameters.transformedTime inst)).complexity
          conditionalMachine)
        (haccounting.lower inst)

end DifferenceEstimator

end GapMINCKT

end Complexity
