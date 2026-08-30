/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Defs
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Internal
import Complexitylib.Metacomplexity.Kolmogorov.Chain.Internal

/-!
# Building the conditional difference estimator from one ordinary estimator
-- proof internals
-/


public section

namespace Complexity

namespace GapMINCKT

namespace DifferenceEstimator

namespace Unconditional

theorem SupportsPairUpper.pair_upper_internal
    {ordinaryTapes conditionalTapes : ℕ}
    {plan : Plan} {composition : PairCompositionPlan}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    (hsupports : SupportsPairUpper plan composition ordinaryMachine
      conditionalMachine)
    (inst : MINCKT.Instance) :
    ordinaryMachine.timeBoundedKolmogorovComplexity
          (pair inst.output inst.condition) (plan.pairInputTime inst) ≤
      inst.complexity conditionalMachine +
          ordinaryMachine.timeBoundedKolmogorovComplexity
            inst.condition inst.time +
        (plan.pairUpperLoss inst : WithTop ℕ) :=
  timeBoundedKolmogorovComplexity_pair_le_add_of_conditional_composition_internal
    (hsupports.composes inst) (hsupports.length_le inst)
      (hsupports.condition_finite inst) (hsupports.result_finite inst)
      (hsupports.condition_le_bound inst) (hsupports.result_le_bound inst)

theorem Compatible.satisfiesSoIInputs_internal
    {ordinaryTapes conditionalTapes : ℕ}
    {plan : Plan} {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {ordinaryParameters : GapMINKT.Logarithmic.Parameters}
    {conditionalParameters : GapMINCKT.Parameters}
    {soiClock soiLoss : ℕ → ℕ}
    (hcompatible : Compatible plan ordinaryMachine conditionalMachine
      ordinaryParameters conditionalParameters soiClock soiLoss)
    {estimate : GapMINKT.Logarithmic.Estimator}
    (hestimate : estimate.SatisfiesBounds ordinaryMachine ordinaryParameters) :
    (plan.components estimate).SatisfiesSoIInputs
      (plan.accountingSchedule ordinaryParameters) ordinaryMachine
        conditionalMachine conditionalParameters soiClock soiLoss := by
  constructor
  · exact hcompatible.soiClock_le_conditionalTime
  · exact hcompatible.soiSize
  · intro inst
    simpa [Plan.components, Plan.pairInput, Plan.accountingSchedule] using
      (hestimate (plan.pairInput inst)).1
  · intro inst
    simpa [Plan.accountingSchedule] using hcompatible.pair_upper inst
  · intro inst
    have hlower := (hestimate (plan.conditionInput inst)).2
    rw [hcompatible.conditionTransformedTime_eq inst] at hlower
    simpa [Plan.components, Plan.conditionInput, Plan.accountingSchedule] using
      hlower
  · intro inst
    have hupper := (hestimate (plan.conditionInput inst)).1
    change (estimate (plan.conditionInput inst) : WithTop ℕ) ≤
      ordinaryMachine.timeBoundedKolmogorovComplexity inst.condition
        (plan.conditionInputTime inst) at hupper
    rw [hcompatible.conditionInputTime_eq inst] at hupper
    simpa [Plan.components, Plan.conditionInput] using hupper
  · intro inst
    have hlower := (hestimate (plan.pairInput inst)).2
    rw [hcompatible.pairTransformedTime_eq inst] at hlower
    simpa [Plan.components, Plan.pairInput, Plan.accountingSchedule] using
      hlower
  · exact hcompatible.upperLoss_budget
  · exact hcompatible.lowerLoss_budget

end Unconditional

end DifferenceEstimator

end GapMINCKT

end Complexity
