/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINKT.Gap.Logarithmic
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Defs
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Internal

/-!
# Building the conditional difference estimator from one ordinary estimator

One unconditional Fact 3.4 estimator is queried on a paired string and on its
condition. Under the explicit clock/loss compatibility contract, those two
queries instantiate every surrounding input of the SoI accounting theorem.
Consequently their adjusted difference satisfies the conditional estimator
sandwich and solves `GapMINCKT`.

The remaining construction obligations are concentrated in `Compatible`: a
concrete upper-chain evaluator, the paper's iterated clock identities and
dominations, and the finite logarithmic budget calculations.
-/


public section

namespace Complexity

namespace GapMINCKT

namespace DifferenceEstimator

namespace Unconditional

namespace Plan

/-- The paired ordinary query contains the canonical pair. -/
@[simp] theorem pairInput_output (plan : Plan) (inst : MINCKT.Instance) :
    (plan.pairInput inst).output = pair inst.output inst.condition := rfl

/-- The paired ordinary query uses the planned source clock. -/
@[simp] theorem pairInput_time (plan : Plan) (inst : MINCKT.Instance) :
    (plan.pairInput inst).time = plan.pairInputTime inst := rfl

/-- The condition query contains exactly the condition string. -/
@[simp] theorem conditionInput_output (plan : Plan) (inst : MINCKT.Instance) :
    (plan.conditionInput inst).output = inst.condition := rfl

/-- The condition query uses the planned source clock. -/
@[simp] theorem conditionInput_time (plan : Plan) (inst : MINCKT.Instance) :
    (plan.conditionInput inst).time = plan.conditionInputTime inst := rfl

/-- The induced minuend is one application of the ordinary estimator to the
paired query. -/
@[simp] theorem components_minuend (plan : Plan)
    (ordinaryEstimate : GapMINKT.Logarithmic.Estimator)
    (inst : MINCKT.Instance) :
    (plan.components ordinaryEstimate).minuend inst =
      ordinaryEstimate (plan.pairInput inst) := rfl

/-- The induced subtrahend is one application of the same estimator to the
condition query. -/
@[simp] theorem components_subtrahend (plan : Plan)
    (ordinaryEstimate : GapMINKT.Logarithmic.Estimator)
    (inst : MINCKT.Instance) :
    (plan.components ordinaryEstimate).subtrahend inst =
      ordinaryEstimate (plan.conditionInput inst) := rfl

/-- The induced difference retains the plan's explicit correction. -/
@[simp] theorem components_correction (plan : Plan)
    (ordinaryEstimate : GapMINKT.Logarithmic.Estimator)
    (inst : MINCKT.Instance) :
    (plan.components ordinaryEstimate).correction inst =
      plan.correction inst := rfl

end Plan

/-- An operational condition-first compiler with attained minima proves the
paired upper-chain field required by `Compatible`. -/
theorem SupportsPairUpper.pair_upper
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
  hsupports.pair_upper_internal inst

/-- A valid unconditional estimator plus clock/loss compatibility instantiates
all inputs surrounding the single SoI invocation. -/
theorem Compatible.satisfiesSoIInputs
    {ordinaryTapes conditionalTapes : ℕ}
    {plan : Plan} {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {ordinaryParameters : GapMINKT.Logarithmic.Parameters}
    {conditionalParameters : GapMINCKT.Parameters}
    {soiClock soiLoss : ℕ → ℕ}
    (hcompatible : Compatible plan ordinaryMachine conditionalMachine
      ordinaryParameters conditionalParameters soiClock soiLoss)
    {ordinaryEstimate : GapMINKT.Logarithmic.Estimator}
    (hestimate : ordinaryEstimate.SatisfiesBounds ordinaryMachine
      ordinaryParameters) :
    (plan.components ordinaryEstimate).SatisfiesSoIInputs
      (plan.accountingSchedule ordinaryParameters) ordinaryMachine
        conditionalMachine conditionalParameters soiClock soiLoss :=
  hcompatible.satisfiesSoIInputs_internal hestimate

/-- Fully composed ordinary-estimator-plus-SoI construction of the conditional
estimator sandwich. -/
theorem Compatible.satisfiesBounds
    {ordinaryTapes conditionalTapes : ℕ}
    {plan : Plan} {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {ordinaryParameters : GapMINKT.Logarithmic.Parameters}
    {conditionalParameters : GapMINCKT.Parameters}
    {soiClock soiLoss : ℕ → ℕ}
    (hcompatible : Compatible plan ordinaryMachine conditionalMachine
      ordinaryParameters conditionalParameters soiClock soiLoss)
    {ordinaryEstimate : GapMINKT.Logarithmic.Estimator}
    (hestimate : ordinaryEstimate.SatisfiesBounds ordinaryMachine
      ordinaryParameters)
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine soiClock soiLoss)
    (hwidening : conditionalParameters.IsWidening) :
    (plan.components ordinaryEstimate).estimate.SatisfiesBounds ordinaryMachine
      conditionalMachine conditionalParameters :=
  (hcompatible.satisfiesSoIInputs hestimate).satisfiesBounds hsoi hwidening

/-- Thresholding the adjusted difference of two ordinary estimator queries
solves the exact conditional gap promise. -/
theorem Compatible.solvedBy
    {ordinaryTapes conditionalTapes : ℕ}
    {plan : Plan} {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {ordinaryParameters : GapMINKT.Logarithmic.Parameters}
    {conditionalParameters : GapMINCKT.Parameters}
    {soiClock soiLoss : ℕ → ℕ}
    (hcompatible : Compatible plan ordinaryMachine conditionalMachine
      ordinaryParameters conditionalParameters soiClock soiLoss)
    {ordinaryEstimate : GapMINKT.Logarithmic.Estimator}
    (hestimate : ordinaryEstimate.SatisfiesBounds ordinaryMachine
      ordinaryParameters)
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine soiClock soiLoss)
    (hwidening : conditionalParameters.IsWidening) :
    (Complexity.GapMINCKT ordinaryMachine conditionalMachine
      conditionalParameters hwidening).SolvedBy
        (GapMINCKT.decisionOfEstimator
          (plan.components ordinaryEstimate).estimate) :=
  GapMINCKT_solvedBy_decisionOfEstimator hwidening
    (hcompatible.satisfiesBounds hestimate hsoi hwidening)

/-- If the induced threshold language is in `P`, the ordinary-estimator-plus-
SoI construction places the exact conditional gap promise in `PromiseP`. -/
theorem Compatible.mem_PromiseP
    {ordinaryTapes conditionalTapes : ℕ}
    {plan : Plan} {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {ordinaryParameters : GapMINKT.Logarithmic.Parameters}
    {conditionalParameters : GapMINCKT.Parameters}
    {soiClock soiLoss : ℕ → ℕ}
    (hcompatible : Compatible plan ordinaryMachine conditionalMachine
      ordinaryParameters conditionalParameters soiClock soiLoss)
    {ordinaryEstimate : GapMINKT.Logarithmic.Estimator}
    (hestimate : ordinaryEstimate.SatisfiesBounds ordinaryMachine
      ordinaryParameters)
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine soiClock soiLoss)
    (hwidening : conditionalParameters.IsWidening)
    (hpolynomial : GapMINCKT.estimatorLanguage
      (plan.components ordinaryEstimate).estimate ∈ P) :
    Complexity.GapMINCKT ordinaryMachine conditionalMachine
        conditionalParameters hwidening ∈ PromiseP :=
  GapMINCKT_mem_PromiseP_of_estimatorLanguage_mem_P hwidening
    (hcompatible.satisfiesBounds hestimate hsoi hwidening) hpolynomial

end Unconditional

end DifferenceEstimator

end GapMINCKT

end Complexity
