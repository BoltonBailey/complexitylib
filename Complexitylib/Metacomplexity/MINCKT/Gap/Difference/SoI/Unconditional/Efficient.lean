/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Efficient.Defs
public import Complexitylib.Metacomplexity.MINKT.Gap.Logarithmic.Efficient
public import Complexitylib.Languages.FirstCell
import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Efficient.Internal

/-!
# Executing the unconditional-estimator reduction in polynomial time

This module proves that encoded polynomial-time implementations of the two
ordinary queries, validity check, numerical rulers, and ordinary estimator
induce a polynomial-time threshold language for the adjusted conditional
estimator.
-/


public section

namespace Complexity

namespace GapMINCKT

namespace DifferenceEstimator

namespace Unconditional

/-- Length comparison produces `true` exactly for the intended inequality. -/
@[simp] theorem lengthLeFlag_eq_true_iff (first second : List Bool) :
    lengthLeFlag first second = [true] ↔ first.length ≤ second.length := by
  simp [lengthLeFlag]

/-- Comparing the lengths of two polynomial-time string functions is itself
polynomial-time. -/
theorem lengthLeFlag_mem_FP {first second : List Bool → List Bool}
    (hfirst : first ∈ FP) (hsecond : second ∈ FP) :
    (fun bits => lengthLeFlag (first bits) (second bits)) ∈ FP :=
  lengthLeFlag_mem_FP_internal hfirst hsecond

/-- Package the explicit Fact 3.4 threshold sweep as the encoded ordinary
estimator consumed by the unconditional two-query reduction. -/
def encodedEstimatorOfGapSolver (decide : List Bool → Bool)
    (hdecide : (fun bits => [decide bits]) ∈ FP) :
    EncodedEstimator
      (GapMINKT.Logarithmic.Efficient.executableEstimator decide) where
  run := GapMINKT.Logarithmic.Efficient.encodedTimeSearchEstimator decide
  run_mem_FP :=
    GapMINKT.Logarithmic.Efficient.encodedTimeSearchEstimator_mem_FP
      decide hdecide
  length_run_encode := fun _inst => rfl

namespace EncodedPlan

/-- The complete encoded two-query threshold test is polynomial-time. -/
theorem decisionString_mem_FP
    {plan : Plan} (encodedPlan : EncodedPlan plan)
    {estimate : GapMINKT.Logarithmic.Estimator}
    (encodedEstimator : EncodedEstimator estimate) :
    encodedPlan.decisionString encodedEstimator ∈ FP :=
  encodedPlan.decisionString_mem_FP_internal encodedEstimator

/-- The encoded test accepts exactly the induced conditional estimator
language, including rejection of malformed source codes. -/
theorem decisionString_mem_firstBitOne_iff
    {plan : Plan} (encodedPlan : EncodedPlan plan)
    {estimate : GapMINKT.Logarithmic.Estimator}
    (encodedEstimator : EncodedEstimator estimate) (bits : List Bool) :
    encodedPlan.decisionString encodedEstimator bits ∈
        Language.firstBitOne ↔
      bits ∈ GapMINCKT.estimatorLanguage
        (plan.components estimate).estimate :=
  encodedPlan.decisionString_mem_firstBitOne_iff_internal encodedEstimator bits

/-- Encoded implementations discharge the algorithmic `P` obligation in the
unconditional-estimator reduction. -/
theorem estimatorLanguage_mem_P
    {plan : Plan} (encodedPlan : EncodedPlan plan)
    {estimate : GapMINKT.Logarithmic.Estimator}
    (encodedEstimator : EncodedEstimator estimate) :
    GapMINCKT.estimatorLanguage (plan.components estimate).estimate ∈ P :=
  encodedPlan.estimatorLanguage_mem_P_internal encodedEstimator

end EncodedPlan

/-- A compatible SoI reduction with encoded implementations places the exact
conditional gap promise in `PromiseP`; no separate language-membership premise
is needed. -/
theorem Compatible.mem_PromiseP_of_implementations
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
    (encodedPlan : EncodedPlan plan)
    (encodedEstimator : EncodedEstimator ordinaryEstimate) :
    Complexity.GapMINCKT ordinaryMachine conditionalMachine
        conditionalParameters hwidening ∈ PromiseP :=
  hcompatible.mem_PromiseP hestimate hsoi hwidening
    (encodedPlan.estimatorLanguage_mem_P encodedEstimator)

/-- The implementation theorem also needs estimator correctness only on the
plan's two ordinary-query families. -/
theorem Compatible.mem_PromiseP_of_implementationsOnQueries
    {ordinaryTapes conditionalTapes : ℕ}
    {plan : Plan} {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {ordinaryParameters : GapMINKT.Logarithmic.Parameters}
    {conditionalParameters : GapMINCKT.Parameters}
    {soiClock soiLoss : ℕ → ℕ}
    (hcompatible : Compatible plan ordinaryMachine conditionalMachine
      ordinaryParameters conditionalParameters soiClock soiLoss)
    {ordinaryEstimate : GapMINKT.Logarithmic.Estimator}
    (hestimate : ordinaryEstimate.SatisfiesBoundsOn ordinaryMachine
      ordinaryParameters plan.IsEstimatorQuery)
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine soiClock soiLoss)
    (hwidening : conditionalParameters.IsWidening)
    (encodedPlan : EncodedPlan plan)
    (encodedEstimator : EncodedEstimator ordinaryEstimate) :
    Complexity.GapMINCKT ordinaryMachine conditionalMachine
        conditionalParameters hwidening ∈ PromiseP :=
  hcompatible.mem_PromisePOnQueries hestimate hsoi hwidening
    (encodedPlan.estimatorLanguage_mem_P encodedEstimator)

end Unconditional

end DifferenceEstimator

end GapMINCKT

end Complexity
