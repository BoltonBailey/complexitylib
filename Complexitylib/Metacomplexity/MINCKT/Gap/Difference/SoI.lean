/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Defs
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Internal

/-!
# SoI accounting for conditional-complexity difference estimators

This module composes a time-bounded symmetry-of-information hypothesis with
explicit joint/condition estimator bounds and finite loss budgets. The result
is the pre-cancellation accounting contract for the adjusted-difference
estimator, hence the full `GapMINCKT` estimator sandwich, solver, and
`PromiseP` completion criterion.

Every clock equality and loss allocation remains visible in
`SatisfiesSoIInputs`; this theorem does not assume that a concrete universal
estimator or its polynomial-time implementation has already been built.
-/


public section

namespace Complexity

namespace GapMINCKT

namespace DifferenceEstimator

/-- SoI and the surrounding estimator inequalities imply both
pre-cancellation accounting bounds. -/
theorem SatisfiesSoIInputs.satisfiesAccounting
    {ordinaryTapes conditionalTapes : ℕ}
    {components : DifferenceEstimator} {schedule : SoIAccountingSchedule}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : Parameters} {soiClock soiLoss : ℕ → ℕ}
    (hinputs : components.SatisfiesSoIInputs schedule ordinaryMachine
      conditionalMachine parameters soiClock soiLoss)
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine soiClock soiLoss)
    (hwidening : parameters.IsWidening) :
    components.SatisfiesAccounting ordinaryMachine conditionalMachine
      parameters :=
  hinputs.satisfiesAccounting_internal hsoi hwidening

/-- Fully composed SoI-to-estimator theorem. -/
theorem SatisfiesSoIInputs.satisfiesBounds
    {ordinaryTapes conditionalTapes : ℕ}
    {components : DifferenceEstimator} {schedule : SoIAccountingSchedule}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : Parameters} {soiClock soiLoss : ℕ → ℕ}
    (hinputs : components.SatisfiesSoIInputs schedule ordinaryMachine
      conditionalMachine parameters soiClock soiLoss)
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine soiClock soiLoss)
    (hwidening : parameters.IsWidening) :
    components.estimate.SatisfiesBounds ordinaryMachine conditionalMachine
      parameters :=
  (hinputs.satisfiesAccounting hsoi hwidening).satisfiesBounds

/-- Thresholding the SoI-certified adjusted difference solves the exact
conditional gap promise. -/
theorem SatisfiesSoIInputs.solvedBy
    {ordinaryTapes conditionalTapes : ℕ}
    {components : DifferenceEstimator} {schedule : SoIAccountingSchedule}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : Parameters} {soiClock soiLoss : ℕ → ℕ}
    (hinputs : components.SatisfiesSoIInputs schedule ordinaryMachine
      conditionalMachine parameters soiClock soiLoss)
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine soiClock soiLoss)
    (hwidening : parameters.IsWidening) :
    (Complexity.GapMINCKT ordinaryMachine conditionalMachine parameters
      hwidening).SolvedBy (decisionOfEstimator components.estimate) :=
  GapMINCKT_solvedBy_decisionOfEstimator hwidening
    (hinputs.satisfiesBounds hsoi hwidening)

/-- A polynomial-time threshold language for the SoI-certified difference is a
`PromiseP` completion of `GapMINCKT`. -/
theorem SatisfiesSoIInputs.mem_PromiseP
    {ordinaryTapes conditionalTapes : ℕ}
    {components : DifferenceEstimator} {schedule : SoIAccountingSchedule}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : Parameters} {soiClock soiLoss : ℕ → ℕ}
    (hinputs : components.SatisfiesSoIInputs schedule ordinaryMachine
      conditionalMachine parameters soiClock soiLoss)
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine soiClock soiLoss)
    (hwidening : parameters.IsWidening)
    (hpolynomial : estimatorLanguage components.estimate ∈ P) :
    Complexity.GapMINCKT ordinaryMachine conditionalMachine parameters
        hwidening ∈ PromiseP :=
  GapMINCKT_mem_PromiseP_of_estimatorLanguage_mem_P hwidening
    (hinputs.satisfiesBounds hsoi hwidening) hpolynomial

end DifferenceEstimator

end GapMINCKT

end Complexity
