/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Gap
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.Defs
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.Internal

/-!
# Difference estimators for conditional gap MinKT

This module packages the cancellation step in the estimator construction of
Hirahara's Proposition 6.2. A joint estimate, condition estimate, and explicit
correction produce a conditional estimator by natural subtraction. The two
pre-cancellation accounting inequalities are sufficient to prove the exact
`GapMINCKT` estimator sandwich and hence solve the promise.
-/


public section

namespace Complexity

namespace GapMINCKT

namespace DifferenceEstimator

/-- The adjusted difference expands to its three numerical components. -/
@[simp] theorem estimate_apply (components : DifferenceEstimator)
    (inst : MINCKT.Instance) :
    components.estimate inst =
      components.minuend inst - components.subtrahend inst -
        components.correction inst :=
  estimate_apply_internal components inst

/-- The two pre-cancellation accounting inequalities imply the exact
conditional-complexity estimator sandwich. -/
theorem SatisfiesAccounting.satisfiesBounds
    {ordinaryTapes conditionalTapes : ℕ}
    {components : DifferenceEstimator}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : Parameters}
    (haccounting : components.SatisfiesAccounting ordinaryMachine
      conditionalMachine parameters) :
    components.estimate.SatisfiesBounds ordinaryMachine conditionalMachine
      parameters :=
  haccounting.satisfiesBounds_internal

/-- Thresholding an accounting-certified adjusted difference solves the exact
conditional gap promise. -/
theorem SatisfiesAccounting.solvedBy
    {ordinaryTapes conditionalTapes : ℕ}
    {components : DifferenceEstimator}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : Parameters}
    (haccounting : components.SatisfiesAccounting ordinaryMachine
      conditionalMachine parameters)
    (hwidening : parameters.IsWidening) :
    (Complexity.GapMINCKT ordinaryMachine conditionalMachine parameters
      hwidening).SolvedBy (decisionOfEstimator components.estimate) :=
  GapMINCKT_solvedBy_decisionOfEstimator hwidening
    haccounting.satisfiesBounds

/-- Polynomial-time thresholding of an accounting-certified adjusted
difference supplies a `PromiseP` completion. -/
theorem SatisfiesAccounting.mem_PromiseP
    {ordinaryTapes conditionalTapes : ℕ}
    {components : DifferenceEstimator}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : Parameters}
    (haccounting : components.SatisfiesAccounting ordinaryMachine
      conditionalMachine parameters)
    (hwidening : parameters.IsWidening)
    (hpolynomial : estimatorLanguage components.estimate ∈ P) :
    Complexity.GapMINCKT ordinaryMachine conditionalMachine parameters
        hwidening ∈ PromiseP :=
  GapMINCKT_mem_PromiseP_of_estimatorLanguage_mem_P hwidening
    haccounting.satisfiesBounds hpolynomial

end DifferenceEstimator

end GapMINCKT

end Complexity
