/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Defs

/-!
# Encoded implementations of the unconditional-estimator reduction

These contracts expose the algorithmic content hidden by the semantic
assumption that an induced estimator language belongs to `P`. Natural-valued
estimates and corrections are represented extensionally by output length. The
plan implementation builds the two canonical ordinary MINKT queries, recognizes
valid conditional-gap codes, and materializes the correction and threshold as
length rulers.
-/


@[expose] public section

namespace Complexity

namespace GapMINCKT

namespace DifferenceEstimator

namespace Unconditional

/-- A one-bit flag recording whether the first string is no longer than the
second. -/
def lengthLeFlag (first second : List Bool) : List Bool :=
  [decide (first.length ≤ second.length)]

/-- A polynomial-time implementation of an ordinary numerical estimator.
Only the output length is semantically relevant, so the implementation may use
any bit contents. -/
structure EncodedEstimator (estimate : GapMINKT.Logarithmic.Estimator) where
  /-- Run the estimator on a canonical ordinary MINKT code. -/
  run : List Bool → List Bool
  /-- The estimator implementation is polynomial-time computable. -/
  run_mem_FP : run ∈ FP
  /-- On a canonical input, output length is exactly the numerical estimate. -/
  length_run_encode : ∀ inst : MINKT.Instance,
    (run inst.encode).length = estimate inst

/-- Polynomial-time encoded data needed to execute an unconditional two-query
plan. Correctness is required only after the source conditional-gap code
successfully decodes; `validRuler` separately recognizes that domain. -/
structure EncodedPlan (plan : Plan) where
  /-- Build the paired ordinary MINKT query. -/
  pairQuery : List Bool → List Bool
  /-- Build the condition-only ordinary MINKT query. -/
  conditionQuery : List Bool → List Bool
  /-- One-cell ruler on valid source codes and the empty ruler otherwise. -/
  validRuler : List Bool → List Bool
  /-- Materialize the plan's correction as a unary-length ruler. -/
  correctionRuler : List Bool → List Bool
  /-- Materialize the source threshold as a unary-length ruler. -/
  thresholdRuler : List Bool → List Bool
  /-- The paired-query builder is polynomial-time computable. -/
  pairQuery_mem_FP : pairQuery ∈ FP
  /-- The condition-query builder is polynomial-time computable. -/
  conditionQuery_mem_FP : conditionQuery ∈ FP
  /-- The validity ruler is polynomial-time computable. -/
  validRuler_mem_FP : validRuler ∈ FP
  /-- The correction ruler is polynomial-time computable. -/
  correctionRuler_mem_FP : correctionRuler ∈ FP
  /-- The threshold ruler is polynomial-time computable. -/
  thresholdRuler_mem_FP : thresholdRuler ∈ FP
  /-- The validity ruler has length one exactly on successfully decoded codes. -/
  length_validRuler : ∀ bits,
    (validRuler bits).length =
      match GapMINCKT.Instance.decode? bits with
      | some _inst => 1
      | none => 0
  /-- A valid source code is mapped to its exact paired query. -/
  pairQuery_eq : ∀ bits inst,
    GapMINCKT.Instance.decode? bits = some inst →
      pairQuery bits = (plan.pairInput inst.base).encode
  /-- A valid source code is mapped to its exact condition query. -/
  conditionQuery_eq : ∀ bits inst,
    GapMINCKT.Instance.decode? bits = some inst →
      conditionQuery bits = (plan.conditionInput inst.base).encode
  /-- The correction ruler has the planned length on valid inputs. -/
  length_correctionRuler : ∀ bits inst,
    GapMINCKT.Instance.decode? bits = some inst →
      (correctionRuler bits).length = plan.correction inst.base
  /-- The threshold ruler recovers the source threshold length. -/
  length_thresholdRuler : ∀ bits inst,
    GapMINCKT.Instance.decode? bits = some inst →
      (thresholdRuler bits).length = inst.threshold

namespace EncodedPlan

/-- Execute the adjusted-difference threshold test entirely through string
functions. The right ruler has length `D + correction + threshold`; comparison
with the joint-estimate ruler is equivalent to
`J - D - correction ≤ threshold`. Truncation by `validRuler` rejects malformed
source codes. -/
def decisionString {plan : Plan} (encodedPlan : EncodedPlan plan)
    {estimate : GapMINKT.Logarithmic.Estimator}
    (encodedEstimator : EncodedEstimator estimate) : List Bool → List Bool :=
  fun bits =>
    let joint := encodedEstimator.run (encodedPlan.pairQuery bits)
    let condition := encodedEstimator.run (encodedPlan.conditionQuery bits)
    let budget := condition ++ encodedPlan.correctionRuler bits ++
      encodedPlan.thresholdRuler bits
    (lengthLeFlag joint budget).take (encodedPlan.validRuler bits).length

end EncodedPlan

end Unconditional

end DifferenceEstimator

end GapMINCKT

end Complexity
