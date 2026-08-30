/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Efficient.Defs
import Complexitylib.Classes.P.Cobham.Internal
import Complexitylib.Classes.P.Preimage
public import Complexitylib.Languages.FirstCell

/-!
# Encoded unconditional-estimator implementations -- proof internals
-/


public section

namespace Complexity

namespace GapMINCKT

namespace DifferenceEstimator

namespace Unconditional

private theorem lengthLeFlag_eq_not_nonempty (first second : List Bool) :
    lengthLeFlag first second =
      notBit (nonemptyFlag (first.drop second.length)) := by
  by_cases hlength : first.length ≤ second.length
  · rw [lengthLeFlag]
    simp [hlength, List.drop_eq_nil_iff.mpr hlength, notBit]
  · have hdrop : first.drop second.length ≠ [] := by
      simpa [List.drop_eq_nil_iff] using hlength
    cases hrest : first.drop second.length with
    | nil => exact (hdrop hrest).elim
    | cons bit rest =>
        simp [lengthLeFlag, hlength, notBit, nonemptyFlag]

theorem lengthLeFlag_mem_FP_internal
    {first second : List Bool → List Bool}
    (hfirst : first ∈ FP) (hsecond : second ∈ FP) :
    (fun bits => lengthLeFlag (first bits) (second bits)) ∈ FP := by
  have hfirstCobham : first ∈ CobhamFP := FP_subset_CobhamFP hfirst
  have hsecondCobham : second ∈ CobhamFP := FP_subset_CobhamFP hsecond
  change Cobham (fun input : Fin 1 → List Bool => first (input 0)) at hfirstCobham
  change Cobham (fun input : Fin 1 → List Bool => second (input 0)) at hsecondCobham
  have hdrop : Cobham (fun input : Fin 1 → List Bool =>
      (first (input 0)).drop (second (input 0)).length) :=
    Cobham.dropFn hsecondCobham hfirstCobham
  have hflag := Cobham.notFn (Cobham.nonemptyFn hdrop)
  apply CobhamFP_subset_FP
  change Cobham (fun input : Fin 1 → List Bool =>
    lengthLeFlag (first (input 0)) (second (input 0)))
  exact hflag.of_eq fun input =>
    (lengthLeFlag_eq_not_nonempty (first (input 0)) (second (input 0))).symm

namespace EncodedPlan

theorem decisionString_mem_FP_internal
    {plan : Plan} (encodedPlan : EncodedPlan plan)
    {estimate : GapMINKT.Logarithmic.Estimator}
    (encodedEstimator : EncodedEstimator estimate) :
    encodedPlan.decisionString encodedEstimator ∈ FP := by
  have hjoint :
      (fun bits => encodedEstimator.run (encodedPlan.pairQuery bits)) ∈ FP := by
    simpa [Function.comp_def] using
      mem_FP_comp encodedPlan.pairQuery_mem_FP encodedEstimator.run_mem_FP
  have hcondition :
      (fun bits => encodedEstimator.run (encodedPlan.conditionQuery bits)) ∈
        FP := by
    simpa [Function.comp_def] using
      mem_FP_comp encodedPlan.conditionQuery_mem_FP encodedEstimator.run_mem_FP
  have hbudget : (fun bits =>
      encodedEstimator.run (encodedPlan.conditionQuery bits) ++
        encodedPlan.correctionRuler bits ++
          encodedPlan.thresholdRuler bits) ∈ FP :=
    Cobham.appendFn_mem_FP
      (Cobham.appendFn_mem_FP hcondition encodedPlan.correctionRuler_mem_FP)
      encodedPlan.thresholdRuler_mem_FP
  have hcomparison := lengthLeFlag_mem_FP_internal hjoint hbudget
  change (fun bits =>
    (lengthLeFlag (encodedEstimator.run (encodedPlan.pairQuery bits))
      (encodedEstimator.run (encodedPlan.conditionQuery bits) ++
        encodedPlan.correctionRuler bits ++
          encodedPlan.thresholdRuler bits)).take
            (encodedPlan.validRuler bits).length) ∈ FP
  exact Cobham.takeLenFn_mem_FP encodedPlan.validRuler_mem_FP hcomparison

theorem decisionString_mem_firstBitOne_iff_internal
    {plan : Plan} (encodedPlan : EncodedPlan plan)
    {estimate : GapMINKT.Logarithmic.Estimator}
    (encodedEstimator : EncodedEstimator estimate) (bits : List Bool) :
    encodedPlan.decisionString encodedEstimator bits ∈
        Language.firstBitOne ↔
      bits ∈ GapMINCKT.estimatorLanguage
        (plan.components estimate).estimate := by
  cases hdecode : GapMINCKT.Instance.decode? bits with
  | none =>
      have hvalid := encodedPlan.length_validRuler bits
      rw [hdecode] at hvalid
      simp [EncodedPlan.decisionString, GapMINCKT.estimatorLanguage,
        Language.firstBitOne, hdecode, hvalid]
  | some inst =>
      have hvalid := encodedPlan.length_validRuler bits
      rw [hdecode] at hvalid
      have hpair := encodedPlan.pairQuery_eq bits inst hdecode
      have hcondition := encodedPlan.conditionQuery_eq bits inst hdecode
      have hcorrection := encodedPlan.length_correctionRuler bits inst hdecode
      have hthreshold := encodedPlan.length_thresholdRuler bits inst hdecode
      have harithmetic :
          estimate (plan.pairInput inst.base) ≤
              estimate (plan.conditionInput inst.base) +
                plan.correction inst.base + inst.threshold ↔
            (plan.components estimate).estimate inst.base ≤ inst.threshold := by
        simp only [DifferenceEstimator.estimate, Plan.components]
        omega
      simp [EncodedPlan.decisionString, GapMINCKT.estimatorLanguage,
        Language.firstBitOne, hdecode, hvalid, hpair, hcondition,
        encodedEstimator.length_run_encode, hcorrection, hthreshold,
        lengthLeFlag]
      simpa [Nat.add_assoc] using harithmetic

theorem estimatorLanguage_mem_P_internal
    {plan : Plan} (encodedPlan : EncodedPlan plan)
    {estimate : GapMINKT.Logarithmic.Estimator}
    (encodedEstimator : EncodedEstimator estimate) :
    GapMINCKT.estimatorLanguage (plan.components estimate).estimate ∈ P := by
  have hpreimage := mem_P_preimage
    (decisionString_mem_FP_internal encodedPlan encodedEstimator)
      firstBitOne_mem_P
  have heq :
      encodedPlan.decisionString encodedEstimator ⁻¹' Language.firstBitOne =
        GapMINCKT.estimatorLanguage (plan.components estimate).estimate := by
    ext bits
    exact decisionString_mem_firstBitOne_iff_internal encodedPlan
      encodedEstimator bits
  rw [← heq]
  exact hpreimage

end EncodedPlan

end Unconditional

end DifferenceEstimator

end GapMINCKT

end Complexity
