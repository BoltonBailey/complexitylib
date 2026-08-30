/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINKT.Gap.Logarithmic.Defs
public import Complexitylib.Metacomplexity.MINKT.Gap.Internal
import Complexitylib.Metacomplexity.Kolmogorov.Internal

/-!
# Logarithmic-gap MINKT -- proof internals
-/


public section

namespace Complexity

namespace GapMINKT

namespace Logarithmic

namespace Parameters

theorem identity_isAdmissible_internal : identity.IsAdmissible := by
  constructor
  · intro outputLength time
    exact le_rfl
  · refine ⟨1, 1, ?_⟩
    intro outputLength time
    simp [identity]
    omega

end Parameters

theorem transformedTime_ge_internal (parameters : Parameters)
    (hwidening : parameters.IsWidening) (inst : MINKT.Instance) :
    inst.time ≤ parameters.transformedTime inst :=
  hwidening inst.output.length inst.time

theorem isNo_iff_no_relaxedWitness_internal {tapes : ℕ}
    (inst : GapMINKT.Instance) (machine : TM tapes)
    (parameters : Parameters) :
    IsNo inst machine parameters ↔
      ¬∃ program, IsRelaxedWitness inst machine parameters program := by
  constructor
  · intro hno ⟨program, hlength, hproduce⟩
    have hcomplexity :=
      (TM.timeBoundedKolmogorovComplexity_le_internal hproduce).trans
        (WithTop.coe_le_coe.mpr hlength)
    exact (not_lt_of_ge hcomplexity) hno
  · intro hnone
    apply lt_of_not_ge
    intro hcomplexity
    obtain ⟨program, hlength, hproduce⟩ :=
      (TM.timeBoundedKolmogorovComplexity_le_coe_iff_internal
        machine inst.output (parameters.transformedTime inst.base)
          (inst.threshold + parameters.logarithmicSlack inst.base)).mp
        hcomplexity
    exact hnone ⟨program, hlength, hproduce⟩

theorem not_isNo_of_isYes_internal {tapes : ℕ}
    (inst : GapMINKT.Instance) (machine : TM tapes)
    (parameters : Parameters) (hwidening : parameters.IsWidening)
    (hyes : inst.IsYes machine) : ¬IsNo inst machine parameters := by
  intro hno
  have hclock := TM.timeBoundedKolmogorovComplexity_mono_internal
    machine inst.output
      (transformedTime_ge_internal parameters hwidening inst.base)
  have hslack : (inst.threshold : WithTop ℕ) ≤
      (inst.threshold + parameters.logarithmicSlack inst.base : ℕ) :=
    WithTop.coe_le_coe.mpr (Nat.le_add_right _ _)
  exact (not_lt_of_ge (hclock.trans (hyes.trans hslack))) hno

theorem yesLanguage_mem_encode_iff_internal {tapes : ℕ}
    (machine : TM tapes) (inst : GapMINKT.Instance) :
    inst.encode ∈ yesLanguage machine ↔ inst.IsYes machine := by
  exact GapMINKT.yesLanguage_mem_encode_iff_internal machine inst

theorem noLanguage_mem_encode_iff_internal {tapes : ℕ}
    (machine : TM tapes) (parameters : Parameters)
    (inst : GapMINKT.Instance) :
    inst.encode ∈ noLanguage machine parameters ↔
      IsNo inst machine parameters := by
  simp [noLanguage, GapMINKT.Instance.decode?_encode_internal]

theorem disjoint_yesLanguage_noLanguage_internal {tapes : ℕ}
    (machine : TM tapes) (parameters : Parameters)
    (hwidening : parameters.IsWidening) :
    Disjoint (yesLanguage machine) (noLanguage machine parameters) := by
  apply Set.disjoint_left.mpr
  intro bits hyes hno
  cases hdecode : GapMINKT.Instance.decode? bits with
  | none => simp [yesLanguage, GapMINKT.yesLanguage, hdecode] at hyes
  | some inst =>
      have hisYes : inst.IsYes machine := by
        simpa [yesLanguage, GapMINKT.yesLanguage, hdecode] using hyes
      have hisNo : IsNo inst machine parameters := by
        simpa [noLanguage, hdecode] using hno
      exact not_isNo_of_isYes_internal inst machine parameters hwidening
        hisYes hisNo

theorem estimator_le_threshold_of_isYes_internal {tapes : ℕ}
    {machine : TM tapes} {parameters : Parameters} {estimate : Estimator}
    (hestimate : estimate.SatisfiesBounds machine parameters)
    (inst : GapMINKT.Instance) (hyes : inst.IsYes machine) :
    estimate inst.base ≤ inst.threshold :=
  WithTop.coe_le_coe.mp ((hestimate inst.base).1.trans hyes)

theorem threshold_lt_estimator_of_isNo_internal {tapes : ℕ}
    {machine : TM tapes} {parameters : Parameters} {estimate : Estimator}
    (hestimate : estimate.SatisfiesBounds machine parameters)
    (inst : GapMINKT.Instance) (hno : IsNo inst machine parameters) :
    inst.threshold < estimate inst.base := by
  apply Nat.lt_of_not_ge
  intro hthreshold
  have hlower := (hestimate inst.base).2
  have hsum :
      estimate inst.base + parameters.logarithmicSlack inst.base ≤
        inst.threshold + parameters.logarithmicSlack inst.base :=
    Nat.add_le_add_right hthreshold _
  have hlater := hlower.trans (WithTop.coe_le_coe.mpr hsum)
  exact (not_lt_of_ge hlater) hno

theorem estimatorLanguage_mem_encode_iff_internal (estimate : Estimator)
    (inst : GapMINKT.Instance) :
    inst.encode ∈ estimatorLanguage estimate ↔
      estimate inst.base ≤ inst.threshold := by
  simp [estimatorLanguage, GapMINKT.Instance.decode?_encode_internal]

theorem decisionOfEstimator_eq_true_iff_internal (estimate : Estimator)
    (bits : List Bool) :
    decisionOfEstimator estimate bits = true ↔
      bits ∈ estimatorLanguage estimate := by
  cases hdecode : GapMINKT.Instance.decode? bits with
  | none => simp [decisionOfEstimator, estimatorLanguage, hdecode]
  | some inst => simp [decisionOfEstimator, estimatorLanguage, hdecode]

theorem yesLanguage_subset_estimatorLanguage_internal {tapes : ℕ}
    {machine : TM tapes} {parameters : Parameters} {estimate : Estimator}
    (hestimate : estimate.SatisfiesBounds machine parameters) :
    yesLanguage machine ⊆ estimatorLanguage estimate := by
  intro bits hyes
  cases hdecode : GapMINKT.Instance.decode? bits with
  | none => simp [yesLanguage, GapMINKT.yesLanguage, hdecode] at hyes
  | some inst =>
      have hisYes : inst.IsYes machine := by
        simpa [yesLanguage, GapMINKT.yesLanguage, hdecode] using hyes
      have hbound := estimator_le_threshold_of_isYes_internal
        hestimate inst hisYes
      simpa [estimatorLanguage, hdecode] using hbound

theorem disjoint_estimatorLanguage_noLanguage_internal {tapes : ℕ}
    {machine : TM tapes} {parameters : Parameters} {estimate : Estimator}
    (hestimate : estimate.SatisfiesBounds machine parameters) :
    Disjoint (estimatorLanguage estimate) (noLanguage machine parameters) := by
  apply Set.disjoint_left.mpr
  intro bits hestimateLanguage hno
  cases hdecode : GapMINKT.Instance.decode? bits with
  | none => simp [estimatorLanguage, hdecode] at hestimateLanguage
  | some inst =>
      have hle : estimate inst.base ≤ inst.threshold := by
        simpa [estimatorLanguage, hdecode] using hestimateLanguage
      have hisNo : IsNo inst machine parameters := by
        simpa [noLanguage, hdecode] using hno
      have hlt := threshold_lt_estimator_of_isNo_internal
        hestimate inst hisNo
      omega

theorem decisionOfEstimator_eq_true_of_mem_yesLanguage_internal {tapes : ℕ}
    {machine : TM tapes} {parameters : Parameters} {estimate : Estimator}
    (hestimate : estimate.SatisfiesBounds machine parameters)
    {bits : List Bool} (hyes : bits ∈ yesLanguage machine) :
    decisionOfEstimator estimate bits = true :=
  (decisionOfEstimator_eq_true_iff_internal estimate bits).mpr
    (yesLanguage_subset_estimatorLanguage_internal hestimate hyes)

theorem decisionOfEstimator_eq_false_of_mem_noLanguage_internal {tapes : ℕ}
    {machine : TM tapes} {parameters : Parameters} {estimate : Estimator}
    (hestimate : estimate.SatisfiesBounds machine parameters)
    {bits : List Bool} (hno : bits ∈ noLanguage machine parameters) :
    decisionOfEstimator estimate bits = false := by
  cases hvalue : decisionOfEstimator estimate bits with
  | false => rfl
  | true =>
      have hmem :=
        (decisionOfEstimator_eq_true_iff_internal estimate bits).mp hvalue
      exact (Set.disjoint_left.mp
        (disjoint_estimatorLanguage_noLanguage_internal hestimate)
          hmem hno).elim

end Logarithmic

end GapMINKT

end Complexity
