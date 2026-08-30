/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Gap.Slice.Defs
import Complexitylib.Metacomplexity.MCSP.Gap.Internal
import Complexitylib.Metacomplexity.MCSP.Internal
import Complexitylib.Metacomplexity.MCSP.Threshold.Internal

/-!
# Arity-indexed Gap MCSP slices -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace SliceParameters

theorem reducesTo_refl_internal (parameters : SliceParameters) :
    parameters.ReducesTo parameters := by
  constructor <;> intro arity <;> exact le_rfl

theorem ReducesTo.trans_internal {first second third : SliceParameters}
    (hfirst : first.ReducesTo second) (hsecond : second.ReducesTo third) :
    first.ReducesTo third := by
  constructor
  · intro arity
    exact (hfirst.1 arity).trans (hsecond.1 arity)
  · intro arity
    exact (hsecond.2 arity).trans (hfirst.2 arity)

end SliceParameters

theorem mem_sliceYesLanguage_encode_iff_internal
    (parameters : SliceParameters) (inst : MCSP.Instance) :
    inst.encode ∈ sliceYesLanguage parameters ↔
      inst.threshold = parameters.yesThreshold inst.arity ∧
        inst.HasCircuitAtMost := by
  simpa [sliceYesLanguage] using
    MCSP.mem_atThreshold_encode_iff_internal parameters.yesThreshold inst

theorem mem_sliceNoLanguage_encode_iff_internal
    (parameters : SliceParameters) (inst : MCSP.Instance) :
    inst.encode ∈ sliceNoLanguage parameters ↔
      inst.threshold = parameters.yesThreshold inst.arity ∧
        parameters.noThreshold inst.arity < inst.minimumSize := by
  simp [sliceNoLanguage, MCSP.Instance.decode?_encode_internal]

theorem disjoint_sliceLanguages_internal
    (parameters : SliceParameters) (hgap : parameters.IsGap) :
    Disjoint (sliceYesLanguage parameters) (sliceNoLanguage parameters) := by
  apply Set.disjoint_left.mpr
  intro bits hyes hno
  cases hdecode : MCSP.Instance.decode? bits with
  | none => simp [sliceYesLanguage, MCSP.atThreshold, hdecode] at hyes
  | some inst =>
      have hyes' :
          inst.threshold = parameters.yesThreshold inst.arity ∧
            inst.HasCircuitAtMost := by
        simpa [sliceYesLanguage, MCSP.atThreshold, hdecode] using hyes
      have hno' :
          inst.threshold = parameters.yesThreshold inst.arity ∧
            parameters.noThreshold inst.arity < inst.minimumSize := by
        simpa [sliceNoLanguage, hdecode] using hno
      have hminimum : inst.minimumSize ≤ inst.threshold :=
        (MCSP.Instance.hasCircuitAtMost_iff_minimumSize_le_internal inst).mp
          hyes'.2
      have hthreshold := hgap inst.arity
      omega

theorem sliceProblem_mapReducesVia_rethreshold_internal
    {source target : SliceParameters} (hparameters : source.ReducesTo target)
    (hsource : source.IsGap) (htarget : target.IsGap) :
    (PromiseProblem.mk (sliceYesLanguage source) (sliceNoLanguage source)
      (disjoint_sliceLanguages_internal source hsource)).MapReducesVia
    (PromiseProblem.mk (sliceYesLanguage target) (sliceNoLanguage target)
      (disjoint_sliceLanguages_internal target htarget))
    (MCSP.rethreshold target.yesThreshold) := by
  constructor
  · intro bits hyes
    cases hdecode : MCSP.Instance.decode? bits with
    | none =>
        simp [sliceYesLanguage, MCSP.atThreshold, hdecode] at hyes
    | some inst =>
        have hyes' :
            inst.threshold = source.yesThreshold inst.arity ∧
              inst.HasCircuitAtMost := by
          simpa [sliceYesLanguage, MCSP.atThreshold, hdecode] using hyes
        have hbits :=
          (MCSP.Instance.decode?_eq_some_iff_internal bits inst).mp hdecode
        subst bits
        rw [MCSP.rethreshold_encode_internal,
          mem_sliceYesLanguage_encode_iff_internal]
        constructor
        · rfl
        · rw [MCSP.Instance.hasCircuitAtMost_iff_minimumSize_le_internal,
            MCSP.Instance.minimumSize_withThreshold_internal]
          have hminimum : inst.minimumSize ≤ inst.threshold :=
            (MCSP.Instance.hasCircuitAtMost_iff_minimumSize_le_internal inst).mp
              hyes'.2
          exact hminimum.trans_eq hyes'.1 |>.trans (hparameters.1 inst.arity)
  · intro bits hno
    cases hdecode : MCSP.Instance.decode? bits with
    | none => simp [sliceNoLanguage, hdecode] at hno
    | some inst =>
        have hno' :
            inst.threshold = source.yesThreshold inst.arity ∧
              source.noThreshold inst.arity < inst.minimumSize := by
          simpa [sliceNoLanguage, hdecode] using hno
        have hbits :=
          (MCSP.Instance.decode?_eq_some_iff_internal bits inst).mp hdecode
        subst bits
        rw [MCSP.rethreshold_encode_internal,
          mem_sliceNoLanguage_encode_iff_internal]
        constructor
        · rfl
        · rw [MCSP.Instance.minimumSize_withThreshold_internal]
          exact lt_of_le_of_lt (hparameters.2 inst.arity) hno'.2

end GapMCSP

end Complexity
