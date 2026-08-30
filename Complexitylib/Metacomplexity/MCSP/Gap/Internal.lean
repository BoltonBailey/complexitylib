/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Gap.Defs
import Complexitylib.Metacomplexity.MCSP.Internal

/-!
# Gap MCSP -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

theorem isYes_iff_hasCircuitAtMost_internal (inst : MCSP.Instance) :
    IsYes inst ↔ inst.HasCircuitAtMost := by
  rw [MCSP.Instance.hasCircuitAtMost_iff_minimumSize_le_internal]
  rfl

theorem IsYes.withThreshold_mono_internal (inst : MCSP.Instance)
    {first second : ℕ} (hthreshold : first ≤ second)
    (hyes : IsYes (inst.withThreshold first)) :
    IsYes (inst.withThreshold second) := by
  exact le_trans hyes hthreshold

theorem IsNo.withThreshold_anti_internal
    {parameters : Parameters} (hmonotone : parameters.ThresholdMonotone)
    (inst : MCSP.Instance) {first second : ℕ}
    (hthreshold : first ≤ second)
    (hno : IsNo parameters (inst.withThreshold second)) :
    IsNo parameters (inst.withThreshold first) := by
  exact lt_of_le_of_lt
    (hmonotone inst.arity hthreshold) hno

theorem IsNo.anti_relaxation_internal
    {first second : Parameters} (hrelax : first.RelaxesTo second)
    (inst : MCSP.Instance) (hno : IsNo second inst) : IsNo first inst := by
  exact lt_of_le_of_lt
    (hrelax inst.arity inst.threshold) hno

theorem yesLanguage_eq_MCSP_internal : yesLanguage = MCSP := by
  ext bits
  cases hdecode : MCSP.Instance.decode? bits with
  | none => simp [yesLanguage, MCSP, hdecode]
  | some inst =>
      simp [yesLanguage, MCSP, hdecode, IsYes,
        MCSP.Instance.hasCircuitAtMost_iff_minimumSize_le_internal]

theorem noLanguage_anti_relaxation_internal
    {first second : Parameters} (hrelax : first.RelaxesTo second) :
    noLanguage second ⊆ noLanguage first := by
  intro bits hno
  cases hdecode : MCSP.Instance.decode? bits with
  | none => simp [noLanguage, hdecode] at hno
  | some inst =>
      have hno' : IsNo second inst := by
        simpa [noLanguage, hdecode] using hno
      simpa [noLanguage, hdecode] using
        IsNo.anti_relaxation_internal hrelax inst hno'

theorem disjoint_yesLanguage_noLanguage_internal
    (parameters : Parameters) (hwidening : parameters.IsWidening) :
    Disjoint yesLanguage (noLanguage parameters) := by
  apply Set.disjoint_left.mpr
  intro bits hyes hno
  cases hdecode : MCSP.Instance.decode? bits with
  | none => simp [yesLanguage, hdecode] at hyes
  | some inst =>
      have hyes' : inst.minimumSize ≤ inst.threshold := by
        simpa [yesLanguage, hdecode, IsYes] using hyes
      have hno' : parameters.relaxedThreshold inst.arity inst.threshold <
          inst.minimumSize := by
        simpa [noLanguage, hdecode, IsNo] using hno
      have hwiden := hwidening inst.arity inst.threshold
      omega

end GapMCSP

end Complexity
