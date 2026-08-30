/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Gap.Defs
public import Complexitylib.Metacomplexity.MCSP.Gap.Internal

/-!
# Gap MCSP

Gap MCSP is a genuine promise problem over the existing canonical MCSP codec.
The source threshold is part of each instance; an explicit parameter map gives
the relaxed no-threshold. The public theory exposes the monotonicity directions
needed for quantitative hardness-magnification reductions.
-/


public section

namespace Complexity

namespace GapMCSP

/-- The gap yes predicate is exactly ordinary MCSP membership for a decoded
instance. -/
theorem isYes_iff_hasCircuitAtMost (inst : MCSP.Instance) :
    IsYes inst ↔ inst.HasCircuitAtMost :=
  isYes_iff_hasCircuitAtMost_internal inst

/-- Increasing the source threshold preserves the gap yes predicate. -/
theorem IsYes.withThreshold_mono (inst : MCSP.Instance)
    {first second : ℕ} (hthreshold : first ≤ second)
    (hyes : IsYes (inst.withThreshold first)) :
    IsYes (inst.withThreshold second) :=
  IsYes.withThreshold_mono_internal inst hthreshold hyes

/-- Under a monotone relaxation map, increasing the source threshold can only
shrink the no side. -/
theorem IsNo.withThreshold_anti
    {parameters : Parameters} (hmonotone : parameters.ThresholdMonotone)
    (inst : MCSP.Instance) {first second : ℕ}
    (hthreshold : first ≤ second)
    (hno : IsNo parameters (inst.withThreshold second)) :
    IsNo parameters (inst.withThreshold first) :=
  IsNo.withThreshold_anti_internal hmonotone inst hthreshold hno

/-- Raising the relaxed threshold shrinks the no predicate. -/
theorem IsNo.anti_relaxation
    {first second : Parameters} (hrelax : first.RelaxesTo second)
    (inst : MCSP.Instance) (hno : IsNo second inst) : IsNo first inst :=
  IsNo.anti_relaxation_internal hrelax inst hno

/-- The encoded gap yes language is definitionally the existing total MCSP
language; only the no side introduces a promise. -/
theorem yesLanguage_eq_MCSP : yesLanguage = MCSP :=
  yesLanguage_eq_MCSP_internal

/-- Pointwise raising the relaxed threshold shrinks the encoded no language. -/
theorem noLanguage_anti_relaxation
    {first second : Parameters} (hrelax : first.RelaxesTo second) :
    noLanguage second ⊆ noLanguage first :=
  noLanguage_anti_relaxation_internal hrelax

/-- Widening makes the canonical yes and no languages disjoint. -/
theorem disjoint_yesLanguage_noLanguage
    (parameters : Parameters) (hwidening : parameters.IsWidening) :
    Disjoint yesLanguage (noLanguage parameters) :=
  disjoint_yesLanguage_noLanguage_internal parameters hwidening

/-- Canonical Gap MCSP promise problem under a widening threshold map. -/
def problem (parameters : Parameters)
    (hwidening : parameters.IsWidening) : PromiseProblem where
  yesInstances := yesLanguage
  noInstances := noLanguage parameters
  disjoint := disjoint_yesLanguage_noLanguage parameters hwidening

/-- If the target uses a pointwise smaller relaxed threshold, identity is a
side-preserving reduction: the yes side is unchanged and the target no side is
larger. -/
theorem problem_mapReducesVia_id
    {source target : Parameters}
    (hrelax : target.RelaxesTo source)
    (hsource : source.IsWidening) (htarget : target.IsWidening) :
    (problem source hsource).MapReducesVia
      (problem target htarget) id := by
  constructor
  · intro bits hyes
    exact hyes
  · intro bits hno
    exact noLanguage_anti_relaxation hrelax hno

end GapMCSP

end Complexity
