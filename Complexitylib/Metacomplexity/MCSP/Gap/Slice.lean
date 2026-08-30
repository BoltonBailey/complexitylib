/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Gap.Slice.Defs
public import Complexitylib.Metacomplexity.MCSP.Gap.Slice.Internal

/-!
# Arity-indexed Gap MCSP slices

This module exposes canonical `GapMCSP[s_yes, s_no]` promises. Its reduction
theorem keeps the represented truth table fixed, writes the target yes
threshold into the code, and exposes the two exact inequalities needed for
side preservation.
-/


public section

namespace Complexity

namespace GapMCSP

namespace SliceParameters

/-- Every threshold pair reduces to itself. -/
theorem reducesTo_refl (parameters : SliceParameters) :
    parameters.ReducesTo parameters :=
  reducesTo_refl_internal parameters

/-- Parameter order composes. -/
theorem ReducesTo.trans {first second third : SliceParameters}
    (hfirst : first.ReducesTo second) (hsecond : second.ReducesTo third) :
    first.ReducesTo third :=
  ReducesTo.trans_internal hfirst hsecond

end SliceParameters

/-- Membership in the encoded yes slice exposes its forced threshold and MCSP
witness predicate. -/
@[simp] theorem mem_sliceYesLanguage_encode_iff
    (parameters : SliceParameters) (inst : MCSP.Instance) :
    inst.encode ∈ sliceYesLanguage parameters ↔
      inst.threshold = parameters.yesThreshold inst.arity ∧
        inst.HasCircuitAtMost :=
  mem_sliceYesLanguage_encode_iff_internal parameters inst

/-- Membership in the encoded no slice exposes both finite thresholds. -/
@[simp] theorem mem_sliceNoLanguage_encode_iff
    (parameters : SliceParameters) (inst : MCSP.Instance) :
    inst.encode ∈ sliceNoLanguage parameters ↔
      inst.threshold = parameters.yesThreshold inst.arity ∧
        parameters.noThreshold inst.arity < inst.minimumSize :=
  mem_sliceNoLanguage_encode_iff_internal parameters inst

/-- A pointwise gap makes the two encoded slice languages disjoint. -/
theorem disjoint_sliceLanguages
    (parameters : SliceParameters) (hgap : parameters.IsGap) :
    Disjoint (sliceYesLanguage parameters) (sliceNoLanguage parameters) :=
  disjoint_sliceLanguages_internal parameters hgap

/-- Canonical arity-indexed Gap MCSP promise problem. -/
def sliceProblem (parameters : SliceParameters)
    (hgap : parameters.IsGap) : PromiseProblem where
  yesInstances := sliceYesLanguage parameters
  noInstances := sliceNoLanguage parameters
  disjoint := disjoint_sliceLanguages parameters hgap

/-- Exact table-preserving reduction between ordered threshold slices. The map
re-encodes only the target yes threshold; `MCSP.rethreshold_comp` and
`MCSP.length_rethreshold_of_decode?_eq_some` give its composition and precise
output-length behavior. -/
theorem sliceProblem_mapReducesVia_rethreshold
    {source target : SliceParameters} (hparameters : source.ReducesTo target)
    (hsource : source.IsGap) (htarget : target.IsGap) :
    (sliceProblem source hsource).MapReducesVia
      (sliceProblem target htarget)
      (MCSP.rethreshold target.yesThreshold) :=
  sliceProblem_mapReducesVia_rethreshold_internal
    hparameters hsource htarget

end GapMCSP

end Complexity
