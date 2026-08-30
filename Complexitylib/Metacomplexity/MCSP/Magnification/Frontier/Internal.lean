/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.Frontier.Defs

/-!
# The selected GapMCSP magnification frontier -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace DenominatorConstant

theorem hasSmallBetaCircuitLowerBound_iff_internal
    (constant : DenominatorConstant) (epsilon : PositiveRationalScale) :
    constant.HasSmallBetaCircuitLowerBound epsilon ↔
      ∃ cutoff, ∀ beta ≤ cutoff,
        (constant.parametersAt beta).HasEventualCircuitLowerBound epsilon := by
  exact PositiveRationalScale.eventually_atZeroFromPositive_iff

theorem HasSmallBetaCircuitLowerBound.pointwise_internal
    {constant : DenominatorConstant} {epsilon : PositiveRationalScale}
    (hlower : constant.HasSmallBetaCircuitLowerBound epsilon) :
    ∀ᶠ beta in PositiveRationalScale.atZeroFromPositive,
      (constant.parametersAt beta).HasPointwiseCircuitLowerBound epsilon := by
  exact hlower.mono fun _ hlowerAtBeta => hlowerAtBeta.pointwise

theorem hasMagnificationLowerBoundHypothesis_iff_internal
    (constant : DenominatorConstant) :
    constant.HasMagnificationLowerBoundHypothesis ↔
      ∃ epsilon cutoff, ∀ beta ≤ cutoff,
        (constant.parametersAt beta).HasEventualCircuitLowerBound epsilon := by
  constructor
  · rintro ⟨epsilon, hlower⟩
    obtain ⟨cutoff, hlower⟩ :=
      (hasSmallBetaCircuitLowerBound_iff_internal constant epsilon).mp hlower
    exact ⟨epsilon, cutoff, hlower⟩
  · rintro ⟨epsilon, cutoff, hlower⟩
    exact ⟨epsilon,
      (hasSmallBetaCircuitLowerBound_iff_internal constant epsilon).mpr
        ⟨cutoff, hlower⟩⟩

theorem HasMagnificationLowerBoundHypothesis.pointwise_internal
    {constant : DenominatorConstant}
    (hlower : constant.HasMagnificationLowerBoundHypothesis) :
    ∃ epsilon,
      ∀ᶠ beta in PositiveRationalScale.atZeroFromPositive,
        (constant.parametersAt beta).HasPointwiseCircuitLowerBound epsilon := by
  obtain ⟨epsilon, hlower⟩ := hlower
  exact ⟨epsilon, hlower.pointwise_internal⟩

end DenominatorConstant

end Magnification

end GapMCSP

end Complexity
