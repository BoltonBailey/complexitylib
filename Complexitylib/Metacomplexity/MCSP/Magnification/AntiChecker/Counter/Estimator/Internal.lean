/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Estimator.Defs
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Relation.Internal

/-!
# Counter-family extension estimators -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

namespace ApproximateCounterFamily

theorem extensionEstimator_eq_of_length_lt_internal
    {overhead arity : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (target : BitString arity → Bool)
    (inputs : List (BitString arity)) (input : BitString arity)
    (hlength : inputs.length < requiredRoundCount beta arity) :
    family.extensionEstimator target inputs input =
      (family.counter ⟨inputs.length, hlength⟩).estimate
        (packTargetSamples target (input :: inputs).get) := by
  simp [extensionEstimator, hlength]

theorem isAccurateRequiredRoundEstimator_internal
    {overhead arity : ℕ} {beta : PositiveRationalScale}
    {family : ApproximateCounterFamily overhead beta arity}
    (hcorrect : family.IsCorrect)
    (target : BitString arity → Bool) :
    IsAccurateRequiredRoundEstimator beta target
      (family.extensionEstimator target) := by
  intro inputs hlength input
  rw [extensionEstimator_eq_of_length_lt_internal
    family target inputs input hlength]
  have happrox := hcorrect ⟨inputs.length, hlength⟩
    (packTargetSamples target (input :: inputs).get)
  simpa only [
      candidateLabeledSurvivorCount_unpack_packTargetSamples_internal,
      List.ofFn_get] using happrox

end ApproximateCounterFamily

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
