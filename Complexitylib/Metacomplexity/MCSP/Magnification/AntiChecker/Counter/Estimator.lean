/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Estimator.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Estimator.Internal

/-!
# Counter-family extension estimators

This module connects a correct finite counter family to the exact bounded
semantic estimator contract used by anti-checker round composition.
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

namespace ApproximateCounterFamily

/-- Inside the required prefix range, the total estimator evaluates the
counter indexed by the current prefix length. -/
theorem extensionEstimator_eq_of_length_lt
    {overhead arity : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (target : BitString arity → Bool)
    (inputs : List (BitString arity)) (input : BitString arity)
    (hlength : inputs.length < requiredRoundCount beta arity) :
    family.extensionEstimator target inputs input =
      (family.counter ⟨inputs.length, hlength⟩).estimate
        (packTargetSamples target (input :: inputs).get) :=
  extensionEstimator_eq_of_length_lt_internal
    family target inputs input hlength

/-- Correctness of every finite counter turns the induced total estimator into
the bounded accuracy contract required by round composition. -/
theorem isAccurateRequiredRoundEstimator
    {overhead arity : ℕ} {beta : PositiveRationalScale}
    {family : ApproximateCounterFamily overhead beta arity}
    (hcorrect : family.IsCorrect)
    (target : BitString arity → Bool) :
    IsAccurateRequiredRoundEstimator beta target
      (family.extensionEstimator target) :=
  isAccurateRequiredRoundEstimator_internal hcorrect target

end ApproximateCounterFamily

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
