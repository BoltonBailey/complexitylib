/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Rounds.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Rounds.Internal

/-!
# Anti-Checker Lemma round parameters

At every sufficiently large arity, an accurate semantic extension estimator
and target hardness generate a shrink trace of any prescribed finite length.
This is the combinatorial round-composition contract; constructing a small
circuit that realizes the estimator is a separate conditional step.
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- For every sufficiently large arity, any accurate round estimator produces
a `1/(4n)` shrink trace of any requested length for every hard target. -/
theorem eventually_exists_shrinkTrace_of_isHardAt
    (beta : PositiveRationalScale) :
    ∀ᶠ arity : ℕ in Filter.atTop,
      ∀ (target : BitString arity → Bool)
          (estimator :
            List (BitString arity) → BitString arity → ℕ),
        IsHardAt beta target →
          IsAccurateRoundEstimator beta target estimator →
            ∀ rounds,
              ∃ inputs : List (BitString arity),
                inputs.length = rounds ∧
                  AntiChecker.IsShrinkTrace
                    (roundShrinkDenominator arity) target
                    (smallThreshold beta arity) inputs :=
  eventually_exists_shrinkTrace_of_isHardAt_internal beta

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
