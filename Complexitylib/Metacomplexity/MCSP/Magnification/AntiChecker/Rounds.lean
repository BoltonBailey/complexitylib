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

/-- The initial canonical survivor count is strictly below the power of two
indexed by the selected number of halving blocks. -/
theorem initialCandidateSurvivorCount_lt_two_pow_roundBlockCount
    {arity : ℕ} (beta : PositiveRationalScale)
    (target : BitString arity → Bool) :
    AntiChecker.candidateSurvivorCount target
        (smallThreshold beta arity) [] <
      2 ^ roundBlockCount beta arity :=
  initialCandidateSurvivorCount_lt_two_pow_roundBlockCount_internal
    beta target

/-- The published sample count eventually covers every shrinking round needed
by the canonical circuit-code cardinality bound. -/
theorem eventually_requiredRoundCount_le_sampleCount
    (beta : PositiveRationalScale) :
    ∀ᶠ arity : ℕ in Filter.atTop,
      requiredRoundCount beta arity ≤ sampleCount beta arity :=
  eventually_requiredRoundCount_le_sampleCount_internal beta

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

/-- For every sufficiently large arity, an accurate round estimator yields an
anti-checker of exactly the published sample count for every hard target. -/
theorem eventually_exists_isFor_length_eq_sampleCount_of_isHardAt
    (beta : PositiveRationalScale) :
    ∀ᶠ arity : ℕ in Filter.atTop,
      ∀ (harity : arity ≠ 0),
        letI : NeZero arity := ⟨harity⟩
        ∀ (target : BitString arity → Bool)
          (estimator :
            List (BitString arity) → BitString arity → ℕ),
        IsHardAt beta target →
          IsAccurateRoundEstimator beta target estimator →
            ∃ inputs : List (BitString arity),
              inputs.length = sampleCount beta arity ∧
                AntiChecker.IsFor target (smallThreshold beta arity) inputs :=
  eventually_exists_isFor_length_eq_sampleCount_of_isHardAt_internal beta

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
