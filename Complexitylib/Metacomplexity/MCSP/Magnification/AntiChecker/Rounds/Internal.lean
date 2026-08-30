/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Rounds.Defs
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Rounds.Selection.Internal
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.GoodString

/-!
# Anti-Checker Lemma round parameters -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

theorem eventually_exists_shrinkTrace_of_isHardAt_internal
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
                    (smallThreshold beta arity) inputs := by
  filter_upwards
      [eventually_hasShrinkExtension_of_isHardAt beta,
        Filter.eventually_ge_atTop 1]
      with arity hgood harity
  intro target estimator hhard hestimate rounds
  have htrace :=
    AntiChecker.exists_isShrinkTrace_length_of_approximatesEveryRound_internal
      (precision := roundPrecision arity) (denominator := 2 * arity)
      estimator rounds (by unfold roundPrecision; omega) (by omega)
      (by unfold roundPrecision; omega) hestimate
      (fun inputs => hgood target inputs hhard)
  simpa [roundShrinkDenominator, ← Nat.mul_assoc] using htrace

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
