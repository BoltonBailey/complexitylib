/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Rounds.Selection.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Defs

/-!
# Anti-Checker Lemma round parameters -- definitions

The good-string argument supplies a genuine `1/(2n)` shrinking extension.
Relative approximation at precision `8n` preserves a `1/(4n)` shrink after
estimate minimization.
-/


@[expose] public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- Relative-count precision sufficient for one approximate-selection round. -/
def roundPrecision (arity : ℕ) : ℕ :=
  8 * arity

/-- Survivor-shrink denominator certified after approximate minimization. -/
def roundShrinkDenominator (arity : ℕ) : ℕ :=
  4 * arity

/-- Number of halving blocks needed to exceed the canonical initial survivor
count by a factor of two. -/
def roundBlockCount (beta : PositiveRationalScale) (arity : ℕ) : ℕ :=
  AntiChecker.codeLengthBound arity (smallThreshold beta arity) + 2

/-- Number of shrinking rounds used before padding to the published sample
count. -/
def requiredRoundCount (beta : PositiveRationalScale) (arity : ℕ) : ℕ :=
  roundShrinkDenominator arity * roundBlockCount beta arity

/-- A semantic extension estimator satisfies the required relative-count
contract at every sample prefix for the selected small-circuit threshold. -/
def IsAccurateRoundEstimator {arity : ℕ}
    (beta : PositiveRationalScale) (target : BitString arity → Bool)
    (estimator : List (BitString arity) → BitString arity → ℕ) : Prop :=
  AntiChecker.ApproximatesEveryRound (roundPrecision arity) target
    (smallThreshold beta arity) estimator

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
