/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Rounds.Defs

/-!
# Approximate-selection round traces -- definitions

An extension estimator assigns an estimated survivor count to every possible
next input at every sample prefix. This layer records bounded and global
accuracy, together with the trace obtained by repeatedly choosing a minimum
estimate.
-/


@[expose] public section

namespace Complexity

namespace AntiChecker

/-- An extension estimator satisfies the relative survivor-count contract at
every sample prefix shorter than the prescribed number of rounds. -/
def ApproximatesRoundsUpTo {arity : ℕ} (rounds precision : ℕ)
    (target : BitString arity → Bool) (threshold : ℕ)
    (estimator : List (BitString arity) → BitString arity → ℕ) : Prop :=
  ∀ inputs, inputs.length < rounds →
    ApproximatesAllExtensions precision target threshold inputs
      (estimator inputs)

/-- An extension estimator satisfies the relative survivor-count contract at
every possible sample prefix. -/
def ApproximatesEveryRound {arity : ℕ} (precision : ℕ)
    (target : BitString arity → Bool) (threshold : ℕ)
    (estimator : List (BitString arity) → BitString arity → ℕ) : Prop :=
  ∀ inputs,
    ApproximatesAllExtensions precision target threshold inputs
      (estimator inputs)

/-- Every input in the list, read from tail to head, minimizes the estimator
relative to the prefix constructed before it. -/
def IsEstimateSelectionTrace {arity : ℕ}
    (estimator : List (BitString arity) → BitString arity → ℕ) :
    List (BitString arity) → Prop
  | [] => True
  | input :: inputs =>
      IsEstimateSelectionTrace estimator inputs ∧
        IsEstimateMinimizer (estimator inputs) input

end AntiChecker

end Complexity
