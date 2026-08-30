/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Approximation.Defs

/-!
# Approximate-count selection -- definitions

This layer describes one round of the constructive anti-checker procedure. It
chooses an input minimizing the estimated survivor count and records shrinkage
using cross-multiplied natural inequalities.
-/


@[expose] public section

namespace Complexity

namespace AntiChecker

/-- An input minimizes a natural-valued estimate over all inputs of the fixed
arity. -/
def IsEstimateMinimizer {arity : ℕ}
    (estimate : BitString arity → ℕ) (chosen : BitString arity) : Prop :=
  ∀ input, estimate chosen ≤ estimate input

/-- Estimates for every possible one-input extension satisfy the relative
survivor-count contract. -/
def ApproximatesAllExtensions {arity : ℕ}
    (precision : ℕ) (target : BitString arity → Bool)
    (threshold : ℕ) (inputs : List (BitString arity))
    (estimate : BitString arity → ℕ) : Prop :=
  ∀ input,
    ApproximatesCandidateSurvivorCount precision target threshold
      (input :: inputs) (estimate input)

/-- Adding `input` reduces the canonical survivor count by at least the
fraction `1 / denominator`, represented without division. -/
def IsShrinkExtension {arity : ℕ}
    (denominator : ℕ) (target : BitString arity → Bool)
    (threshold : ℕ) (inputs : List (BitString arity))
    (input : BitString arity) : Prop :=
  denominator * candidateSurvivorCount target threshold (input :: inputs) ≤
    (denominator - 1) * candidateSurvivorCount target threshold inputs

/-- Some one-input extension reduces the canonical survivor count by the
requested fraction. -/
def HasShrinkExtension {arity : ℕ}
    (denominator : ℕ) (target : BitString arity → Bool)
    (threshold : ℕ) (inputs : List (BitString arity)) : Prop :=
  ∃ input, IsShrinkExtension denominator target threshold inputs input

end AntiChecker

end Complexity
