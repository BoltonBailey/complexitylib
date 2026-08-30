/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Counting.Defs

/-!
# Relative survivor-count approximation -- definitions

Relative error `1 / precision` is represented using natural-number
cross-multiplication. This avoids choosing a rational rounding convention for
the integer output of an approximate counter.
-/


@[expose] public section

namespace Complexity

namespace AntiChecker

/-- `estimate` approximates `actual` to relative error at most
`1 / precision`, expressed without division. -/
def IsRelativeApproximation
    (precision actual estimate : ℕ) : Prop :=
  0 < precision ∧
    (precision - 1) * actual ≤ precision * estimate ∧
      precision * estimate ≤ (precision + 1) * actual

/-- A natural number relatively approximates the canonical survivor count for
one target-labelled sample prefix. -/
def ApproximatesCandidateSurvivorCount {arity : ℕ}
    (precision : ℕ) (target : BitString arity → Bool)
    (threshold : ℕ) (inputs : List (BitString arity))
    (estimate : ℕ) : Prop :=
  IsRelativeApproximation precision
    (candidateSurvivorCount target threshold inputs) estimate

end AntiChecker

end Complexity
