/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Nat.Basic

/-!
# Approximate counting contracts -- definitions

This module records division-free multiplicative approximation predicates for
natural-number counts. The weak Stockmeyer layer uses a constant factor, while
the anti-checker application uses relative error `1 / precision`.
-/


@[expose] public section

namespace Complexity

namespace ApproximateCounting

/-- Symmetric multiplicative approximation without division. -/
def IsFactorApproximation (factor actual estimate : ℕ) : Prop :=
  estimate ≤ factor * actual ∧ actual ≤ factor * estimate

instance instDecidableIsFactorApproximation (factor actual estimate : ℕ) :
    Decidable (IsFactorApproximation factor actual estimate) := by
  unfold IsFactorApproximation
  infer_instance

/-- `estimate` approximates `actual` to relative error at most
`1 / precision`, expressed without division. -/
def IsRelativeApproximation (precision actual estimate : ℕ) : Prop :=
  0 < precision ∧
    (precision - 1) * actual ≤ precision * estimate ∧
      precision * estimate ≤ (precision + 1) * actual

instance instDecidableIsRelativeApproximation
    (precision actual estimate : ℕ) :
    Decidable (IsRelativeApproximation precision actual estimate) := by
  unfold IsRelativeApproximation
  infer_instance

end ApproximateCounting

end Complexity
