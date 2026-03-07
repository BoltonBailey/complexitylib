import Mathlib.Analysis.Asymptotics.Defs

/-!
# Big-O for natural number functions

This module defines `Complexity.BigO`, a thin adapter that lifts Mathlib's
`Asymptotics.IsBigO` to `ℕ → ℕ` functions (casting through `ℝ`).

The scoped notation `f =O g` is available when `Complexity` is opened and
reads like standard complexity-theoretic big-O: `f(n) = O(g(n))`.
-/

open Asymptotics Filter

namespace Complexity

/-- `f` grows at most as fast as `g` asymptotically: `f(n) = O(g(n))` as `n → ∞`.
    Lifts Mathlib's `Asymptotics.IsBigO` to `ℕ → ℕ` functions, avoiding
    repeated `Nat.cast` coercions in complexity class definitions.

    Unfolding: `f =O g ↔ ∃ C, ∀ᶠ n in atTop, ↑(f n) ≤ C * ↑(g n)`. -/
def BigO (f g : ℕ → ℕ) : Prop :=
  (fun n => (f n : ℝ)) =O[atTop] (fun n => (g n : ℝ))

scoped infixl:50 " =O " => BigO

end Complexity
