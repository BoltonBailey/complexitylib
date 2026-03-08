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

-- ════════════════════════════════════════════════════════════════════════
-- Reusable BigO arithmetic lemmas
-- ════════════════════════════════════════════════════════════════════════

/-- `T₁` is big-O of `T₁ + T₂`. -/
theorem BigO.le_add_left (T₁ T₂ : ℕ → ℕ) :
    T₁ =O (fun n => T₁ n + T₂ n) := by
  show (fun n => ((T₁ n : ℕ) : ℝ)) =O[atTop] (fun n => ((T₁ n + T₂ n : ℕ) : ℝ))
  apply IsBigO.of_bound 1
  filter_upwards with n
  simp only [Nat.cast_add, one_mul, Real.norm_natCast]
  exact le_of_le_of_eq (le_add_of_nonneg_right (Nat.cast_nonneg (α := ℝ) (T₂ n)))
    (abs_of_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))).symm

/-- `T₂` is big-O of `T₁ + T₂`. -/
theorem BigO.le_add_right (T₁ T₂ : ℕ → ℕ) :
    T₂ =O (fun n => T₁ n + T₂ n) := by
  show (fun n => ((T₂ n : ℕ) : ℝ)) =O[atTop] (fun n => ((T₁ n + T₂ n : ℕ) : ℝ))
  apply IsBigO.of_bound 1
  filter_upwards with n
  simp only [Nat.cast_add, one_mul, Real.norm_natCast]
  exact le_of_le_of_eq (le_add_of_nonneg_left (Nat.cast_nonneg (α := ℝ) (T₁ n)))
    (abs_of_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))).symm

/-- If `f₁ =O T₁` and `f₂ =O T₂`, then `c * f₁ + f₂ =O (T₁ + T₂)`. -/
theorem BigO.const_mul_add (c : ℕ) {f₁ f₂ T₁ T₂ : ℕ → ℕ}
    (ho₁ : f₁ =O T₁) (ho₂ : f₂ =O T₂) :
    (fun n => c * f₁ n + f₂ n) =O (fun n => T₁ n + T₂ n) := by
  show (fun n => ((c * f₁ n + f₂ n : ℕ) : ℝ)) =O[atTop]
       (fun n => ((T₁ n + T₂ n : ℕ) : ℝ))
  have hf₁ : (fun n => ((f₁ n : ℕ) : ℝ)) =O[atTop]
      (fun n => ((T₁ n + T₂ n : ℕ) : ℝ)) := ho₁.trans (le_add_left T₁ T₂)
  have hcf₁ : (fun n => ((c * f₁ n : ℕ) : ℝ)) =O[atTop]
      (fun n => ((T₁ n + T₂ n : ℕ) : ℝ)) := by
    have : (fun n => (c : ℝ) * ((f₁ n : ℕ) : ℝ)) =O[atTop]
        (fun n => ((T₁ n + T₂ n : ℕ) : ℝ)) :=
      hf₁.const_mul_left c
    convert this using 1
    ext n; push_cast; ring
  have hf₂ : (fun n => ((f₂ n : ℕ) : ℝ)) =O[atTop]
      (fun n => ((T₁ n + T₂ n : ℕ) : ℝ)) := ho₂.trans (le_add_right T₁ T₂)
  have := hcf₁.add hf₂
  convert this using 1
  ext n; push_cast; ring

end Complexity
