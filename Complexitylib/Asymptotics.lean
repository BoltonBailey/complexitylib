import Mathlib.Analysis.Asymptotics.Defs

/-!
# Asymptotic notation for natural number functions

This module defines `Complexity.BigO` and `Complexity.LittleO`, thin adapters
that lift Mathlib's `Asymptotics.IsBigO` and `Asymptotics.IsLittleO` to
`ℕ → ℕ` functions (casting through `ℝ`).

The scoped notations `f =O g` and `f =o g` are available when `Complexity` is
opened and read like standard complexity-theoretic asymptotic notation.

## Main definitions

- `BigO` — `f =O g` means `f(n) = O(g(n))` as `n → ∞`
- `LittleO` — `f =o g` means `f(n) = o(g(n))` as `n → ∞`

## Main results

### BigO
- `BigO.refl` — reflexivity
- `BigO.trans` — transitivity
- `BigO.of_le` — pointwise `≤` implies big-O
- `BigO.add` — sum of big-O is big-O
- `BigO.const_mul_left` — constant multiple preserves big-O
- `BigO.le_add_left` / `BigO.le_add_right` — projections from a sum
- `BigO.const_mul_add` — `c * f₁ + f₂ = O(T₁ + T₂)`

### LittleO
- `LittleO.isBigO` — little-o implies big-O
- `LittleO.trans` — transitivity
- `LittleO.trans_bigO` — mixed: `o` then `O` gives `o`
- `BigO.trans_littleO` — mixed: `O` then `o` gives `o`
- `LittleO.add` — sum of little-o is little-o
- `LittleO.const_mul_left` — constant multiple preserves little-o
-/

open Asymptotics Filter

namespace Complexity

-- ════════════════════════════════════════════════════════════════════════
-- Definitions
-- ════════════════════════════════════════════════════════════════════════

/-- `f` grows at most as fast as `g` asymptotically: `f(n) = O(g(n))` as `n → ∞`.
    Lifts Mathlib's `Asymptotics.IsBigO` to `ℕ → ℕ` functions, avoiding
    repeated `Nat.cast` coercions in complexity class definitions.

    Unfolding: `f =O g ↔ ∃ C, ∀ᶠ n in atTop, ↑(f n) ≤ C * ↑(g n)`. -/
def BigO (f g : ℕ → ℕ) : Prop :=
  (fun n => (f n : ℝ)) =O[atTop] (fun n => (g n : ℝ))

scoped infixl:50 " =O " => BigO

/-- `f` grows strictly slower than `g` asymptotically: `f(n) = o(g(n))` as `n → ∞`.
    Lifts Mathlib's `Asymptotics.IsLittleO` to `ℕ → ℕ` functions.

    Unfolding: `f =o g ↔ ∀ ε > 0, ∀ᶠ n in atTop, ↑(f n) ≤ ε * ↑(g n)`. -/
def LittleO (f g : ℕ → ℕ) : Prop :=
  (fun n => (f n : ℝ)) =o[atTop] (fun n => (g n : ℝ))

scoped infixl:50 " =o " => LittleO

-- ════════════════════════════════════════════════════════════════════════
-- BigO core lemmas
-- ════════════════════════════════════════════════════════════════════════

/-- Big-O is reflexive: `f = O(f)`. -/
theorem BigO.refl (f : ℕ → ℕ) : f =O f :=
  isBigO_refl _ _

/-- Big-O is transitive: `f = O(g) → g = O(h) → f = O(h)`. -/
theorem BigO.trans {f g h : ℕ → ℕ} (h₁ : f =O g) (h₂ : g =O h) : f =O h :=
  IsBigO.trans h₁ h₂

/-- Pointwise `≤` implies big-O. -/
theorem BigO.of_le {f g : ℕ → ℕ} (h : ∀ n, f n ≤ g n) : f =O g := by
  apply IsBigO.of_bound 1
  filter_upwards with n
  simp only [one_mul, Real.norm_natCast]
  exact_mod_cast h n

/-- Sum of two big-O functions: `f₁ = O(g) → f₂ = O(g) → (f₁ + f₂) = O(g)`. -/
theorem BigO.add {f₁ f₂ g : ℕ → ℕ} (h₁ : f₁ =O g) (h₂ : f₂ =O g) :
    (fun n => f₁ n + f₂ n) =O g := by
  show (fun n => ((f₁ n + f₂ n : ℕ) : ℝ)) =O[atTop] _
  have key := IsBigO.add h₁ h₂
  convert key using 1
  ext n; push_cast; ring

/-- Constant multiple preserves big-O. -/
theorem BigO.const_mul_left (c : ℕ) {f g : ℕ → ℕ} (h : f =O g) :
    (fun n => c * f n) =O g := by
  show (fun n => ((c * f n : ℕ) : ℝ)) =O[atTop] _
  have hcf : (fun n => (c : ℝ) * (f n : ℝ)) =O[atTop] (fun n => (f n : ℝ)) :=
    IsBigO.const_mul_left (isBigO_refl _ _) (c : ℝ)
  have key := IsBigO.trans hcf h
  convert key using 1
  ext n; push_cast; ring

-- ════════════════════════════════════════════════════════════════════════
-- LittleO core lemmas
-- ════════════════════════════════════════════════════════════════════════

/-- Little-o implies big-O: if `f = o(g)` then `f = O(g)`. -/
theorem LittleO.isBigO {f g : ℕ → ℕ} (h : f =o g) : f =O g :=
  IsLittleO.isBigO h

/-- Little-o is transitive: `f = o(g) → g = o(h) → f = o(h)`. -/
theorem LittleO.trans {f g h : ℕ → ℕ} (h₁ : f =o g) (h₂ : g =o h) : f =o h :=
  IsLittleO.trans_isBigO h₁ (IsLittleO.isBigO h₂)

/-- Mixed transitivity: `f = o(g) → g = O(h) → f = o(h)`. -/
theorem LittleO.trans_bigO {f g h : ℕ → ℕ} (h₁ : f =o g) (h₂ : g =O h) : f =o h :=
  IsLittleO.trans_isBigO h₁ h₂

/-- Mixed transitivity: `f = O(g) → g = o(h) → f = o(h)`. -/
theorem BigO.trans_littleO {f g h : ℕ → ℕ} (h₁ : f =O g) (h₂ : g =o h) : f =o h :=
  IsBigO.trans_isLittleO h₁ h₂

/-- Sum of two little-o functions: `f₁ = o(g) → f₂ = o(g) → (f₁ + f₂) = o(g)`. -/
theorem LittleO.add {f₁ f₂ g : ℕ → ℕ} (h₁ : f₁ =o g) (h₂ : f₂ =o g) :
    (fun n => f₁ n + f₂ n) =o g := by
  show (fun n => ((f₁ n + f₂ n : ℕ) : ℝ)) =o[atTop] _
  have key := IsLittleO.add h₁ h₂
  convert key using 1
  ext n; push_cast; ring

/-- Constant multiple preserves little-o. -/
theorem LittleO.const_mul_left (c : ℕ) {f g : ℕ → ℕ} (h : f =o g) :
    (fun n => c * f n) =o g := by
  show (fun n => ((c * f n : ℕ) : ℝ)) =o[atTop] _
  have hcf : (fun n => (c : ℝ) * (f n : ℝ)) =O[atTop] (fun n => (f n : ℝ)) :=
    IsBigO.const_mul_left (isBigO_refl _ _) (c : ℝ)
  have key := IsBigO.trans_isLittleO hcf h
  convert key using 1
  ext n; push_cast; ring

-- ════════════════════════════════════════════════════════════════════════
-- BigO arithmetic lemmas (addition bounds)
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
      (fun n => ((T₁ n + T₂ n : ℕ) : ℝ)) := IsBigO.trans ho₁ (le_add_left T₁ T₂)
  have hcf₁ : (fun n => ((c * f₁ n : ℕ) : ℝ)) =O[atTop]
      (fun n => ((T₁ n + T₂ n : ℕ) : ℝ)) := by
    have : (fun n => (c : ℝ) * ((f₁ n : ℕ) : ℝ)) =O[atTop]
        (fun n => ((T₁ n + T₂ n : ℕ) : ℝ)) :=
      IsBigO.const_mul_left hf₁ c
    convert this using 1
    ext n; push_cast; ring
  have hf₂ : (fun n => ((f₂ n : ℕ) : ℝ)) =O[atTop]
      (fun n => ((T₁ n + T₂ n : ℕ) : ℝ)) := IsBigO.trans ho₂ (le_add_right T₁ T₂)
  have := IsBigO.add hcf₁ hf₂
  convert this using 1
  ext n; push_cast; ring

end Complexity
