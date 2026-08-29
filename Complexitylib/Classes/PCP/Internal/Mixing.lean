/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.RegularGraph

/-!
# The expander mixing lemma for `t`-step walks

The quantitative heart of every expander argument, in the square-norm form set
up in `RegularGraph`: on a graph with `SpectralBound lam`, the correlation
between a function `f` at the start of a `t`-step walk and a function `g` at its
end is what independence would predict, up to `lam ^ t` times the two standard
deviations.

Stated with everything squared, so no `Real.sqrt` appears:

`(⟪f, Aᵗ g⟫ - (∑ f)(∑ g)/n) ^ 2 ≤ lam ^ (2t) · Var f · Var g`

where `Var f = ∑ f² - (∑ f)²/n` is the (unnormalised) variance. Specialised to
indicator functions of vertex sets this is the usual expander mixing lemma, and
it is the estimate Dinur's powering step applies to the sets of vertices whose
walk-labels disagree with a global assignment.

## Main definitions

- `RegGraph.mean`, `RegGraph.center` — the mean of a function and its
  mean-zero part

## Main results

- `RegGraph.step_const`, `RegGraph.step_add`, `RegGraph.stepIter_const`,
  `RegGraph.stepIter_add` — the walk operator is affine-linear and fixes
  constants
- `RegGraph.sum_center`, `RegGraph.sum_sq_center` — the Pythagoras identity
  splitting a function into its mean and its mean-zero part
- `RegGraph.inner_stepIter_eq` — the correlation splits into the independent
  part and a mean-zero correlation
- `RegGraph.mixing_sq` — the mixing lemma
-/

@[expose] public section

namespace Complexity

namespace RegGraph

variable (G : RegGraph)

/-! ### Linearity of the walk operator -/

@[simp] theorem step_const (c : ℝ) (v : G.V) : G.step (fun _ => c) v = c := by
  have hd : (G.deg : ℝ) ≠ 0 := G.deg_ne_zero
  simp only [step, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_eq_deg]
  field_simp

theorem step_add (f g : G.V → ℝ) (v : G.V) :
    G.step (fun w => f w + g w) v = G.step f v + G.step g v := by
  simp only [step]
  rw [← add_div, Finset.sum_add_distrib]

theorem stepIter_const (t : ℕ) (c : ℝ) : G.stepIter t (fun _ => c) = fun _ => c := by
  induction t with
  | zero => rfl
  | succ t ih => rw [stepIter_succ, ih]; funext v; exact G.step_const c v

theorem stepIter_add (t : ℕ) (f g : G.V → ℝ) :
    G.stepIter t (fun w => f w + g w) = fun v => G.stepIter t f v + G.stepIter t g v := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [stepIter_succ, ih]
      funext v
      rw [G.step_add, ← stepIter_succ, ← stepIter_succ]

/-! ### Centering -/

/-- The mean of a function on the vertices. -/
noncomputable def mean (f : G.V → ℝ) : ℝ := (∑ v : G.V, f v) / (G.order : ℝ)

/-- The mean-zero part of a function. -/
noncomputable def center (f : G.V → ℝ) : G.V → ℝ := fun v => f v - G.mean f

theorem eq_mean_add_center (f : G.V → ℝ) : f = fun v => G.mean f + G.center f v := by
  funext v; simp [center]

theorem sum_center (hn : 0 < G.order) (f : G.V → ℝ) : ∑ v : G.V, G.center f v = 0 := by
  have hnq : (G.order : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp only [center, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mean, card_eq_order]
  field_simp
  ring

theorem sum_sq_center (hn : 0 < G.order) (f : G.V → ℝ) :
    ∑ v : G.V, (G.center f v) ^ 2
      = (∑ v : G.V, (f v) ^ 2) - (∑ v : G.V, f v) ^ 2 / (G.order : ℝ) := by
  have hnq : (G.order : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have expand : ∀ v : G.V, (G.center f v) ^ 2
      = (f v) ^ 2 - 2 * G.mean f * f v + (G.mean f) ^ 2 := by
    intro v; simp only [center]; ring
  calc ∑ v : G.V, (G.center f v) ^ 2
      = ∑ v : G.V, ((f v) ^ 2 - 2 * G.mean f * f v + (G.mean f) ^ 2) :=
        Finset.sum_congr rfl fun v _ => expand v
    _ = (∑ v : G.V, (f v) ^ 2) - 2 * G.mean f * (∑ v : G.V, f v)
          + (G.order : ℝ) * (G.mean f) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp [mul_comm]
    _ = (∑ v : G.V, (f v) ^ 2) - (∑ v : G.V, f v) ^ 2 / (G.order : ℝ) := by
        simp only [mean]
        field_simp
        ring

theorem sum_sq_center_nonneg (f : G.V → ℝ) : 0 ≤ ∑ v : G.V, (G.center f v) ^ 2 :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-! ### The mixing lemma -/

/-- The correlation between `f` at the start of a `t`-step walk and `g` at its
end splits into the product of averages plus the correlation of the mean-zero
parts. -/
theorem inner_stepIter_eq (hn : 0 < G.order) (t : ℕ) (f g : G.V → ℝ) :
    ∑ v : G.V, f v * G.stepIter t g v
      = (∑ v : G.V, f v) * (∑ v : G.V, g v) / (G.order : ℝ)
        + ∑ v : G.V, G.center f v * G.stepIter t (G.center g) v := by
  have hnq : (G.order : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hsumS : ∑ v : G.V, G.stepIter t (G.center g) v = 0 := by
    rw [G.sum_stepIter, G.sum_center hn]
  have hsumF : ∑ v : G.V, G.center f v = 0 := G.sum_center hn f
  have hg : G.stepIter t g = fun v => G.mean g + G.stepIter t (G.center g) v := by
    conv_lhs => rw [G.eq_mean_add_center g]
    rw [G.stepIter_add, G.stepIter_const]
  have hf : ∀ v : G.V, f v = G.mean f + G.center f v := fun v => by
    simp [center]
  calc ∑ v : G.V, f v * G.stepIter t g v
      = ∑ v : G.V, (G.mean f + G.center f v)
          * (G.mean g + G.stepIter t (G.center g) v) := by
        rw [hg]
        exact Finset.sum_congr rfl fun v _ => by rw [hf v]
    _ = ∑ v : G.V, (G.mean f * G.mean g
          + (G.mean f * G.stepIter t (G.center g) v
            + (G.mean g * G.center f v
              + G.center f v * G.stepIter t (G.center g) v))) :=
        Finset.sum_congr rfl fun v _ => by ring
    _ = (G.order : ℝ) * (G.mean f * G.mean g)
          + (G.mean f * (∑ v : G.V, G.stepIter t (G.center g) v)
            + (G.mean g * (∑ v : G.V, G.center f v)
              + ∑ v : G.V, G.center f v * G.stepIter t (G.center g) v)) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, card_eq_order]
        ring
    _ = (G.order : ℝ) * (G.mean f * G.mean g)
          + ∑ v : G.V, G.center f v * G.stepIter t (G.center g) v := by
        rw [hsumS, hsumF]; ring
    _ = (∑ v : G.V, f v) * (∑ v : G.V, g v) / (G.order : ℝ)
          + ∑ v : G.V, G.center f v * G.stepIter t (G.center g) v := by
        simp only [mean]
        field_simp

/-- **The expander mixing lemma for `t`-step walks.** -/
theorem mixing_sq {lam : ℝ} (h : G.SpectralBound lam) (hn : 0 < G.order) (t : ℕ)
    (f g : G.V → ℝ) :
    (∑ v : G.V, f v * G.stepIter t g v
        - (∑ v : G.V, f v) * (∑ v : G.V, g v) / (G.order : ℝ)) ^ 2
      ≤ lam ^ (2 * t) * ((∑ v : G.V, (f v) ^ 2) - (∑ v : G.V, f v) ^ 2 / (G.order : ℝ))
          * ((∑ v : G.V, (g v) ^ 2) - (∑ v : G.V, g v) ^ 2 / (G.order : ℝ)) := by
  have hcorr : ∑ v : G.V, f v * G.stepIter t g v
      - (∑ v : G.V, f v) * (∑ v : G.V, g v) / (G.order : ℝ)
      = ∑ v : G.V, G.center f v * G.stepIter t (G.center g) v := by
    rw [G.inner_stepIter_eq hn t f g]; ring
  rw [hcorr, ← G.sum_sq_center hn f, ← G.sum_sq_center hn g]
  have hcs : (∑ v : G.V, G.center f v * G.stepIter t (G.center g) v) ^ 2
      ≤ (∑ v : G.V, (G.center f v) ^ 2)
        * ∑ v : G.V, (G.stepIter t (G.center g) v) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hspec : ∑ v : G.V, (G.stepIter t (G.center g) v) ^ 2
      ≤ lam ^ (2 * t) * ∑ v : G.V, (G.center g v) ^ 2 :=
    G.sum_sq_stepIter_le h t (G.center g) (G.sum_center hn g)
  calc (∑ v : G.V, G.center f v * G.stepIter t (G.center g) v) ^ 2
      ≤ (∑ v : G.V, (G.center f v) ^ 2)
          * ∑ v : G.V, (G.stepIter t (G.center g) v) ^ 2 := hcs
    _ ≤ (∑ v : G.V, (G.center f v) ^ 2)
          * (lam ^ (2 * t) * ∑ v : G.V, (G.center g v) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hspec (G.sum_sq_center_nonneg f)
    _ = lam ^ (2 * t) * (∑ v : G.V, (G.center f v) ^ 2)
          * ∑ v : G.V, (G.center g v) ^ 2 := by ring

end RegGraph

end Complexity
