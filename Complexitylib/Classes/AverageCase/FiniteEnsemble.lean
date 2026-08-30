/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.AverageCase.FiniteEnsemble.Defs
public import Complexitylib.Classes.AverageCase.FiniteEnsemble.Internal

/-!
# Finite uniform-seed distribution ensembles

This module exposes exact distributions generated from arbitrary nonempty finite
uniform seed spaces. It generalizes dyadic ensembles while preserving sampler
multiplicity, and provides probability laws, pushforwards, products, point
masses, normalization, and an exact dyadic-to-finite bridge.
-/


public section

universe u v w

namespace Complexity

/-- Uniform finite-event probabilities are nonnegative. -/
theorem uniformProbability_nonneg {Ω : Type u} [Fintype Ω]
    (event : Finset Ω) :
    0 ≤ uniformProbability event :=
  uniformProbability_nonneg_internal event

/-- Uniform finite-event probabilities are at most one in a nonempty sample
space. -/
theorem uniformProbability_le_one {Ω : Type u}
    [Fintype Ω] [Nonempty Ω] (event : Finset Ω) :
    uniformProbability event ≤ 1 :=
  uniformProbability_le_one_internal event

/-- The empty event has uniform probability zero. -/
@[simp] theorem uniformProbability_empty {Ω : Type u} [Fintype Ω] :
    uniformProbability (∅ : Finset Ω) = 0 :=
  uniformProbability_empty_internal

/-- The entire nonempty sample space has uniform probability one. -/
@[simp] theorem uniformProbability_univ {Ω : Type u}
    [Fintype Ω] [Nonempty Ω] :
    uniformProbability (Finset.univ : Finset Ω) = 1 :=
  uniformProbability_univ_internal

/-- Uniform probability of a complement is one minus the original
probability. -/
theorem uniformProbability_compl {Ω : Type u}
    [Fintype Ω] [DecidableEq Ω] [Nonempty Ω] (event : Finset Ω) :
    uniformProbability eventᶜ = 1 - uniformProbability event :=
  uniformProbability_compl_internal event

/-- Union bound for arbitrary finite uniform sample spaces. -/
theorem uniformProbability_union_le {Ω : Type u}
    [Fintype Ω] [DecidableEq Ω] (event₁ event₂ : Finset Ω) :
    uniformProbability (event₁ ∪ event₂) ≤
      uniformProbability event₁ + uniformProbability event₂ :=
  uniformProbability_union_le_internal event₁ event₂

/-- Conditioning by a finite partition of a uniform sample space. -/
theorem uniformProbability_eq_sum_fiberwise
    {Ω : Type u} {ι : Type v} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq ι] (event : Finset Ω) (indices : Finset ι) (f : Ω → ι)
    (hmaps : (event : Set Ω).MapsTo f indices) :
    uniformProbability event =
      ∑ i ∈ indices,
        uniformProbability (event.filter fun seed => f seed = i) :=
  uniformProbability_eq_sum_fiberwise_internal event indices f hmaps

/-- Independent finite uniform seeds multiply event probabilities. -/
theorem uniformProbability_product
    {Ω : Type u} {Ξ : Type v} [Fintype Ω] [DecidableEq Ω]
    [Fintype Ξ] [DecidableEq Ξ] (P : Ω → Prop) (Q : Ξ → Prop)
    [DecidablePred P] [DecidablePred Q] :
    uniformProbability
        (Finset.univ.filter fun seed : Ω × Ξ => P seed.1 ∧ Q seed.2) =
      uniformProbability (Finset.univ.filter P) *
      uniformProbability (Finset.univ.filter Q) :=
  uniformProbability_product_internal P Q

/-- Relabeling a finite uniform sample space by an equivalence preserves event
probability. -/
theorem uniformProbability_equiv
    {Ω : Type u} {Ξ : Type v} [Fintype Ω] [DecidableEq Ω]
    [Fintype Ξ] [DecidableEq Ξ] (e : Ω ≃ Ξ) (P : Ξ → Prop)
    [DecidablePred P] :
    uniformProbability (Finset.univ.filter fun x : Ω => P (e x)) =
      uniformProbability (Finset.univ.filter P) :=
  uniformProbability_equiv_internal e P

/-- Every point in a finite uniform sample space has reciprocal-cardinality
probability. -/
theorem uniformProbability_eq {Ω : Type u}
    [Fintype Ω] [DecidableEq Ω] (x : Ω) :
    uniformProbability (Finset.univ.filter fun y : Ω => y = x) =
      1 / Fintype.card Ω :=
  uniformProbability_eq_internal x

namespace FiniteEnsemble

variable {α : Type u} {β : Type w}

/-- Ensemble event probabilities are nonnegative. -/
theorem probability_nonneg (D : FiniteEnsemble α) (n : ℕ)
    (P : α → Prop) [DecidablePred P] :
    0 ≤ D.probability n P :=
  probability_nonneg_internal D n P

/-- Ensemble event probabilities are at most one. -/
theorem probability_le_one (D : FiniteEnsemble α) (n : ℕ)
    (P : α → Prop) [DecidablePred P] :
    D.probability n P ≤ 1 :=
  probability_le_one_internal D n P

@[simp] theorem probability_false (D : FiniteEnsemble α) (n : ℕ) :
    D.probability n (fun _ => False) = 0 :=
  probability_false_internal D n

@[simp] theorem probability_true (D : FiniteEnsemble α) (n : ℕ) :
    D.probability n (fun _ => True) = 1 :=
  probability_true_internal D n

theorem probability_not (D : FiniteEnsemble α) (n : ℕ)
    (P : α → Prop) [DecidablePred P] :
    D.probability n (fun x => ¬ P x) = 1 - D.probability n P :=
  probability_not_internal D n P

theorem probability_or_le (D : FiniteEnsemble α) (n : ℕ)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] :
    D.probability n (fun x => P x ∨ Q x) ≤
      D.probability n P + D.probability n Q :=
  probability_or_le_internal D n P Q

theorem probability_mono (D : FiniteEnsemble α) (n : ℕ)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ x, P x → Q x) :
    D.probability n P ≤ D.probability n Q :=
  probability_mono_internal D n P Q hPQ

theorem probability_congr (D : FiniteEnsemble α) (n : ℕ)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ x, P x ↔ Q x) :
    D.probability n P = D.probability n Q :=
  probability_congr_internal D n P Q hPQ

@[simp] theorem probability_map (D : FiniteEnsemble α) (f : α → β)
    (n : ℕ) (P : β → Prop) [DecidablePred P] :
    (D.map f).probability n P = D.probability n (fun x => P (f x)) :=
  probability_map_internal D f n P

theorem sum_mass_eq_one [DecidableEq α] (D : FiniteEnsemble α) (n : ℕ) :
    ∑ x ∈ D.support n, D.mass n x = 1 :=
  sum_mass_eq_one_internal D n

theorem probability_product (D : FiniteEnsemble α) (E : FiniteEnsemble β)
    (n : ℕ) (P : α → Prop) (Q : β → Prop)
    [DecidablePred P] [DecidablePred Q] :
    (D.product E).probability n (fun xy => P xy.1 ∧ Q xy.2) =
      D.probability n P * E.probability n Q :=
  probability_product_internal D E n P Q

theorem probability_dirac (x : ℕ → α) (n : ℕ)
    (P : α → Prop) [DecidablePred P] :
    (dirac x).probability n P = if P (x n) then 1 else 0 :=
  probability_dirac_internal x n P

end FiniteEnsemble

namespace DyadicEnsemble

variable {α : Type u}

/-- The finite-uniform embedding preserves every event probability exactly. -/
@[simp] theorem probability_toFinite (D : DyadicEnsemble α) (n : ℕ)
    (P : α → Prop) [DecidablePred P] :
    D.toFinite.probability n P = D.probability n P :=
  probability_toFinite_internal D n P

end DyadicEnsemble

end Complexity
