/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.AverageCase.Ensemble.Defs
public import Complexitylib.Classes.AverageCase.Ensemble.Internal

/-!
# Exact dyadic distribution ensembles

This module exposes finite distribution ensembles represented by uniform Boolean
seeds. It provides exact event probabilities, pushforwards, point masses,
independent products, and normalization of the induced finite mass function.

Polynomial-time samplability and heuristic algorithms are deliberately separate
layers: these definitions and counting theorems make no computational claim about
the sample map.
-/


public section

universe u v

namespace Complexity

namespace DyadicEnsemble

variable {α : Type u} {β : Type v}

/-- Ensemble event probabilities are nonnegative. -/
theorem probability_nonneg (D : DyadicEnsemble α) (n : ℕ)
    (P : α → Prop) [DecidablePred P] :
    0 ≤ D.probability n P :=
  probability_nonneg_internal D n P

/-- Ensemble event probabilities are at most one. -/
theorem probability_le_one (D : DyadicEnsemble α) (n : ℕ)
    (P : α → Prop) [DecidablePred P] :
    D.probability n P ≤ 1 :=
  probability_le_one_internal D n P

/-- The impossible event has probability zero. -/
@[simp] theorem probability_false (D : DyadicEnsemble α) (n : ℕ) :
    D.probability n (fun _ => False) = 0 :=
  probability_false_internal D n

/-- The certain event has probability one. -/
@[simp] theorem probability_true (D : DyadicEnsemble α) (n : ℕ) :
    D.probability n (fun _ => True) = 1 :=
  probability_true_internal D n

/-- Complementary events have complementary probabilities. -/
theorem probability_not (D : DyadicEnsemble α) (n : ℕ)
    (P : α → Prop) [DecidablePred P] :
    D.probability n (fun x => ¬ P x) = 1 - D.probability n P :=
  probability_not_internal D n P

/-- Union bound for two predicates on one ensemble slice. -/
theorem probability_or_le (D : DyadicEnsemble α) (n : ℕ)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] :
    D.probability n (fun x => P x ∨ Q x) ≤
      D.probability n P + D.probability n Q :=
  probability_or_le_internal D n P Q

/-- Event probability is monotone under predicate implication. -/
theorem probability_mono (D : DyadicEnsemble α) (n : ℕ)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ x, P x → Q x) :
    D.probability n P ≤ D.probability n Q :=
  probability_mono_internal D n P Q hPQ

/-- Extensionally equal events have equal probability. -/
theorem probability_congr (D : DyadicEnsemble α) (n : ℕ)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ x, P x ↔ Q x) :
    D.probability n P = D.probability n Q :=
  probability_congr_internal D n P Q hPQ

/-- Exact pushforward law: measuring `P` after mapping samples by `f` is the
same as measuring the preimage of `P` in the source ensemble. -/
@[simp] theorem probability_map (D : DyadicEnsemble α) (f : α → β)
    (n : ℕ) (P : β → Prop) [DecidablePred P] :
    (D.map f).probability n P = D.probability n (fun x => P (f x)) :=
  probability_map_internal D f n P

/-- The masses of all outputs in a slice's finite support sum exactly to one. -/
theorem sum_mass_eq_one [DecidableEq α] (D : DyadicEnsemble α) (n : ℕ) :
    ∑ x ∈ D.support n, D.mass n x = 1 :=
  sum_mass_eq_one_internal D n

/-- Events on independently sampled components have product probability. -/
theorem probability_product (D : DyadicEnsemble α) (E : DyadicEnsemble β)
    (n : ℕ) (P : α → Prop) (Q : β → Prop)
    [DecidablePred P] [DecidablePred Q] :
    (D.product E).probability n (fun xy => P xy.1 ∧ Q xy.2) =
      D.probability n P * E.probability n Q :=
  probability_product_internal D E n P Q

/-- A point mass assigns probability one exactly to events containing its
selected point. -/
theorem probability_dirac (x : ℕ → α) (n : ℕ)
    (P : α → Prop) [DecidablePred P] :
    (dirac x).probability n P = if P (x n) then 1 else 0 :=
  probability_dirac_internal x n P

/-- Event probability under uniform `n`-bit lists is ordinary finite uniform
probability over `Fin n → Bool`. -/
theorem probability_uniformBits (n : ℕ)
    (P : List Bool → Prop) [DecidablePred P] :
    uniformBits.probability n P =
      eventProb (Finset.univ.filter fun seed : Fin n → Bool =>
        P (List.ofFn seed)) :=
  probability_uniformBits_internal n P

end DyadicEnsemble

end Complexity
