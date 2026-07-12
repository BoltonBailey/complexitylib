/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.Formula

/-!
# Restrictions

A **restriction** is a partial assignment that fixes some variables to constants
and leaves the rest free — the basic operation behind random-restriction and
switching-lemma arguments (roadmap track L4). This module defines restrictions,
their composition, and proves that evaluating a *restricted* Boolean formula
agrees with evaluating the original under the restriction applied to the
assignment (evaluation commutes with restriction).

## Main definitions and results

- `Restriction`, `Restriction.applyTo`, `Restriction.comp`
- `Restriction.applyTo_comp` — applying a composite restriction is applying the
  two in sequence
- `BoolFormula.restrict`, `BoolFormula.eval_restrict` — evaluation commutes with
  restriction
-/

namespace Complexity

/-- A restriction: a partial assignment fixing some variables (`some b`) and
    leaving the rest free (`none`). -/
abbrev Restriction := ℕ → Option Bool

namespace Restriction

/-- Apply a restriction on top of a total assignment: fixed variables take the
    restriction's value, free variables fall back to the assignment. -/
def applyTo (ρ : Restriction) (α : ℕ → Bool) : ℕ → Bool := fun i => (ρ i).getD (α i)

/-- Compose two restrictions: the first takes precedence, the second fills in the
    variables the first leaves free. -/
def comp (ρ₁ ρ₂ : Restriction) : Restriction := fun i => (ρ₁ i).or (ρ₂ i)

/-- Applying a composite restriction is the same as applying the two restrictions
    in sequence. -/
theorem applyTo_comp (ρ₁ ρ₂ : Restriction) (α : ℕ → Bool) :
    applyTo (comp ρ₁ ρ₂) α = applyTo ρ₁ (applyTo ρ₂ α) := by
  funext i
  simp only [applyTo, comp]
  cases ρ₁ i <;> rfl

end Restriction

namespace BoolFormula

/-- Apply a restriction to a formula, replacing each fixed variable by the
    corresponding constant and leaving free variables in place. -/
def restrict (ρ : Restriction) : BoolFormula → BoolFormula
  | var i => match ρ i with
    | some b => if b then tru else fls
    | none => var i
  | tru => tru
  | fls => fls
  | neg φ => neg (restrict ρ φ)
  | conj φ ψ => conj (restrict ρ φ) (restrict ρ ψ)
  | disj φ ψ => disj (restrict ρ φ) (restrict ρ ψ)

/-- **Evaluation commutes with restriction.** Evaluating a restricted formula at
    `α` equals evaluating the original formula at the restriction applied to
    `α`. -/
theorem eval_restrict (ρ : Restriction) (α : ℕ → Bool) (φ : BoolFormula) :
    eval α (restrict ρ φ) = eval (Restriction.applyTo ρ α) φ := by
  induction φ with
  | var i =>
    cases h : ρ i with
    | none => simp [restrict, eval, Restriction.applyTo, h]
    | some b => cases b <;> simp [restrict, eval, Restriction.applyTo, h]
  | tru => rfl
  | fls => rfl
  | neg φ ih => simp only [restrict, eval, ih]
  | conj φ ψ ihφ ihψ => simp only [restrict, eval, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp only [restrict, eval, ihφ, ihψ]

/-- Restriction preserves the tree size: fixing a variable replaces a leaf by a
    constant leaf, and connectives are untouched. So `(restrict ρ φ).size = φ.size`
    — restriction never grows a formula (a fact width/size arguments rely on). -/
theorem restrict_size (ρ : Restriction) (φ : BoolFormula) :
    (restrict ρ φ).size = φ.size := by
  induction φ with
  | var i =>
    simp only [restrict]
    cases ρ i with
    | none => rfl
    | some b => cases b <;> rfl
  | tru => rfl
  | fls => rfl
  | neg φ ih => simp only [restrict, size, ih]
  | conj φ ψ ihφ ihψ => simp only [restrict, size, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp only [restrict, size, ihφ, ihψ]

/-- Restriction also preserves the leaf count: `(restrict ρ φ).leaves = φ.leaves`. -/
theorem restrict_leaves (ρ : Restriction) (φ : BoolFormula) :
    (restrict ρ φ).leaves = φ.leaves := by
  induction φ with
  | var i =>
    simp only [restrict]
    cases ρ i with
    | none => rfl
    | some b => cases b <;> rfl
  | tru => rfl
  | fls => rfl
  | neg φ ih => simp only [restrict, leaves, ih]
  | conj φ ψ ihφ ihψ => simp only [restrict, leaves, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp only [restrict, leaves, ihφ, ihψ]

/-- Restriction preserves the formula depth exactly: it only relabels leaves,
    leaving the connective tree — and hence every root-to-leaf path length —
    untouched. So `(restrict ρ φ).depth = φ.depth`. -/
theorem restrict_depth (ρ : Restriction) (φ : BoolFormula) :
    (restrict ρ φ).depth = φ.depth := by
  induction φ with
  | var i =>
    simp only [restrict]
    cases ρ i with
    | none => rfl
    | some b => cases b <;> rfl
  | tru => rfl
  | fls => rfl
  | neg φ ih => simp only [restrict, depth, ih]
  | conj φ ψ ihφ ihψ => simp only [restrict, depth, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp only [restrict, depth, ihφ, ihψ]

/-- Restriction only ever removes variables: `vars (restrict ρ φ) ⊆ vars φ`. Fixing
    a variable turns its leaf into a constant (dropping it); free variables are
    untouched. This is the variable-tracking fact switching-lemma arguments use to
    bound the surviving support after a random restriction. -/
theorem vars_restrict_subset (ρ : Restriction) (φ : BoolFormula) :
    vars (restrict ρ φ) ⊆ vars φ := by
  induction φ with
  | var i =>
    simp only [restrict]
    cases ρ i with
    | none => simp [vars]
    | some b => cases b <;> simp [vars]
  | tru => simp [restrict, vars]
  | fls => simp [restrict, vars]
  | neg φ ih => simpa [restrict, vars] using ih
  | conj φ ψ ihφ ihψ =>
    simp only [restrict, vars]
    exact Finset.union_subset_union ihφ ihψ
  | disj φ ψ ihφ ihψ =>
    simp only [restrict, vars]
    exact Finset.union_subset_union ihφ ihψ

end BoolFormula

end Complexity
