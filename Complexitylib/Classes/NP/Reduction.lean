/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.NP
import Complexitylib.Classes.P.Defs

/-!
# Polynomial-time many-one reductions and NP-completeness

This file defines **polynomial-time many-one (Karp) reductions** `L ≤ₚ L'` and
the derived notions **`NPHard`** and **`NPComplete`**, following Arora–Barak
(Definitions 2.7, 2.8).

A reduction `L ≤ₚ L'` is a polynomial-time computable function `f` (i.e. `f ∈ FP`)
such that `x ∈ L ↔ f x ∈ L'`. A language is NP-hard when every language in `NP`
reduces to it, and NP-complete when it is additionally a member of `NP`.

The headline application is `SAT.NPComplete_language` (Cook–Levin), in
`Complexitylib/SAT/CookLevin.lean`.
-/

namespace Complexity


/-- **Polynomial-time many-one reduction.** `MapReducesPoly L L'` (written
    `L ≤ₚ L'`) holds when there is a polynomial-time computable function `f`
    (`f ∈ FP`) with `x ∈ L ↔ f x ∈ L'` for every input `x`. -/
def MapReducesPoly (L L' : Language) : Prop :=
  ∃ f : List Bool → List Bool, f ∈ FP ∧ ∀ x, x ∈ L ↔ f x ∈ L'

@[inherit_doc] infix:50 " ≤ₚ " => MapReducesPoly

/-- **NP-hardness.** `L` is NP-hard when every language in `NP` reduces to `L`
    in polynomial time. -/
def NPHard (L : Language) : Prop := ∀ L' ∈ NP, L' ≤ₚ L

/-- **NP-completeness.** `L` is NP-complete when it is in `NP` and NP-hard. -/
def NPComplete (L : Language) : Prop := L ∈ NP ∧ NPHard L

/-! ### `≤ₚ` is a preorder, modulo two `FP` facts

Reflexivity and transitivity of polynomial-time many-one reducibility follow
purely from `FP` being closed under identity and composition. The two lemmas
below isolate exactly those two facts; discharging them (via a copy Turing
machine for `id ∈ FP`, and a sequential-composition machine for closure under
`∘`) is all that remains to make `≤ₚ` a genuine preorder. -/

/-- **Reflexivity of `≤ₚ` reduces to `id ∈ FP`.** -/
theorem MapReducesPoly.refl_of_id_mem (hid : id ∈ FP) (L : Language) : L ≤ₚ L :=
  ⟨id, hid, fun _ => Iff.rfl⟩

/-- **Transitivity of `≤ₚ` reduces to `FP` being closed under composition.** -/
theorem MapReducesPoly.trans_of_comp
    (hcomp : ∀ f g : List Bool → List Bool, f ∈ FP → g ∈ FP → (g ∘ f) ∈ FP)
    {L₁ L₂ L₃ : Language} (h₁ : L₁ ≤ₚ L₂) (h₂ : L₂ ≤ₚ L₃) : L₁ ≤ₚ L₃ := by
  obtain ⟨f, hf, hf'⟩ := h₁
  obtain ⟨g, hg, hg'⟩ := h₂
  exact ⟨g ∘ f, hcomp f g hf hg, fun x => (hf' x).trans (hg' (f x))⟩

end Complexity
