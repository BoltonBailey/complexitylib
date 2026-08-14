/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.NP.Reduction
public import Complexitylib.Classes.Containments

/-!
# coNP: structural theory and coNP-completeness

This file develops the elementary structural theory of `coNP` on top of the
definition `coNP = complClass NP` from `Complexitylib.Classes.NP`:

* `P_subset_coNP` and `P_subset_NP_inter_coNP` — deterministic polynomial
  time sits inside `NP ∩ coNP`, via closure of `P` under complement.
* `MapReducesPoly.compl` — a Karp reduction `L₁ ≤ₚ L₂` is simultaneously a
  reduction `L₁ᶜ ≤ₚ L₂ᶜ` (the *same* function witnesses both).
* `coNPHard` / `coNPComplete` — hardness and completeness for `coNP`, dual
  to `NPHard` / `NPComplete`.
* `NPHard.compl`, `NPComplete.compl` and their converses — completeness
  dualizes: `L` is NP-complete iff `Lᶜ` is coNP-complete.
* `NP_eq_coNP_of_P_eq_NP` — if `P = NP` then `NP = coNP`; contrapositively
  (`P_ne_NP_of_NP_ne_coNP`), separating `NP` from `coNP` separates `P`
  from `NP`.

The headline application is `SAT.coNPComplete_compl_language` (the
complement of SAT is coNP-complete), in `Complexitylib/SAT/CoNP.lean`.
-/


@[expose] public section

namespace Complexity

/-! ### Complements and membership -/

/-- Complementation swaps `NP` and `coNP`: `Lᶜ ∈ coNP ↔ L ∈ NP`.
    (The companion direction `L ∈ coNP ↔ Lᶜ ∈ NP` is `mem_complClass`.) -/
@[simp] theorem compl_mem_coNP_iff {L : Language} : Lᶜ ∈ coNP ↔ L ∈ NP := by
  rw [coNP, mem_complClass, compl_compl]

/-- **P is contained in coNP.** A language decidable in deterministic
    polynomial time has its complement decidable in deterministic polynomial
    time (`P_compl`), hence in `NP`. -/
theorem P_subset_coNP : P ⊆ coNP := fun _ hL =>
  mem_complClass.mpr (P_subset_NP (P_compl hL))

/-- **P is contained in NP ∩ coNP** (Arora–Barak, discussion after
    Definition 2.20). Whether the containment is strict is open. -/
theorem P_subset_NP_inter_coNP : P ⊆ NP ∩ coNP :=
  Set.subset_inter P_subset_NP P_subset_coNP

/-! ### Reductions dualize -/

/-- **Karp reductions dualize to complements.** The same polynomial-time
    function that reduces `L₁` to `L₂` also reduces `L₁ᶜ` to `L₂ᶜ`, since
    `x ∈ L₁ ↔ f x ∈ L₂` gives `x ∉ L₁ ↔ f x ∉ L₂`. -/
theorem MapReducesPoly.compl {L₁ L₂ : Language} (h : L₁ ≤ₚ L₂) : L₁ᶜ ≤ₚ L₂ᶜ := by
  obtain ⟨f, hf, hf'⟩ := h
  exact ⟨f, hf, fun x => not_congr (hf' x)⟩

/-! ### coNP-hardness and coNP-completeness -/

/-- **coNP-hardness.** `L` is coNP-hard when every language in `coNP`
    reduces to `L` in polynomial time. -/
def coNPHard (L : Language) : Prop := ∀ L' ∈ coNP, L' ≤ₚ L

/-- **coNP-completeness.** `L` is coNP-complete when it is in `coNP` and
    coNP-hard. -/
def coNPComplete (L : Language) : Prop := L ∈ coNP ∧ coNPHard L

/-- coNP-hardness transfers forward along a polynomial-time many-one
    reduction. -/
theorem coNPHard.of_reduction {L₁ L₂ : Language}
    (h₁ : coNPHard L₁) (h₂ : L₁ ≤ₚ L₂) : coNPHard L₂ :=
  fun L hL => (h₁ L hL).trans h₂

/-- A language in `coNP` is coNP-complete when a coNP-hard language reduces
    to it. -/
theorem coNPComplete.of_mem_of_reduction {L₁ L₂ : Language}
    (h₁ : coNPHard L₁) (hmem : L₂ ∈ coNP) (h₂ : L₁ ≤ₚ L₂) :
    coNPComplete L₂ :=
  ⟨hmem, h₁.of_reduction h₂⟩

/-- coNP-completeness transfers forward along a polynomial-time reduction
    once membership of the target language in `coNP` is known. -/
theorem coNPComplete.transfer {L₁ L₂ : Language}
    (h₁ : coNPComplete L₁) (hmem : L₂ ∈ coNP) (h₂ : L₁ ≤ₚ L₂) :
    coNPComplete L₂ :=
  coNPComplete.of_mem_of_reduction h₁.2 hmem h₂

/-! ### Completeness dualizes -/

/-- The complement of an NP-hard language is coNP-hard: any `L' ∈ coNP` has
    `L'ᶜ ∈ NP`, so `L'ᶜ ≤ₚ L`, and dualizing gives `L' ≤ₚ Lᶜ`. -/
theorem NPHard.compl {L : Language} (h : NPHard L) : coNPHard Lᶜ := fun L' hL' => by
  have hred := (h L'ᶜ (mem_complClass.mp hL')).compl
  rwa [compl_compl] at hred

/-- The complement of a coNP-hard language is NP-hard. -/
theorem coNPHard.compl {L : Language} (h : coNPHard L) : NPHard Lᶜ := fun L' hL' => by
  have hred := (h L'ᶜ (compl_mem_coNP_iff.mpr hL')).compl
  rwa [compl_compl] at hred

/-- **The complement of an NP-complete language is coNP-complete**
    (Arora–Barak, Definition 2.20 and the surrounding discussion). -/
theorem NPComplete.compl {L : Language} (h : NPComplete L) : coNPComplete Lᶜ :=
  ⟨compl_mem_coNP_iff.mpr h.1, h.2.compl⟩

/-- **The complement of a coNP-complete language is NP-complete.** -/
theorem coNPComplete.compl {L : Language} (h : coNPComplete L) : NPComplete Lᶜ :=
  ⟨mem_complClass.mp h.1, h.2.compl⟩

/-! ### `P = NP` collapses `NP` and `coNP` -/

/-- **If `P = NP` then `NP = coNP`.** Under `P = NP` the class `NP` inherits
    closure under complement from `P` (`P_compl`), and a class closed under
    complement equals its complement class. -/
theorem NP_eq_coNP_of_P_eq_NP (h : P = NP) : NP = coNP := by
  have hcompl : ∀ L : Language, L ∈ NP → Lᶜ ∈ NP := fun L hL => by
    rw [← h] at hL ⊢
    exact P_compl hL
  ext L
  refine ⟨fun hL => mem_complClass.mpr (hcompl L hL), fun hL => ?_⟩
  have hLcc := hcompl Lᶜ (mem_complClass.mp hL)
  rwa [compl_compl] at hLcc

/-- **If `NP ≠ coNP` then `P ≠ NP`.** The standard route to `P ≠ NP` through
    the (believed stronger) separation of `NP` from `coNP`. -/
theorem P_ne_NP_of_NP_ne_coNP (h : NP ≠ coNP) : P ≠ NP :=
  fun hP => h (NP_eq_coNP_of_P_eq_NP hP)

end Complexity
