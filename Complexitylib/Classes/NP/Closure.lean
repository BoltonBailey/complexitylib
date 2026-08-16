/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.NP.CoNP
public import Complexitylib.Classes.NP.Internal.Closure

/-!
# Closure of NP and coNP under polynomial-time reductions

## Main results

- `mem_NP_preimage` — polynomial-time preprocessing preserves membership
  in `NP`.
- `MapReducesPoly.mem_NP` / `MapReducesPoly.mem_coNP` — membership in `NP`
  and `coNP` transports backward along Karp reductions.
- `NPComplete.mem_coNP_iff_NP_eq_coNP` — an NP-complete language lies in
  `coNP` iff `NP = coNP` (Arora–Barak, discussion after Definition 2.20).
-/


@[expose] public section

namespace Complexity

/-- If `f` is polynomial-time computable and `L` is in `NP`, then the
preimage language `{x | f x ∈ L}` is in `NP`. -/
theorem mem_NP_preimage {f : List Bool → List Bool} {L : Language}
    (hf : f ∈ FP) (hL : L ∈ NP) : f ⁻¹' L ∈ NP :=
  mem_NP_preimage_internal hf hL

/-- **NP is closed under polynomial-time many-one reductions.** Membership
in `NP` transports backward along a Karp reduction. -/
theorem MapReducesPoly.mem_NP {L₁ L₂ : Language}
    (hred : L₁ ≤ₚ L₂) (hL₂ : L₂ ∈ NP) : L₁ ∈ NP := by
  obtain ⟨f, hf, hcorrect⟩ := hred
  have heq : L₁ = f ⁻¹' L₂ := Set.ext fun x => hcorrect x
  rw [heq]
  exact mem_NP_preimage hf hL₂

/-- **coNP is closed under polynomial-time many-one reductions.** -/
theorem MapReducesPoly.mem_coNP {L₁ L₂ : Language}
    (hred : L₁ ≤ₚ L₂) (hL₂ : L₂ ∈ coNP) : L₁ ∈ coNP :=
  mem_complClass.mpr (hred.compl.mem_NP (mem_complClass.mp hL₂))

/-- **An NP-complete language lies in `coNP` iff `NP = coNP`** (Arora–Barak,
discussion after Definition 2.20): once a single NP-complete language has a
coNP certificate, every NP language does. -/
theorem NPComplete.mem_coNP_iff_NP_eq_coNP {L : Language}
    (h : NPComplete L) : L ∈ coNP ↔ NP = coNP := by
  constructor
  · intro hL
    have hsub : NP ⊆ coNP := fun L' hL' => (h.2 L' hL').mem_coNP hL
    refine Set.Subset.antisymm hsub fun L' hL' => ?_
    have hcompl : L'ᶜ ∈ coNP := hsub (mem_complClass.mp hL')
    have := mem_complClass.mp hcompl
    rwa [compl_compl] at this
  · intro hEq
    exact hEq ▸ h.1

end Complexity
