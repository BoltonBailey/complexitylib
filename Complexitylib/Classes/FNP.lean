import Complexitylib.Classes.FNP.Defs
import Complexitylib.Classes.FNP.Internal

/-!
# FNP and TFNP

This file defines the function/search complexity classes **FNP** and **TFNP**
(see `FNP/Defs.lean`) and proves the fundamental connection between TFNP and
NP ∩ coNP: if a language has both NP and coNP witness relations, the combined
certificate-finding problem is in TFNP (Megiddo–Papadimitriou 1991).
-/

/-- **NP ∩ coNP yields TFNP** (Megiddo–Papadimitriou 1991): given FNP relations
    `R₁` (witnesses for `x ∈ L`) and `R₂` (witnesses for `x ∉ L`), the tagged
    relation is in TFNP. The tag bit records which type of certificate was found,
    so any solution to the search problem decides `L`.

    Combined with the NP witness theorem
    (`NP = {L | ∃ R ∈ FNP, ∀ x, x ∈ L ↔ ∃ y, R x y}`),
    this establishes that every language in NP ∩ coNP gives rise to a TFNP
    search problem. -/
theorem tfnp_of_np_conp_witnesses
    {R₁ R₂ : List Bool → List Bool → Prop} {L : Language}
    (hR₁ : R₁ ∈ FNP) (hR₂ : R₂ ∈ FNP)
    (h_mem : ∀ x, x ∈ L ↔ ∃ y, R₁ x y)
    (h_nmem : ∀ x, x ∉ L ↔ ∃ y, R₂ x y) :
    tagRelation R₁ R₂ ∈ TFNP := by
  refine ⟨tagRelation_in_FNP hR₁ hR₂, ?_⟩
  intro x
  by_cases hx : x ∈ L
  · obtain ⟨w, hw⟩ := (h_mem x).mp hx
    exact ⟨true :: w, hw⟩
  · obtain ⟨w, hw⟩ := (h_nmem x).mp hx
    exact ⟨false :: w, hw⟩
