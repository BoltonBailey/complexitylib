/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.PadVerts
public import Complexitylib.Classes.PCP.Internal.RegCSP

/-!
# Padding a constraint system

`PadVerts` enlarges a regular graph; here the constraints come along. The fresh
vertices carry self-loops, and those loops are given the trivial constraint, so
they are satisfied by every assignment and never contribute an unsatisfied dart.

Nothing is lost except dilution: the unsatisfied darts are exactly the old ones,
while the total number of darts grows in proportion to the number of vertices.
The unsatisfiability value is therefore scaled by the ratio of the old vertex
count to the new — a constant factor, since padding is only ever to within a
constant multiple.

## Main definitions

- `Complexity.RegCSP.padVerts` — the padded constraint system

## Main results

- `Complexity.RegCSP.card_unsatDarts_padVerts` — the unsatisfied darts are the
  old ones
- `Complexity.RegCSP.satisfiable_padVerts_iff` — satisfiability is unchanged
- `Complexity.RegCSP.unsatVal_padVerts_ge` — the value is diluted by exactly the
  ratio of the vertex counts
-/

@[expose] public section

namespace Complexity

namespace RegCSP

variable {α : Type}

/-- The padded constraint system: fresh vertices, whose self-loops carry the
constraint that is always satisfied. -/
def padVerts (R : RegCSP α) (k : ℕ) : RegCSP α where
  graph := R.graph.padVerts k
  rel := fun v i x y =>
    match v with
    | Sum.inl w => R.rel w i x y
    | Sum.inr _ => true

@[simp] theorem graph_padVerts (R : RegCSP α) (k : ℕ) :
    (R.padVerts k).graph = R.graph.padVerts k := rfl

/-- Restricting an assignment of the padded system to the original vertices. -/
def unpad (R : RegCSP α) {k : ℕ} (a : (R.padVerts k).Assignment) : R.Assignment :=
  fun v => a (Sum.inl v)

/-- Extending an assignment to the padded system. -/
noncomputable def repad [Nonempty α] (R : RegCSP α) {k : ℕ} (a : R.Assignment) :
    (R.padVerts k).Assignment :=
  fun v =>
    match v with
    | Sum.inl w => a w
    | Sum.inr _ => Classical.arbitrary α

theorem unpad_repad [Nonempty α] (R : RegCSP α) {k : ℕ} (a : R.Assignment) :
    R.unpad (R.repad (k := k) a) = a := rfl

theorem satisfies_padVerts_inl (R : RegCSP α) {k : ℕ} (a : (R.padVerts k).Assignment)
    (v : R.graph.V) (i : R.graph.D) :
    (R.padVerts k).Satisfies a (Sum.inl v, i) ↔ R.Satisfies (R.unpad a) (v, i) := Iff.rfl

theorem satisfies_padVerts_inr (R : RegCSP α) {k : ℕ} (a : (R.padVerts k).Assignment)
    (j : Fin k) (i : R.graph.D) : (R.padVerts k).Satisfies a (Sum.inr j, i) := rfl

/-- **The unsatisfied darts are exactly the old ones.** -/
theorem unsatDarts_padVerts (R : RegCSP α) {k : ℕ} (a : (R.padVerts k).Assignment) :
    (R.padVerts k).unsatDarts a
      = (R.unsatDarts (R.unpad a)).image fun p => (Sum.inl p.1, p.2) := by
  classical
  ext p
  constructor
  · intro hp
    rw [mem_unsatDarts] at hp
    obtain ⟨v | j, i⟩ := p
    · exact Finset.mem_image.2 ⟨(v, i), (mem_unsatDarts R).2 hp, rfl⟩
    · exact absurd (R.satisfies_padVerts_inr a j i) hp
  · intro hp
    obtain ⟨⟨w, i'⟩, hw, heq⟩ := Finset.mem_image.1 hp
    rw [← heq, mem_unsatDarts]
    rw [mem_unsatDarts] at hw
    exact hw

theorem card_unsatDarts_padVerts (R : RegCSP α) {k : ℕ}
    (a : (R.padVerts k).Assignment) :
    ((R.padVerts k).unsatDarts a).card = (R.unsatDarts (R.unpad a)).card := by
  classical
  have hinj : Function.Injective
      (fun p : R.Dart => ((Sum.inl p.1, p.2) : (R.padVerts k).Dart)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (by injection h.1) h.2
  rw [unsatDarts_padVerts]
  exact Finset.card_image_of_injective _ hinj

/-- **Satisfiability is unchanged.** -/
theorem satisfiable_padVerts_iff [Nonempty α] (R : RegCSP α) (k : ℕ) :
    (R.padVerts k).Satisfiable ↔ R.Satisfiable := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨R.unpad a, fun p => ?_⟩
    obtain ⟨v, i⟩ := p
    exact (R.satisfies_padVerts_inl a v i).1 (ha (Sum.inl v, i))
  · rintro ⟨b, hb⟩
    refine ⟨R.repad b, fun p => ?_⟩
    obtain ⟨v | j, i⟩ := p
    · rw [satisfies_padVerts_inl, unpad_repad]
      exact hb (v, i)
    · exact R.satisfies_padVerts_inr _ j i

/-! ### The dilution -/

theorem unsatFrac_padVerts (R : RegCSP α) (k : ℕ) (a : (R.padVerts k).Assignment) :
    (R.padVerts k).unsatFrac a
      = ((R.unsatDarts (R.unpad a)).card : ℚ)
        / (((R.graph.order + k) * R.graph.deg : ℕ) : ℚ) := by
  rw [unsatFrac, card_unsatDarts_padVerts]
  congr 2
  rw [graph_padVerts, RegGraph.order_padVerts, RegGraph.deg_padVerts]

/-- **Padding dilutes the value by the ratio of the vertex counts.** -/
theorem unsatVal_padVerts_ge [Fintype α] [Nonempty α] [DecidableEq α]
    (R : RegCSP α) (k : ℕ) (hord : 0 < R.graph.order) :
    R.unsatVal * ((R.graph.order : ℕ) : ℚ) / (((R.graph.order + k : ℕ)) : ℚ)
      ≤ (R.padVerts k).unsatVal := by
  classical
  have hd : (0 : ℚ) < (R.graph.deg : ℕ) := by
    have := R.graph.deg_pos
    exact_mod_cast this
  have ho : (0 : ℚ) < (R.graph.order : ℕ) := by exact_mod_cast hord
  have hok : (0 : ℚ) < ((R.graph.order + k : ℕ) : ℚ) := by
    have : 0 < R.graph.order + k := by omega
    exact_mod_cast this
  have hod : (0 : ℚ) < ((R.graph.order * R.graph.deg : ℕ) : ℚ) := by
    have : 0 < R.graph.order * R.graph.deg := Nat.mul_pos hord R.graph.deg_pos
    exact_mod_cast this
  have hokd : (0 : ℚ) < (((R.graph.order + k) * R.graph.deg : ℕ) : ℚ) := by
    have : 0 < (R.graph.order + k) * R.graph.deg :=
      Nat.mul_pos (by omega) R.graph.deg_pos
    exact_mod_cast this
  refine Finset.le_inf' _ _ fun a _ => ?_
  have hle : R.unsatVal ≤ R.unsatFrac (R.unpad a) := R.unsatVal_le _
  rw [unsatFrac] at hle
  rw [le_div_iff₀ hod] at hle
  rw [unsatFrac_padVerts, div_le_div_iff₀ hok hokd]
  push_cast at hle ⊢
  nlinarith [hle, hd, ho, hok]

end RegCSP

end Complexity
