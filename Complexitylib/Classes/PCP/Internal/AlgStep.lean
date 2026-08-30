/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.Dinur
public import Complexitylib.Classes.PCP.Internal.AlgCompose

/-!
# One round, in numbers

A round of amplification multiplies both counts of a constraint graph by a
constant factor. This module records those factors, so an algorithm that writes
the round's output knows how big it is.

## Main results

- `Complexity.MultiTest.numVerts_toGraph` — the vertices of a family's graph
- `Complexity.RegCSP.card_pos_compose` — the positions of a composed proof
- `Complexity.Dinur.numVerts_step` — a round's vertex count
- `Complexity.MultiTest.tailNum_eq` — the first endpoint of an edge
- `Complexity.MultiTest.rel_toGraph_eq` — its constraint, from the verdict and
  the read
-/

@[expose] public section

namespace Complexity

open BooleanAnalysis

namespace MultiTest

variable {Pos E Q : Type} (M : MultiTest Pos E Q) [Fintype Pos] [Fintype E] [Fintype Q]
  [NumEnc Pos] [NumEnc E] [NumEnc Q]

/-- **The vertices**: one per position, and one per (test, random string). -/
theorem numVerts_toGraph :
    M.toGraph.numVerts = Fintype.card Pos + Fintype.card E * 2 ^ M.R := by
  show Fintype.card (Pos ⊕ (E × Cube M.R)) = _
  rw [Fintype.card_sum, Fintype.card_prod, card_cube]

/-- Splitting a number into a quotient and a remainder, with the remainder
itself split. -/
theorem split_mixed {a b c C Q : ℕ} (hb : b < C) (hc : c < Q) :
    (a * (C * Q) + (b * Q + c)) / (C * Q) = a
      ∧ (a * (C * Q) + (b * Q + c)) % (C * Q) / Q = b
      ∧ (a * (C * Q) + (b * Q + c)) % Q = c := by
  have hQ : 0 < Q := Nat.lt_of_le_of_lt (Nat.zero_le _) hc
  have hCQ : 0 < C * Q := Nat.mul_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hb) hQ
  have hlt : b * Q + c < C * Q := by
    have : b * Q + Q ≤ C * Q := by
      have : (b + 1) * Q ≤ C * Q := Nat.mul_le_mul_right _ hb
      rw [Nat.add_mul, Nat.one_mul] at this
      exact this
    omega
  have hmod : (a * (C * Q) + (b * Q + c)) % (C * Q) = b * Q + c := by
    rw [Nat.mul_comm a (C * Q), Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.mul_comm a (C * Q), Nat.mul_add_div hCQ, Nat.div_eq_of_lt hlt, Nat.add_zero]
  · rw [hmod, Nat.mul_comm b Q, Nat.mul_add_div hQ, Nat.div_eq_of_lt hc, Nat.add_zero]
  · have hre : a * (C * Q) + (b * Q + c) = c + (a * C + b) * Q := by ring
    rw [hre, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

omit [Fintype Pos] [NumEnc Pos] in
/-- **How an edge number splits**: the test, the random string, the read. -/
theorem enc_edgeOf_split (k : Fin (Fintype.card M.Edge)) :
    NumEnc.enc (M.edgeOf k).1 = k.val / (2 ^ M.R * Fintype.card Q)
      ∧ NumEnc.enc (M.edgeOf k).2.1 = k.val % (2 ^ M.R * Fintype.card Q) / Fintype.card Q
      ∧ NumEnc.enc (M.edgeOf k).2.2 = k.val % Fintype.card Q := by
  have hk : k.val = NumEnc.enc (M.edgeOf k).1 * (2 ^ M.R * Fintype.card Q)
      + (NumEnc.enc (M.edgeOf k).2.1 * Fintype.card Q + NumEnc.enc (M.edgeOf k).2.2) := by
    rw [← M.enc_edgeOf k, M.enc_edge]
    rw [show NumEnc.card (Cube M.R) = 2 ^ M.R from by
      rw [NumEnc.card_eq_fintype_card, card_cube]]
    rw [show NumEnc.card Q = Fintype.card Q from NumEnc.card_eq_fintype_card Q]
  have hb : NumEnc.enc (M.edgeOf k).2.1 < 2 ^ M.R := by
    have := NumEnc.enc_lt (M.edgeOf k).2.1
    rwa [NumEnc.card_eq_fintype_card, card_cube] at this
  have hc : NumEnc.enc (M.edgeOf k).2.2 < Fintype.card Q := by
    have := NumEnc.enc_lt (M.edgeOf k).2.2
    rwa [NumEnc.card_eq_fintype_card] at this
  obtain ⟨h1, h2, h3⟩ := split_mixed hb hc
  exact ⟨by rw [hk, h1], by rw [hk, h2], by rw [hk, h3]⟩

/-- **The first endpoint of an edge, in numbers.** -/
noncomputable def tailNum (k : ℕ) : ℕ :=
  Fintype.card Pos
    + (k / (2 ^ M.R * Fintype.card Q) * 2 ^ M.R
      + k % (2 ^ M.R * Fintype.card Q) / Fintype.card Q)

theorem tailNum_eq (k : Fin (Fintype.card M.Edge)) :
    M.tailNum k.val = (M.toGraph.tail k).val := by
  obtain ⟨h1, h2, _⟩ := M.enc_edgeOf_split k
  rw [tailNum, M.val_tail_toGraph, ← h1, ← h2, NumEnc.card_eq_fintype_card Pos,
    NumEnc.card_eq_fintype_card (Cube M.R), card_cube]

/-- The constraint an edge carries: the test vertex's answers must pass the
test, and the read's answer must be the position's bit. -/
def relOfCheck (chk : (Q → ZMod 2) → Bool) (i : Q) :
    Alpha Q → Alpha Q → Bool :=
  fun l₁ l₂ => decide (chk l₁.2 = true ∧ l₁.2 i = l₂.1)

/-- **The constraint depends only on the verdict and the read.** -/
theorem rel_toGraph_eq (k : Fin (Fintype.card M.Edge)) :
    M.toGraph.rel k
      = relOfCheck (M.check (M.edgeOf k).1 (M.edgeOf k).2.1) (M.edgeOf k).2.2 := rfl

end MultiTest

namespace RegCSP

variable {β : Type} [Fintype β] [DecidableEq β] [Nonempty β] (R : RegCSP β)
  [NumEnc R.graph.V] [NumEnc R.graph.D] (B : ℕ)

omit [Fintype β] [DecidableEq β] [Nonempty β] [NumEnc R.graph.V] [NumEnc R.graph.D] in
/-- **The positions of a composed proof**: an encoding block per vertex, and a
linear and a quadratic table per dart. -/
theorem card_pos_compose :
    Fintype.card (R.Pos (B := B))
      = R.graph.order * 2 ^ B
        + (R.graph.order * R.graph.deg * 2 ^ Tester.nOf B
          + R.graph.order * R.graph.deg * 2 ^ (Tester.nOf B * Tester.nOf B)) := by
  show Fintype.card ((R.graph.V × Cube B) ⊕
    ((R.Dart × Cube (Tester.nOf B)) ⊕ (R.Dart × Cube (Tester.nOf B * Tester.nOf B)))) = _
  rw [Fintype.card_sum, Fintype.card_sum,
    show Fintype.card (R.graph.V × Cube B) = R.graph.order * 2 ^ B from by
      rw [Fintype.card_prod, card_cube]; rfl,
    show Fintype.card (R.Dart × Cube (Tester.nOf B))
        = R.graph.order * R.graph.deg * 2 ^ Tester.nOf B from by
      rw [Fintype.card_prod, card_cube, R.card_dart],
    show Fintype.card (R.Dart × Cube (Tester.nOf B * Tester.nOf B))
        = R.graph.order * R.graph.deg * 2 ^ (Tester.nOf B * Tester.nOf B) from by
      rw [Fintype.card_prod, card_cube, R.card_dart]]

omit [DecidableEq β] [Nonempty β] [NumEnc R.graph.V] [NumEnc R.graph.D] in
/-- The composed test's randomness. -/
theorem R_compose (enc : β → Cube B) : (R.compose enc).R = Tester.ROf B := rfl

omit [DecidableEq β] [Nonempty β] in
/-- **An edge number splits into a vertex, a dart, a string and a read.** -/
theorem edge_split (enc : β → Cube B) (k : Fin (Fintype.card (R.compose enc).Edge)) :
    k.val = ((NumEnc.enc ((R.compose enc).edgeOf k).1.1 * NumEnc.card R.graph.D
          + NumEnc.enc ((R.compose enc).edgeOf k).1.2)
        * 2 ^ Tester.ROf B
        + NumEnc.enc ((R.compose enc).edgeOf k).2.1) * 22
      + NumEnc.enc ((R.compose enc).edgeOf k).2.2 := by
  have h1 := MultiTest.enc_edgeOf (M := R.compose enc) k
  have h2 := MultiTest.enc_edge (M := R.compose enc) ((R.compose enc).edgeOf k)
  have h3 := RegCSP.enc_dart R ((R.compose enc).edgeOf k).1
  have hq : NumEnc.card ReadIdx = 22 := rfl
  have hcube : NumEnc.card (Cube (R.compose enc).R) = 2 ^ Tester.ROf B := by
    rw [NumEnc.card_eq_fintype_card, card_cube, R_compose]
  rw [h2, h3, hq, hcube] at h1
  rw [← h1]
  ring

omit [DecidableEq β] [Nonempty β] [NumEnc R.graph.V] [NumEnc R.graph.D] in
/-- **The first endpoint, from an edge's split.** -/
theorem tailNum_split (enc : β → Cube B) (a c d : ℕ) (hc : c < 2 ^ Tester.ROf B)
    (hd : d < 22) :
    (R.compose enc).tailNum ((a * 2 ^ Tester.ROf B + c) * 22 + d)
      = Fintype.card (R.Pos (B := B)) + (a * 2 ^ Tester.ROf B + c) := by
  have hQ : Fintype.card ReadIdx = 22 := rfl
  have hR : (2 : ℕ) ^ (R.compose enc).R = 2 ^ Tester.ROf B := rfl
  have hre : (a * 2 ^ Tester.ROf B + c) * 22 + d
      = a * (2 ^ Tester.ROf B * 22) + (c * 22 + d) := by ring
  obtain ⟨h1, h2, _⟩ := MultiTest.split_mixed (a := a) hc hd
  rw [MultiTest.tailNum, hQ, hR, hre, h1, h2]

omit [DecidableEq β] [Nonempty β] [NumEnc R.graph.V] [NumEnc R.graph.D] in
/-- **The first endpoint**, with the string count given by name. -/
theorem tailNum_split' (enc : β → Cube B) (cZ a c d : ℕ) (hcZ : cZ = 2 ^ Tester.ROf B)
    (hc : c < cZ) (hd : d < 22) :
    (R.compose enc).tailNum ((a * cZ + c) * 22 + d)
      = Fintype.card (R.Pos (B := B)) + (a * cZ + c) := by
  subst hcZ
  exact tailNum_split R B enc a c d hc hd

omit [DecidableEq β] [Nonempty β] in
/-- **An edge's data**, packaged so that a caller never has to spell the
composed system out: the test, the string and the read it names, together with
how its number splits. -/
theorem edge_data (enc : β → Cube B) (e : ℕ)
    (he : e < (R.compose enc).toGraph.numEdges) :
    ∃ (p : R.Dart) (z : Cube (Tester.ROf B)) (i : ReadIdx),
      p = ((R.compose enc).edgeOf ⟨e, he⟩).1
        ∧ z = ((R.compose enc).edgeOf ⟨e, he⟩).2.1
        ∧ i = ((R.compose enc).edgeOf ⟨e, he⟩).2.2
        ∧ e = ((NumEnc.enc p.1 * NumEnc.card R.graph.D + NumEnc.enc p.2)
              * 2 ^ Tester.ROf B + NumEnc.enc z) * 22 + NumEnc.enc i := by
  refine ⟨((R.compose enc).edgeOf ⟨e, he⟩).1, ((R.compose enc).edgeOf ⟨e, he⟩).2.1,
    ((R.compose enc).edgeOf ⟨e, he⟩).2.2, rfl, rfl, rfl, ?_⟩
  exact edge_split R B enc ⟨e, he⟩

end RegCSP

namespace Dinur

variable (E : ExpanderFamily)

/-- The constant factor by which a round multiplies the vertex count. -/
noncomputable def vertFactor (q : ℕ) : ℕ :=
  2 * (2 ^ bits E (powT K q)
    + powDeg E ^ powT K q * q ^ powT K q
      * (2 ^ Tester.nOf (bits E (powT K q))
        + 2 ^ (Tester.nOf (bits E (powT K q)) * Tester.nOf (bits E (powT K q)))
        + 2 ^ Tester.ROf (bits E (powT K q))))

/-- The constant number of positions a round makes per edge of its input. -/
noncomputable def posFactor (q : ℕ) : ℕ :=
  2 * (2 ^ bits E (powT K q)
    + powDeg E ^ powT K q * q ^ powT K q
      * (2 ^ Tester.nOf (bits E (powT K q))
        + 2 ^ (Tester.nOf (bits E (powT K q)) * Tester.nOf (bits E (powT K q)))))

/-- **The positions of a round's proof, counted.** -/
theorem card_pos_step (q : ℕ) (hq : 0 < q) (G : ConstraintGraph DinurAlpha) :
    Fintype.card (((G.preprocess E).killedPow q (powT K q) hq).Pos
        (B := bits E (powT K q)))
      = posFactor E q * G.numEdges := by
  have horder : ((G.preprocess E).killedPow q (powT K q) hq).graph.order = 2 * G.numEdges := by
    rw [RegCSP.graph_killedPow, RegGraph.order_killedPower, G.order_preprocess]
  have hdeg : ((G.preprocess E).killedPow q (powT K q) hq).graph.deg
      = powDeg E ^ powT K q * q ^ powT K q := by
    rw [RegCSP.graph_killedPow, RegGraph.deg_killedPower, G.deg_preprocess, powDeg]
  rw [RegCSP.card_pos_compose, horder, hdeg, posFactor]
  ring

/-- **A round multiplies the vertex count by a constant.** -/
theorem numVerts_step (q : ℕ) (hq : 0 < q) (G : ConstraintGraph DinurAlpha) :
    (step E q hq G).numVerts = vertFactor E q * G.numEdges := by
  have horder : ((G.preprocess E).killedPow q (powT K q) hq).graph.order = 2 * G.numEdges := by
    rw [RegCSP.graph_killedPow, RegGraph.order_killedPower, G.order_preprocess]
  have hdeg : ((G.preprocess E).killedPow q (powT K q) hq).graph.deg
      = powDeg E ^ powT K q * q ^ powT K q := by
    rw [RegCSP.graph_killedPow, RegGraph.deg_killedPower, G.deg_preprocess, powDeg]
  have hdart : Fintype.card ((G.preprocess E).killedPow q (powT K q) hq).Dart
      = 2 * G.numEdges * (powDeg E ^ powT K q * q ^ powT K q) := by
    rw [RegCSP.card_dart, horder, hdeg]
  have hR : (RegCSP.compose (enc E G (powT K q))
      ((G.preprocess E).killedPow q (powT K q) hq)).R
      = Tester.ROf (bits E (powT K q)) := rfl
  rw [step, MultiTest.numVerts_toGraph, RegCSP.card_pos_compose, horder, hdeg, hdart, hR,
    vertFactor]
  ring

end Dinur

end Complexity
