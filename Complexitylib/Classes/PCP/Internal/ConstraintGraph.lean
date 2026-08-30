/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp

/-!
# Constraint graphs and their unsatisfiability value

The combinatorial core of Dinur's proof of the PCP theorem. A *constraint
graph* over an alphabet `α` is a finite multigraph whose edges each carry a
binary constraint on the labels of their endpoints; an *assignment* labels the
vertices, and the *unsatisfiability value* `unsatVal` is the least fraction of
edges any assignment leaves unsatisfied.

Dinur's amplification step is a transformation of constraint graphs that
preserves satisfiability (`unsatVal = 0`) while doubling `unsatVal` otherwise,
so all of that argument is phrased in terms of the definitions here.

## Design

- Vertices are `Fin numVerts` and edges are *indexed* by `Fin numEdges`, so
  parallel edges and self-loops are allowed. Both are essential: powering a
  constraint graph produces many parallel walk-edges, and the degree-reduction
  and expanderization steps add edges to a graph that may already have them.
- Edges are directed (`tail`/`head`) and constraints are `Bool`-valued
  functions of the two endpoint labels, which keeps everything decidable and
  computable. Undirected graphs are modelled by including both orientations,
  which the analysis of random walks will require explicitly rather than
  implicitly.
- `unsatFrac` divides by `numEdges`, so an edgeless graph gets value `0` by
  Lean's `x / 0 = 0` convention. Every lemma below is stated so that this is
  the mathematically correct answer.

## Main definitions

- `ConstraintGraph`, `ConstraintGraph.Assignment`, `ConstraintGraph.Satisfies`
- `ConstraintGraph.unsatFrac` — the fraction of edges an assignment fails
- `ConstraintGraph.unsatVal` — the minimum of `unsatFrac` over all assignments
- `ConstraintGraph.Satisfiable`

## Main results

- `unsatFrac_eq_zero_iff` — an assignment wastes no edges exactly when it
  satisfies them all
- `exists_assignment_unsatFrac_eq_unsatVal` — the minimum is attained
- `unsatVal_eq_zero_iff_satisfiable` — the gap-`0` case is satisfiability
- `unsatVal_nonneg`, `unsatVal_le_one`
-/

@[expose] public section

namespace Complexity

/-- A constraint graph over the alphabet `α`: a finite multigraph on the
vertices `Fin numVerts`, with edges indexed by `Fin numEdges`, each edge
carrying a binary constraint on the labels of its endpoints. -/
structure ConstraintGraph (α : Type) where
  /-- The number of vertices; the vertices are `Fin numVerts`. -/
  numVerts : ℕ
  /-- The number of edges; the edges are indexed by `Fin numEdges`, so parallel
  edges and self-loops are allowed. -/
  numEdges : ℕ
  /-- The source of an edge. -/
  tail : Fin numEdges → Fin numVerts
  /-- The target of an edge. -/
  head : Fin numEdges → Fin numVerts
  /-- The constraint carried by an edge, as a predicate on the labels of its
  tail and its head, in that order. -/
  rel : Fin numEdges → α → α → Bool

namespace ConstraintGraph

variable {α : Type} {G : ConstraintGraph α}

/-- An assignment labels every vertex with a symbol of the alphabet. -/
abbrev Assignment (G : ConstraintGraph α) : Type := Fin G.numVerts → α

/-- Whether the assignment `a` satisfies the edge `e`, as a `Bool`. -/
def satisfies (G : ConstraintGraph α) (a : G.Assignment) (e : Fin G.numEdges) : Bool :=
  G.rel e (a (G.tail e)) (a (G.head e))

/-- The assignment `a` satisfies the edge `e`. -/
def Satisfies (G : ConstraintGraph α) (a : G.Assignment) (e : Fin G.numEdges) : Prop :=
  G.satisfies a e = true

instance (G : ConstraintGraph α) (a : G.Assignment) (e : Fin G.numEdges) :
    Decidable (G.Satisfies a e) :=
  inferInstanceAs (Decidable (G.satisfies a e = true))

theorem satisfies_iff {a : G.Assignment} {e : Fin G.numEdges} :
    G.Satisfies a e ↔ G.rel e (a (G.tail e)) (a (G.head e)) = true := Iff.rfl

/-- The edges left unsatisfied by `a`. -/
def unsatEdges (G : ConstraintGraph α) (a : G.Assignment) : Finset (Fin G.numEdges) :=
  Finset.univ.filter fun e => ¬ G.Satisfies a e

@[simp] theorem mem_unsatEdges {a : G.Assignment} {e : Fin G.numEdges} :
    e ∈ G.unsatEdges a ↔ ¬ G.Satisfies a e := by
  simp [unsatEdges]

/-- The fraction of edges that `a` leaves unsatisfied. An edgeless graph has
value `0`. -/
def unsatFrac (G : ConstraintGraph α) (a : G.Assignment) : ℚ :=
  ((G.unsatEdges a).card : ℚ) / (G.numEdges : ℚ)

theorem unsatFrac_nonneg (a : G.Assignment) : 0 ≤ G.unsatFrac a := by
  unfold unsatFrac; positivity

theorem card_unsatEdges_le (a : G.Assignment) : (G.unsatEdges a).card ≤ G.numEdges := by
  simpa using Finset.card_le_univ (G.unsatEdges a)

theorem unsatFrac_le_one (a : G.Assignment) : G.unsatFrac a ≤ 1 := by
  rcases Nat.eq_zero_or_pos G.numEdges with h | h
  · simp [unsatFrac, h]
  · have hpos : (0 : ℚ) < (G.numEdges : ℚ) := by exact_mod_cast h
    rw [unsatFrac, div_le_one hpos]
    exact_mod_cast card_unsatEdges_le a

/-- An assignment wastes no edges exactly when it satisfies every edge. This
holds for the edgeless graph too, where both sides are trivially true. -/
theorem unsatFrac_eq_zero_iff {a : G.Assignment} :
    G.unsatFrac a = 0 ↔ ∀ e, G.Satisfies a e := by
  constructor
  · intro h e
    by_contra he
    have hne : (G.unsatEdges a).Nonempty := ⟨e, by simpa using he⟩
    have hcard : 0 < (G.unsatEdges a).card := Finset.card_pos.mpr hne
    have hm : 0 < G.numEdges := lt_of_lt_of_le hcard (card_unsatEdges_le a)
    have hmq : (0 : ℚ) < (G.numEdges : ℚ) := by exact_mod_cast hm
    have hcq : (0 : ℚ) < ((G.unsatEdges a).card : ℚ) := by exact_mod_cast hcard
    rw [unsatFrac, div_eq_zero_iff] at h
    rcases h with h | h
    · exact absurd h (ne_of_gt hcq)
    · exact absurd h (ne_of_gt hmq)
  · intro h
    have : G.unsatEdges a = ∅ := by
      ext e; simpa using h e
    simp [unsatFrac, this]

/-- A constraint graph is satisfiable when some assignment satisfies every
edge. -/
def Satisfiable (G : ConstraintGraph α) : Prop := ∃ a : G.Assignment, ∀ e, G.Satisfies a e

section Value

variable [Fintype α] [Nonempty α]

/-- The unsatisfiability value: the least fraction of edges any assignment
leaves unsatisfied. -/
noncomputable def unsatVal (G : ConstraintGraph α) : ℚ :=
  (Finset.univ : Finset G.Assignment).inf' Finset.univ_nonempty G.unsatFrac

theorem unsatVal_le (a : G.Assignment) : G.unsatVal ≤ G.unsatFrac a :=
  Finset.inf'_le _ (Finset.mem_univ a)

theorem le_unsatVal {c : ℚ} (h : ∀ a : G.Assignment, c ≤ G.unsatFrac a) : c ≤ G.unsatVal :=
  Finset.le_inf' _ _ fun a _ => h a

/-- The minimum defining `unsatVal` is attained. -/
theorem exists_assignment_unsatFrac_eq_unsatVal (G : ConstraintGraph α) :
    ∃ a : G.Assignment, G.unsatFrac a = G.unsatVal := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty) G.unsatFrac
  exact ⟨a, ha.symm⟩

theorem unsatVal_nonneg (G : ConstraintGraph α) : 0 ≤ G.unsatVal :=
  le_unsatVal fun a => unsatFrac_nonneg a

theorem unsatVal_le_one (G : ConstraintGraph α) : G.unsatVal ≤ 1 := by
  obtain ⟨a, ha⟩ := G.exists_assignment_unsatFrac_eq_unsatVal
  exact ha ▸ unsatFrac_le_one a

/-- The zero-gap case is exactly satisfiability. -/
theorem unsatVal_eq_zero_iff_satisfiable (G : ConstraintGraph α) :
    G.unsatVal = 0 ↔ G.Satisfiable := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := G.exists_assignment_unsatFrac_eq_unsatVal
    exact ⟨a, unsatFrac_eq_zero_iff.mp (ha.trans h)⟩
  · rintro ⟨a, ha⟩
    have h0 : G.unsatFrac a = 0 := unsatFrac_eq_zero_iff.mpr ha
    exact le_antisymm (h0 ▸ unsatVal_le a) G.unsatVal_nonneg

omit [Fintype α] in
/-- An unsatisfiable graph has an edge, since otherwise any labelling works. -/
theorem numEdges_pos_of_not_satisfiable (h : ¬ G.Satisfiable) : 0 < G.numEdges := by
  rcases Nat.eq_zero_or_pos G.numEdges with h0 | h0
  · exact absurd ⟨(fun _ => Classical.arbitrary α : G.Assignment), fun e => absurd e.isLt
      (by simp [h0])⟩ h
  · exact h0

omit [Fintype α] in
/-- On an unsatisfiable graph every assignment fails at least one edge, so its
value is at least one edge's worth. -/
theorem inv_numEdges_le_unsatFrac (h : ¬ G.Satisfiable) (a : G.Assignment) :
    1 / (G.numEdges : ℚ) ≤ G.unsatFrac a := by
  have hpos : 0 < G.numEdges := numEdges_pos_of_not_satisfiable h
  have hne : (G.unsatEdges a).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    refine h ⟨a, fun e => ?_⟩
    by_contra he
    simpa [hcon] using (mem_unsatEdges (a := a) (e := e)).mpr he
  have hcard : (1 : ℚ) ≤ ((G.unsatEdges a).card : ℚ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  rw [unsatFrac]
  gcongr

theorem inv_numEdges_le_unsatVal (h : ¬ G.Satisfiable) :
    1 / (G.numEdges : ℚ) ≤ G.unsatVal :=
  le_unsatVal fun a => inv_numEdges_le_unsatFrac h a

theorem unsatVal_pos_of_not_satisfiable (h : ¬ G.Satisfiable) : 0 < G.unsatVal := by
  refine lt_of_lt_of_le ?_ (inv_numEdges_le_unsatVal h)
  have : (0 : ℚ) < (G.numEdges : ℚ) := by
    exact_mod_cast numEdges_pos_of_not_satisfiable h
  positivity

/-- A positive value certifies unsatisfiability. -/
theorem not_satisfiable_of_unsatVal_pos {G : ConstraintGraph α} (h : 0 < G.unsatVal) :
    ¬ G.Satisfiable := fun hs => absurd ((unsatVal_eq_zero_iff_satisfiable G).mpr hs) (ne_of_gt h)

end Value

end ConstraintGraph

end Complexity
