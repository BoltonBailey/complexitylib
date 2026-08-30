/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.RegularGraph
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic.Positivity

/-!
# Constraint graphs on a regular graph

Dinur's argument runs on constraint graphs whose underlying multigraph is
`d`-regular, because that is what makes random walks and the spectral gap
available. This module puts the two halves together: a `RegCSP` is a `RegGraph`
together with a constraint attached to each **dart**, symmetric under reversal,
so that it is really one constraint per undirected edge.

The measure on constraints is the uniform measure on **darts**: `unsatFrac`
divides the number of unsatisfied darts by `order * deg`. Constraints are
attached to darts rather than to undirected edges, and are *not* required to
agree with their reverse. Nothing is lost: the random walk traverses darts, so
the dart measure is the one every estimate is stated in, and the eventual
verifier samples a dart and checks one constraint. Requiring symmetry instead
would force each construction — powering above all — to prove that reversing a
walk and swapping the two opinions leaves its constraint unchanged, an
index-reversal argument of no mathematical content.

Two presentations of a constraint system coexist in this development, on
purpose. `ConstraintGraph` has its vertex and edge counts as *numeric fields*,
so it is a single type that a transformation can be iterated on (see
`Amplifier`) and that a bitstring encoding can address; `RegCSP` carries
structured vertex and dart types, which is what Dinur's constructions produce.
The bijective bridge between them belongs to the final encoded reduction and is
built there.

## Main definitions

- `RegCSP`, `RegCSP.Dart`, `RegCSP.Assignment`, `RegCSP.satisfies`,
  `RegCSP.Satisfies`, `RegCSP.Satisfiable`, `RegCSP.unsatDarts`
- `RegCSP.unsatFrac`, `RegCSP.unsatVal` — the fraction of darts an assignment
  fails, and its minimum over assignments

## Main results

- `RegCSP.unsatFrac_eq_zero_iff`, `RegCSP.unsatVal_eq_zero_iff_satisfiable` —
  value zero is satisfiability
- `RegCSP.unsatVal_nonneg`, `RegCSP.unsatVal_le_one`
-/

@[expose] public section

namespace Complexity

/-- A constraint system on a regular multigraph: one constraint per **dart**. -/
structure RegCSP (α : Type) where
  /-- The underlying regular multigraph. -/
  graph : RegGraph
  /-- The constraint on the dart `(v, i)`, as a predicate on the label of `v`
  and the label of its `i`-th neighbour, in that order. -/
  rel : graph.V → graph.D → α → α → Bool

namespace RegCSP

variable {α : Type} (R : RegCSP α)

/-- A dart: a vertex together with one of its `d` outgoing edge labels. -/
abbrev Dart (R : RegCSP α) : Type := R.graph.V × R.graph.D

/-- An assignment labels every vertex with a symbol of the alphabet. -/
abbrev Assignment (R : RegCSP α) : Type := R.graph.V → α

/-- Whether the dart `p`'s constraint holds under `a`, as a `Bool`. -/
def satisfies (a : R.Assignment) (p : R.Dart) : Bool :=
  R.rel p.1 p.2 (a p.1) (a (R.graph.nbr p.1 p.2))

/-- The dart `p`'s constraint holds under `a`. -/
def Satisfies (a : R.Assignment) (p : R.Dart) : Prop := R.satisfies a p = true

instance (a : R.Assignment) (p : R.Dart) : Decidable (R.Satisfies a p) :=
  inferInstanceAs (Decidable (R.satisfies a p = true))

/-- The darts left unsatisfied by `a`. -/
def unsatDarts (a : R.Assignment) : Finset R.Dart :=
  Finset.univ.filter fun p => ¬ R.Satisfies a p

@[simp] theorem mem_unsatDarts {a : R.Assignment} {p : R.Dart} :
    p ∈ R.unsatDarts a ↔ ¬ R.Satisfies a p := by
  simp [unsatDarts]

/-- Some assignment satisfies every dart. -/
def Satisfiable : Prop := ∃ a : R.Assignment, ∀ p, R.Satisfies a p

/-- The number of darts. -/
theorem card_dart : Fintype.card R.Dart = R.graph.order * R.graph.deg := by
  simp

theorem card_unsatDarts_le (a : R.Assignment) :
    (R.unsatDarts a).card ≤ R.graph.order * R.graph.deg := by
  have h := Finset.card_le_univ (R.unsatDarts a)
  rwa [card_dart] at h

/-- The fraction of darts an assignment leaves unsatisfied. -/
def unsatFrac (a : R.Assignment) : ℚ :=
  ((R.unsatDarts a).card : ℚ) / ((R.graph.order * R.graph.deg : ℕ) : ℚ)

theorem unsatFrac_nonneg (a : R.Assignment) : 0 ≤ R.unsatFrac a := by
  unfold unsatFrac; positivity

theorem unsatFrac_le_one (a : R.Assignment) : R.unsatFrac a ≤ 1 := by
  rcases Nat.eq_zero_or_pos (R.graph.order * R.graph.deg) with h | h
  · simp [unsatFrac, h]
  · have hpos : (0 : ℚ) < ((R.graph.order * R.graph.deg : ℕ) : ℚ) := by exact_mod_cast h
    rw [unsatFrac, div_le_one hpos]
    exact_mod_cast R.card_unsatDarts_le a

/-- An assignment wastes no darts exactly when it satisfies them all. -/
theorem unsatFrac_eq_zero_iff {a : R.Assignment} :
    R.unsatFrac a = 0 ↔ ∀ p, R.Satisfies a p := by
  constructor
  · intro h p
    by_contra hp
    have hne : (R.unsatDarts a).Nonempty := ⟨p, by simpa using hp⟩
    have hcard : 0 < (R.unsatDarts a).card := Finset.card_pos.mpr hne
    have hm : 0 < R.graph.order * R.graph.deg := lt_of_lt_of_le hcard (R.card_unsatDarts_le a)
    have hmq : (0 : ℚ) < ((R.graph.order * R.graph.deg : ℕ) : ℚ) := by exact_mod_cast hm
    have hcq : (0 : ℚ) < ((R.unsatDarts a).card : ℚ) := by exact_mod_cast hcard
    rw [unsatFrac, div_eq_zero_iff] at h
    rcases h with h | h
    · exact absurd h (ne_of_gt hcq)
    · exact absurd h (ne_of_gt hmq)
  · intro h
    have hempty : R.unsatDarts a = ∅ := by
      ext p; simpa using h p
    simp [unsatFrac, hempty]

section Value

variable [Fintype α] [Nonempty α]

/-- The least fraction of darts any assignment leaves unsatisfied. -/
noncomputable def unsatVal : ℚ :=
  (Finset.univ : Finset R.Assignment).inf' Finset.univ_nonempty R.unsatFrac

theorem unsatVal_le (a : R.Assignment) : R.unsatVal ≤ R.unsatFrac a :=
  Finset.inf'_le _ (Finset.mem_univ a)

theorem le_unsatVal {c : ℚ} (h : ∀ a : R.Assignment, c ≤ R.unsatFrac a) : c ≤ R.unsatVal :=
  Finset.le_inf' _ _ fun a _ => h a

theorem exists_assignment_unsatFrac_eq_unsatVal :
    ∃ a : R.Assignment, R.unsatFrac a = R.unsatVal := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty) R.unsatFrac
  exact ⟨a, ha.symm⟩

theorem unsatVal_nonneg : 0 ≤ R.unsatVal := R.le_unsatVal fun a => R.unsatFrac_nonneg a

theorem unsatVal_le_one : R.unsatVal ≤ 1 := by
  obtain ⟨a, ha⟩ := R.exists_assignment_unsatFrac_eq_unsatVal
  exact ha ▸ R.unsatFrac_le_one a

theorem unsatVal_eq_zero_iff_satisfiable : R.unsatVal = 0 ↔ R.Satisfiable := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := R.exists_assignment_unsatFrac_eq_unsatVal
    exact ⟨a, R.unsatFrac_eq_zero_iff.mp (ha.trans h)⟩
  · rintro ⟨a, ha⟩
    have h0 : R.unsatFrac a = 0 := R.unsatFrac_eq_zero_iff.mpr ha
    exact le_antisymm (h0 ▸ R.unsatVal_le a) R.unsatVal_nonneg

end Value

end RegCSP

end Complexity
