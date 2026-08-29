/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.RegularGraph

/-!
# Padding a regular graph with fresh vertices

`SizedExpander` supplies an expander of approximately, not exactly, a requested
size, so the graph it is to be superposed on must first be brought up to the
expander's size. A regular graph cannot simply gain isolated vertices — that
would break regularity — so the fresh vertices carry self-loops instead, one per
label.

The padded graph is disconnected and so has no spectral gap of its own; that is
of no concern, because expanderization takes the gap from the expander it
superposes, not from the graph underneath.

## Main definitions

- `Complexity.RegGraph.padVerts` — the graph on a prescribed larger vertex set

## Main results

- `Complexity.RegGraph.order_padVerts`, `Complexity.RegGraph.deg_padVerts`
-/

@[expose] public section

namespace Complexity

namespace RegGraph

variable (G : RegGraph)

/-- The rotation map of the padded graph: the old darts as before, and a
self-loop at each fresh vertex. -/
def padRot (k : ℕ) : (G.V ⊕ Fin k) × G.D → (G.V ⊕ Fin k) × G.D
  | (Sum.inl v, i) => (Sum.inl (G.rot (v, i)).1, (G.rot (v, i)).2)
  | (Sum.inr j, i) => (Sum.inr j, i)

theorem padRot_involutive (k : ℕ) : Function.Involutive (G.padRot k) := by
  intro p
  obtain ⟨v | j, i⟩ := p
  · show G.padRot k (Sum.inl (G.rot (v, i)).1, (G.rot (v, i)).2) = _
    rw [padRot]
    have h := G.rot_involutive (v, i)
    simp only [Prod.mk.injEq]
    constructor
    · exact congrArg (fun p => Sum.inl p.1) h
    · exact congrArg (fun p => p.2) h
  · rfl

/-- **The graph with `k` fresh looped vertices added.** -/
def padVerts (k : ℕ) : RegGraph where
  V := G.V ⊕ Fin k
  D := G.D
  decEqV := by
    haveI := G.decEqV
    exact inferInstance
  decEqD := G.decEqD
  fintypeV := by
    haveI := G.fintypeV
    exact inferInstance
  fintypeD := G.fintypeD
  nonemptyD := G.nonemptyD
  rot := G.padRot k
  rot_involutive := G.padRot_involutive k

@[simp] theorem deg_padVerts (k : ℕ) : (G.padVerts k).deg = G.deg := rfl

@[simp] theorem order_padVerts (k : ℕ) : (G.padVerts k).order = G.order + k := by
  show Fintype.card (G.V ⊕ Fin k) = Fintype.card G.V + k
  rw [Fintype.card_sum, Fintype.card_fin]

/-- Padding to a prescribed size. -/
def padTo (N : ℕ) : RegGraph := G.padVerts (N - G.order)

@[simp] theorem deg_padTo (N : ℕ) : (G.padTo N).deg = G.deg := rfl

theorem order_padTo {N : ℕ} (h : G.order ≤ N) : (G.padTo N).order = N := by
  rw [padTo, order_padVerts]
  omega

end RegGraph

end Complexity
