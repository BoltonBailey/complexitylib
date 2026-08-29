/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.Union
public import Complexitylib.Classes.PCP.Internal.NumEnc

/-!
# Expander families, and expanderizing a graph

Dinur's preprocessing needs a *fixed* constant degree `d` and a constant
`lam < 1` such that every vertex count admits a `d`-regular graph with spectral
bound `lam`. `ExpanderFamily` packages exactly that.

The family is given as **raw rotation data** on `Fin n × Fin degree`, one
involution per vertex count, rather than as a function into `RegGraph`. That
matters downstream: degree reduction puts an expander on the cloud of *every*
vertex at once, and those clouds have different sizes, so all of them must speak
the same label type `Fin degree`. Deriving the graphs from shared data gives
that for free, and makes `order` and `deg` computations `Fintype.card_fin`
rather than hypotheses.

Isolating the requirement this way matters for a second reason: nothing else in
the development depends on *how* the family is built. Neither Mathlib nor this
library currently contains an explicit expander construction — no spectral gap,
edge expansion, Cheeger inequality, or zig-zag product — so producing an
`ExpanderFamily` is a self-contained sub-project (zig-zag, or a Margulis-type
Cayley construction), and everything downstream is already stated against this
interface.

## Main definitions

- `RegGraph.ofRot` — a graph on `Fin n` from a rotation involution
- `ExpanderFamily` — constant degree, uniform spectral bound, shared label type
- `ExpanderFamily.graph`, `ExpanderFamily.expanderize`

## Main results

- `ExpanderFamily.order_graph`, `ExpanderFamily.deg_graph`
- `ExpanderFamily.spectralBound_expanderize` — expanderization has a bound
- `ExpanderFamily.expanderize_bound_lt_one` — and the bound is below one
-/

@[expose] public section

namespace Complexity

namespace RegGraph

/-- The graph on `Fin n` with labels `Fin d` given by a rotation involution. -/
def ofRot (d : ℕ) (hd : 0 < d) (n : ℕ) (rot : Fin n × Fin d → Fin n × Fin d)
    (hrot : Function.Involutive rot) : RegGraph where
  V := Fin n
  D := Fin d
  decEqV := inferInstance
  decEqD := inferInstance
  fintypeV := inferInstance
  fintypeD := inferInstance
  nonemptyD := ⟨⟨0, hd⟩⟩
  rot := rot
  rot_involutive := hrot

@[simp] theorem order_ofRot (d : ℕ) (hd : 0 < d) (n : ℕ)
    (rot : Fin n × Fin d → Fin n × Fin d) (hrot : Function.Involutive rot) :
    (ofRot d hd n rot hrot).order = n := Fintype.card_fin n

@[simp] theorem deg_ofRot (d : ℕ) (hd : 0 < d) (n : ℕ)
    (rot : Fin n × Fin d → Fin n × Fin d) (hrot : Function.Involutive rot) :
    (ofRot d hd n rot hrot).deg = d := Fintype.card_fin d

end RegGraph

/-- A family of constant-degree expanders, presented as rotation data: for every
vertex count `n`, an involution on `Fin n × Fin degree` whose graph contracts
mean-zero functions by a fixed `lam < 1`. -/
structure ExpanderFamily where
  /-- The constant degree, shared by every member. -/
  degree : ℕ
  /-- The degree is positive. -/
  degree_pos : 0 < degree
  /-- The rotation map on `n` vertices. -/
  rot : ∀ n : ℕ, Fin n × Fin degree → Fin n × Fin degree
  /-- Each rotation map is an involution. -/
  rot_involutive : ∀ n, Function.Involutive (rot n)
  /-- The uniform contraction factor. -/
  lam : ℝ
  /-- The factor is nonnegative. -/
  lam_nonneg : 0 ≤ lam
  /-- The factor is below one: this is the spectral gap. -/
  lam_lt_one : lam < 1
  /-- Every member contracts mean-zero functions by `lam`. -/
  spectral : ∀ n : ℕ,
    (RegGraph.ofRot degree degree_pos n (rot n) (rot_involutive n)).SpectralBound lam

namespace ExpanderFamily

variable (E : ExpanderFamily) (G : RegGraph) [NumEnc G.V]

/-- The member of the family on `n` vertices. -/
def graph (n : ℕ) : RegGraph :=
  RegGraph.ofRot E.degree E.degree_pos n (E.rot n) (E.rot_involutive n)

@[simp] theorem V_graph (n : ℕ) : (E.graph n).V = Fin n := rfl

@[simp] theorem D_graph (n : ℕ) : (E.graph n).D = Fin E.degree := rfl

@[simp] theorem order_graph (n : ℕ) : (E.graph n).order = n := Fintype.card_fin n

@[simp] theorem deg_graph (n : ℕ) : (E.graph n).deg = E.degree := Fintype.card_fin E.degree

theorem spectral_graph (n : ℕ) : (E.graph n).SpectralBound E.lam := E.spectral n

/-- The identification of the family member's vertices with `G`'s: the
numbering `G`'s vertices carry. -/
noncomputable def vertexEquiv : (E.graph G.order).V ≃ G.V :=
  (NumEnc.equivFinCard G.V).symm

/-- `G` with a family expander superposed on its vertices. -/
noncomputable def expanderize : RegGraph :=
  RegGraph.union G (E.graph G.order) (E.vertexEquiv G)

@[simp] theorem order_expanderize : (E.expanderize G).order = G.order := rfl

@[simp] theorem deg_expanderize : (E.expanderize G).deg = G.deg + E.degree := by
  rw [expanderize, RegGraph.deg_union, deg_graph]

/-- **Expanderization.** Superposing a family expander gives a graph with a
spectral bound. -/
theorem spectralBound_expanderize :
    (E.expanderize G).SpectralBound
      (((G.deg : ℝ) + (E.degree : ℝ) * E.lam) / ((G.deg : ℝ) + (E.degree : ℝ))) := by
  have h := RegGraph.spectralBound_union G (E.graph G.order) (E.vertexEquiv G)
    E.lam_nonneg (E.spectral_graph G.order)
  rw [deg_graph] at h
  exact h

omit [NumEnc G.V] in
/-- The resulting bound is strictly below one, which is what makes powering gain
a factor. -/
theorem expanderize_bound_lt_one :
    ((G.deg : ℝ) + (E.degree : ℝ) * E.lam) / ((G.deg : ℝ) + (E.degree : ℝ)) < 1 := by
  have hdG : (0 : ℝ) < (G.deg : ℝ) := by have := G.deg_pos; positivity
  have hdE : (0 : ℝ) < (E.degree : ℝ) := by exact_mod_cast E.degree_pos
  rw [div_lt_one (by positivity)]
  nlinarith [E.lam_lt_one, E.lam_nonneg]

end ExpanderFamily

end Complexity
