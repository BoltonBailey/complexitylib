/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.SizedExpander
public import Complexitylib.Classes.PCP.Internal.PadCSP
public import Complexitylib.Classes.PCP.Internal.ExpanderizeCSP

/-!
# Expanderizing with an approximately sized family

`ExpanderizeCSP` superposes an expander on a constraint system, which asks for
one on exactly the system's vertex count. The zig-zag tower offers only
approximate sizes, so the system is first enlarged to meet the expander:
`PadCSP` shows the enlargement costs only the ratio of the two vertex counts,
and that ratio is bounded by the family's `factor`.

## Main definitions

- `Complexity.RegCSP.sizedExpanderize` — pad, then superpose

## Main results

- `Complexity.RegCSP.spectralBound_sizedExpanderize` — it has a spectral gap
- `Complexity.RegCSP.satisfiable_sizedExpanderize_iff` — completeness
- `Complexity.RegCSP.unsatVal_sizedExpanderize_ge` — soundness, with the two
  constant losses made explicit
-/

@[expose] public section

namespace Complexity

namespace RegCSP

variable {α : Type} (R : RegCSP α) (F : SizedExpanderFamily)

/-- The size the family offers for this system. -/
def fitSize : ℕ := (F.graph R.graph.order).order

theorem le_fitSize : R.graph.order ≤ R.fitSize F := F.order_ge _

/-- The system, enlarged to the size the family offers. -/
def padded : RegCSP α := R.padVerts (R.fitSize F - R.graph.order)

theorem order_padded : (R.padded F).graph.order = R.fitSize F := by
  rw [padded, graph_padVerts, RegGraph.order_padVerts]
  have := R.le_fitSize F
  omega

@[simp] theorem deg_padded : (R.padded F).graph.deg = R.graph.deg := rfl

/-- The family member's vertices name the enlarged system's. -/
noncomputable def fitEquiv : (F.graph R.graph.order).V ≃ (R.padded F).graph.V :=
  Fintype.equivOfCardEq (by
    show (F.graph R.graph.order).order = (R.padded F).graph.order
    rw [order_padded]
    rfl)

/-- **Expanderization against an approximately sized family.** -/
noncomputable def sizedExpanderize : RegCSP α :=
  (R.padded F).addTrivial (F.graph R.graph.order) (R.fitEquiv F)

@[simp] theorem deg_sizedExpanderize :
    (R.sizedExpanderize F).graph.deg = R.graph.deg + F.degree := by
  rw [sizedExpanderize, graph_addTrivial, RegGraph.deg_union, deg_padded, F.deg_graph]

/-- **The expanderized system has a spectral gap.** -/
theorem spectralBound_sizedExpanderize :
    (R.sizedExpanderize F).graph.SpectralBound
      (((R.graph.deg : ℝ) + (F.degree : ℝ) * F.lam)
        / ((R.graph.deg : ℝ) + (F.degree : ℝ))) := by
  have h := RegGraph.spectralBound_union (R.padded F).graph (F.graph R.graph.order)
    (R.fitEquiv F) F.lam_nonneg (F.spectral R.graph.order)
  rw [F.deg_graph] at h
  exact h

/-- The bound is below one, which is what powering needs. -/
theorem sizedExpanderize_bound_lt_one :
    ((R.graph.deg : ℝ) + (F.degree : ℝ) * F.lam)
      / ((R.graph.deg : ℝ) + (F.degree : ℝ)) < 1 := by
  have hdF : (0 : ℝ) < (F.degree : ℝ) := by exact_mod_cast F.degree_pos
  rw [div_lt_one (by positivity)]
  nlinarith [F.lam_lt_one, F.lam_nonneg]

/-- **Completeness**: enlarging and superposing preserves satisfiability. -/
theorem satisfiable_sizedExpanderize_iff [Nonempty α] :
    (R.sizedExpanderize F).Satisfiable ↔ R.Satisfiable := by
  rw [sizedExpanderize, satisfiable_addTrivial_iff, padded, satisfiable_padVerts_iff]

/-- **Soundness**: the value survives, down to the two constant factors — the
dilution from enlarging, and the dilution from the superposed degree. -/
theorem unsatVal_sizedExpanderize_ge [Fintype α] [Nonempty α] [DecidableEq α]
    (hord : 0 < R.graph.order) :
    R.unsatVal * ((R.graph.order : ℕ) : ℚ) / ((R.fitSize F : ℕ) : ℚ)
        * (R.graph.deg : ℚ) / ((R.graph.deg : ℚ) + (F.degree : ℚ))
      ≤ (R.sizedExpanderize F).unsatVal := by
  have hk : R.graph.order + (R.fitSize F - R.graph.order) = R.fitSize F := by
    have := R.le_fitSize F
    omega
  have hge := R.unsatVal_padVerts_ge (R.fitSize F - R.graph.order) hord
  rw [hk] at hge
  have hde : (0 : ℚ) < (R.graph.deg : ℚ) + (F.degree : ℚ) := by
    have h1 : (0 : ℚ) < (R.graph.deg : ℚ) := by
      have := R.graph.deg_pos
      exact_mod_cast this
    linarith
  have hd : (0 : ℚ) ≤ (R.graph.deg : ℚ) := by positivity
  rw [sizedExpanderize, unsatVal_addTrivial, deg_padded, F.deg_graph]
  rw [div_le_div_iff_of_pos_right hde]
  exact mul_le_mul_of_nonneg_right hge hd

end RegCSP

end Complexity
