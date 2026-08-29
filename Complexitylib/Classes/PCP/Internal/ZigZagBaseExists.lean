/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.SizedExpander
public import Complexitylib.Classes.PCP.Internal.ExpanderExists

/-!
# A base graph for the tower exists

The zig-zag tower is seeded by a single finite graph whose vertices number the
fourth power of its degree and whose spectral bound is a fifth. Such a graph is
what Reingold, Vadhan and Wigderson find by exhaustive search; here it comes
from any expander family at all, by raising one member to a power.

Powering leaves the vertex set alone and raises both the degree and the bound
to the same power, so taking the member on `degree ^ (4 * m)` vertices and
powering it `m` times gives `degree ^ (4 * m) = (degree ^ m) ^ 4` vertices
against degree `degree ^ m` — and `lam ^ m ≤ 1 / 5` once `m` is large enough.

Applied to `randExpander`, this shows a `ZigZagBase` exists.

## Main definitions

- `Complexity.ExpanderFamily.fifthExp` — a power taking the bound below a fifth
- `Complexity.ExpanderFamily.toZigZagBase` — the base graph

## Main results

- `Complexity.nonempty_zigZagBase` — a base graph exists
- `Complexity.nonempty_sizedExpanderFamily` — so the tower's size-flexible
  family exists too
-/

@[expose] public section

namespace Complexity

namespace ExpanderFamily

variable (E : ExpanderFamily)

theorem exists_pow_le_fifth : ∃ m : ℕ, E.lam ^ m ≤ 1 / 5 := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / 5 by norm_num) E.lam_lt_one
  exact ⟨m, hm.le⟩

/-- A power taking the family's bound to at most a fifth. -/
noncomputable def fifthExp : ℕ := Classical.choose E.exists_pow_le_fifth

theorem pow_fifthExp_le : E.lam ^ E.fifthExp ≤ 1 / 5 :=
  Classical.choose_spec E.exists_pow_le_fifth

/-- The size at which the powered member has as many vertices as the fourth
power of its degree. -/
noncomputable def baseOrder : ℕ := E.degree ^ (4 * E.fifthExp)

/-- **A base for the zig-zag tower.** -/
noncomputable def toZigZagBase : ZigZagBase where
  base := (E.graph E.baseOrder).power E.fifthExp
  card_eq := by
    have hV : Fintype.card ((E.graph E.baseOrder).power E.fifthExp).V = E.baseOrder :=
      Fintype.card_fin _
    rw [hV, RegGraph.deg_power, deg_graph, baseOrder, ← pow_mul, Nat.mul_comm]
  lam := E.lam ^ E.fifthExp
  lam_nonneg := pow_nonneg E.lam_nonneg _
  lam_le := E.pow_fifthExp_le
  spectral := RegGraph.spectralBound_power _ (E.spectral_graph _) _

theorem one_le_fifthExp : 1 ≤ E.fifthExp := by
  by_contra h
  have h0 : E.fifthExp = 0 := by omega
  have := E.pow_fifthExp_le
  rw [h0, pow_zero] at this
  norm_num at this

@[simp] theorem deg_toZigZagBase : E.toZigZagBase.base.deg = E.degree ^ E.fifthExp := by
  show ((E.graph E.baseOrder).power E.fifthExp).deg = _
  rw [RegGraph.deg_power, deg_graph]

theorem one_lt_deg_toZigZagBase (h : 1 < E.degree) : 1 < E.toZigZagBase.base.deg := by
  rw [deg_toZigZagBase]
  exact Nat.one_lt_pow (by have := E.one_le_fifthExp; omega) h

/-- **The tower's size-flexible family, from any expander family.** -/
noncomputable def toSizedFamily (h : 1 < E.degree) : SizedExpanderFamily :=
  E.toZigZagBase.toSized (E.one_lt_deg_toZigZagBase h)

end ExpanderFamily

/-- **A base graph for the tower exists.** -/
theorem nonempty_zigZagBase : Nonempty ZigZagBase :=
  ⟨randExpander.toZigZagBase⟩

/-- **A size-flexible family exists.** -/
theorem nonempty_sizedExpanderFamily : Nonempty SizedExpanderFamily :=
  ⟨randExpander.toSizedFamily (by show 1 < 120; norm_num)⟩

end Complexity
