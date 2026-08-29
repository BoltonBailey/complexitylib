/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.ZigZagTower

/-!
# Expanders of approximately a given size

The zig-zag tower produces expanders only at the sizes `(deg ^ 4) ^ (k + 1)`,
which are far apart. `Pad` shows that this is no obstacle: a constraint graph
may be enlarged with isolated vertices, at no cost to anything the amplification
measures, so it is enough to have an expander on *some* size between `n` and a
constant multiple of `n`.

This module records that weaker interface and builds one from a `ZigZagBase`,
by taking the first member of the tower large enough. Minimality of the choice
is what bounds the overshoot: the previous member was too small, and each round
multiplies the size by exactly `deg ^ 4`.

## Main definitions

- `Complexity.SizedExpanderFamily` — expanders of approximately prescribed size
- `Complexity.ZigZagBase.toSized` — the family the tower gives

## Main results

- `Complexity.ZigZagBase.order_toSized_le` — the overshoot is a constant factor
-/

@[expose] public section

namespace Complexity

/-- A family of constant-degree expanders, one of approximately each size: the
graph for `n` has between `n` and `factor * n` vertices. -/
structure SizedExpanderFamily where
  /-- The common degree. -/
  degree : ℕ
  /-- The degree is positive. -/
  degree_pos : 0 < degree
  /-- How far the size may overshoot. -/
  factor : ℕ
  /-- The graph provided for a requested size. -/
  graph : ℕ → RegGraph
  /-- Every member has the common degree. -/
  deg_graph : ∀ n, (graph n).deg = degree
  /-- It is at least as large as requested. -/
  order_ge : ∀ n, n ≤ (graph n).order
  /-- And not too much larger. -/
  order_le : ∀ n, 1 ≤ n → (graph n).order ≤ factor * n
  /-- The uniform contraction factor. -/
  lam : ℝ
  /-- It is nonnegative. -/
  lam_nonneg : 0 ≤ lam
  /-- And below one. -/
  lam_lt_one : lam < 1
  /-- Every member contracts mean-zero functions by `lam`. -/
  spectral : ∀ n, (graph n).SpectralBound lam

namespace ZigZagBase

variable (B : ZigZagBase) (hd : 1 < B.base.deg)

/-- The first index whose member is large enough. -/
noncomputable def towerIndex (n : ℕ) : ℕ :=
  Nat.find (B.exists_order_ge hd n)

theorem le_order_towerIndex (n : ℕ) :
    n ≤ (tower B (B.towerIndex hd n)).graph.order :=
  Nat.find_spec (B.exists_order_ge hd n)

theorem order_towerIndex_le (n : ℕ) (hn : 1 ≤ n) :
    (tower B (B.towerIndex hd n)).graph.order ≤ B.base.deg ^ 4 * n := by
  classical
  rcases Nat.eq_zero_or_pos (B.towerIndex hd n) with h0 | hpos
  · rw [towerIndex] at h0 ⊢
    rw [h0, order_tower]
    calc (B.base.deg ^ 4) ^ (0 + 1) = B.base.deg ^ 4 := by ring
      _ ≤ B.base.deg ^ 4 * n := Nat.le_mul_of_pos_right _ hn
  · obtain ⟨m, hm⟩ : ∃ m, B.towerIndex hd n = m + 1 := ⟨B.towerIndex hd n - 1, by omega⟩
    have hfind : Nat.find (B.exists_order_ge hd n) = m + 1 := hm
    have hlt : ¬ n ≤ (tower B m).graph.order :=
      Nat.find_min (B.exists_order_ge hd n) (m := m) (by rw [hfind]; omega)
    have hmlt : (tower B m).graph.order < n := by omega
    rw [hm, order_tower]
    have hprev : (B.base.deg ^ 4) ^ (m + 1) < n := by
      rw [← order_tower]
      exact hmlt
    calc (B.base.deg ^ 4) ^ (m + 1 + 1) = B.base.deg ^ 4 * (B.base.deg ^ 4) ^ (m + 1) := by
          ring
      _ ≤ B.base.deg ^ 4 * n := Nat.mul_le_mul_left _ (le_of_lt hprev)

/-- **The tower, as a size-flexible family.** -/
noncomputable def toSized : SizedExpanderFamily where
  degree := B.base.deg ^ 2
  degree_pos := by
    have := B.base.deg_pos
    positivity
  factor := B.base.deg ^ 4
  graph := fun n => (tower B (B.towerIndex hd n)).graph
  deg_graph := fun n => deg_tower B _
  order_ge := B.le_order_towerIndex hd
  order_le := B.order_towerIndex_le hd
  lam := 2 / 5
  lam_nonneg := by norm_num
  lam_lt_one := by norm_num
  spectral := fun n => spectral_tower B _

/-! ### The member used for a requested size -/

/-- The tower member chosen for size `n`: the first one at least twice as big,
which is the overshoot the merge needs. -/
noncomputable def fitIndex (n : ℕ) : ℕ := B.towerIndex hd (2 * n)

theorem two_mul_le_order_fit (n : ℕ) :
    2 * n ≤ (tower B (B.fitIndex hd n)).graph.order :=
  B.le_order_towerIndex hd (2 * n)

theorem order_fit_le (n : ℕ) (hn : 1 ≤ n) :
    (tower B (B.fitIndex hd n)).graph.order ≤ (2 * B.base.deg ^ 4) * n := by
  have h := B.order_towerIndex_le hd (2 * n) (by omega)
  calc (tower B (B.fitIndex hd n)).graph.order ≤ B.base.deg ^ 4 * (2 * n) := h
    _ = (2 * B.base.deg ^ 4) * n := by ring

theorem deg_fit (n : ℕ) : (tower B (B.fitIndex hd n)).graph.deg = B.base.deg ^ 2 :=
  deg_tower B _

theorem spectral_fit (n : ℕ) :
    (tower B (B.fitIndex hd n)).graph.SpectralBound (2 / 5) :=
  spectral_tower B _

end ZigZagBase

end Complexity
