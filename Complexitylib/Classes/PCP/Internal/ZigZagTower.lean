/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.ZigZag
public import Complexitylib.Classes.PCP.Internal.Power
public import Complexitylib.Classes.PCP.Internal.ExpanderPad

/-!
# The zig-zag tower

One graph of constant size generates an infinite family. Square a member — the
degree becomes the fourth power of the base's, exactly the number of the base's
vertices — and zig-zag with the base: the vertex count is multiplied by that
same number while the degree drops back to the base's squared.

The spectral bookkeeping is what makes the recursion close. If the base has
bound `lam ≤ 1/5` and a member has bound `2/5`, squaring gives `4/25` and the
zig-zag estimate `λ(G ⓩ H) ≤ λ(G) + λ(H) + λ(H)²` gives at most
`4/25 + 1/5 + 1/25 = 2/5`, the invariant again.

Only the base is non-constructive; the recursion itself is an algorithm, which
is why this yields an expander family a machine can build.

## Main definitions

- `Complexity.ZigZagBase` — a constant-size graph to build from
- `Complexity.TowerStep` — a member of the family, with its invariants
- `Complexity.towerSucc` — one round of squaring and zig-zagging

## Main results

- `Complexity.towerSucc` carries the invariants forward, by construction
- `Complexity.ZigZagBase.order_tower` — the sizes are the powers of `deg ^ 4`
-/

@[expose] public section

namespace Complexity

/-- The seed of the tower: a graph whose vertices number the fourth power of its
degree, with a spectral bound of at most a fifth. -/
structure ZigZagBase where
  /-- The graph itself. -/
  base : RegGraph
  /-- Its vertices number the fourth power of its degree. -/
  card_eq : Fintype.card base.V = base.deg ^ 4
  /-- Its spectral bound. -/
  lam : ℝ
  /-- The bound is nonnegative. -/
  lam_nonneg : 0 ≤ lam
  /-- And at most a fifth, which is what makes the recursion close. -/
  lam_le : lam ≤ 1 / 5
  /-- The bound holds. -/
  spectral : base.SpectralBound lam

namespace ZigZagBase

variable (B : ZigZagBase)

/-- A member of the family: its degree is the base's squared, and its spectral
bound is two fifths. -/
structure TowerStep where
  /-- The graph. -/
  graph : RegGraph
  /-- Its degree is the base's squared. -/
  deg_eq : graph.deg = B.base.deg ^ 2
  /-- Its spectral bound. -/
  spec : graph.SpectralBound (2 / 5)

/-- Squaring a member makes its degree match the base's vertex count. -/
theorem card_sq_eq (T : B.TowerStep) :
    Fintype.card B.base.V = Fintype.card (T.graph.power 2).D := by
  have h1 : Fintype.card (T.graph.power 2).D = (T.graph.power 2).deg := rfl
  rw [h1, RegGraph.deg_power, T.deg_eq, B.card_eq]
  ring

/-- So the base's vertices name the squared member's darts. -/
noncomputable def stepEquiv (T : B.TowerStep) : B.base.V ≃ (T.graph.power 2).D :=
  Fintype.equivOfCardEq (B.card_sq_eq T)

/-- **One round of the tower**, against a chosen naming of the base's vertices
by the squared member's darts. The tower itself takes the arbitrary naming
`stepEquiv`; an explicitly encoded tower supplies its own. -/
noncomputable def towerSuccOf (T : B.TowerStep) (e : B.base.V ≃ (T.graph.power 2).D) :
    B.TowerStep where
  graph := RegGraph.zigzag (T.graph.power 2) B.base e
  deg_eq := by
    rw [RegGraph.deg_zigzag]
    ring
  spec := by
    have hsq : (T.graph.power 2).SpectralBound ((2 / 5) ^ 2) :=
      RegGraph.spectralBound_power T.graph T.spec 2
    have hzz := RegGraph.spectralBound_zigzag (T.graph.power 2) B.base e
      hsq B.spectral (by norm_num) B.lam_nonneg
    have h5 := B.lam_le
    have h0 := B.lam_nonneg
    refine hzz.mono ?_ ?_
    · nlinarith [h0]
    · nlinarith [h5, h0]

/-- **One round of the tower.** -/
noncomputable def towerSucc (T : B.TowerStep) : B.TowerStep :=
  B.towerSuccOf T (B.stepEquiv T)

@[simp] theorem graph_towerSucc (T : B.TowerStep) :
    (B.towerSucc T).graph = RegGraph.zigzag (T.graph.power 2) B.base (B.stepEquiv T) := rfl

/-- The first member: the base, squared. -/
noncomputable def towerZero : B.TowerStep where
  graph := B.base.power 2
  deg_eq := by
    rw [RegGraph.deg_power]
  spec := by
    have hsq : (B.base.power 2).SpectralBound (B.lam ^ 2) :=
      RegGraph.spectralBound_power B.base B.spectral 2
    refine hsq.mono (by positivity) ?_
    have h5 := B.lam_le
    have h0 := B.lam_nonneg
    nlinarith [h5, h0]

/-- **The tower.** -/
noncomputable def tower : ℕ → B.TowerStep
  | 0 => towerZero B
  | k + 1 => towerSucc B (tower k)

theorem deg_tower (k : ℕ) : (tower B k).graph.deg = B.base.deg ^ 2 :=
  (tower B k).deg_eq

theorem spectral_tower (k : ℕ) : (tower B k).graph.SpectralBound (2 / 5) :=
  (tower B k).spec

/-- **The sizes of the tower.** Each round multiplies the vertex count by the
base's vertex count, so the `k`-th member has `(deg ^ 4) ^ (k + 1)` vertices. -/
theorem order_tower (k : ℕ) :
    (tower B k).graph.order = (B.base.deg ^ 4) ^ (k + 1) := by
  induction k with
  | zero =>
      show (B.base.power 2).order = _
      rw [RegGraph.order_power]
      show Fintype.card B.base.V = _
      rw [B.card_eq]
      ring
  | succ m ih =>
      show (RegGraph.zigzag ((tower B m).graph.power 2) B.base
        (B.stepEquiv (tower B m))).order = _
      rw [RegGraph.order_zigzag, RegGraph.order_power, RegGraph.deg_power,
        deg_tower, ih]
      ring

/-- The sizes grow, so every vertex count is eventually passed. -/
theorem exists_order_ge (hd : 1 < B.base.deg) (n : ℕ) :
    ∃ k : ℕ, n ≤ (tower B k).graph.order := by
  refine ⟨n, ?_⟩
  rw [order_tower]
  have h1 : 2 ≤ B.base.deg ^ 4 := by
    calc 2 ≤ B.base.deg := hd
      _ = B.base.deg ^ 1 := (pow_one _).symm
      _ ≤ B.base.deg ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  calc n ≤ 2 ^ n := Nat.le_of_lt (Nat.lt_two_pow_self)
    _ ≤ (B.base.deg ^ 4) ^ n := Nat.pow_le_pow_left h1 n
    _ ≤ (B.base.deg ^ 4) ^ (n + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)

end ZigZagBase

end Complexity
