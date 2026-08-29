/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.ExpanderMerge
public import Complexitylib.Classes.PCP.Internal.ExpanderPad
public import Complexitylib.Classes.PCP.Internal.Power
public import Complexitylib.Classes.PCP.Internal.Clique

/-!
# An expander family from expanders of square size

Explicit constructions such as Margulis's live on `m × m` grids. This module
turns a family on the squares into an `ExpanderFamily` on every vertex count:

* the square graphs are powered until the bound is at most `1/2`, and their
  darts renamed to a `Fin`;
* for `n ≥ 10` a square `N = m²` with `2n ≤ N ≤ 3n` exists, and the merge of
  `ExpanderMerge` gives a graph on `n` vertices;
* for `n < 10` a clique with loops does, padded up to the common degree.

## Main definitions

- `Complexity.SquareFamily` — expanders on every `m * m`
- `Complexity.SquareFamily.toFamily` — the derived `ExpanderFamily`
-/

@[expose] public section

namespace Complexity

/-- A family of constant-degree expanders on the squares `m * m`. -/
structure SquareFamily where
  /-- The constant degree. -/
  degree : ℕ
  /-- The degree is positive. -/
  degree_pos : 0 < degree
  /-- The rotation map on `m * m` vertices. -/
  rot : ∀ m : ℕ, Fin (m * m) × Fin degree → Fin (m * m) × Fin degree
  /-- Each rotation map is an involution. -/
  rot_involutive : ∀ m, Function.Involutive (rot m)
  /-- The uniform contraction factor. -/
  lam : ℝ
  /-- The factor is nonnegative. -/
  lam_nonneg : 0 ≤ lam
  /-- The factor is below one. -/
  lam_lt_one : lam < 1
  /-- Every member contracts mean-zero functions by `lam`. -/
  spectral : ∀ m : ℕ,
    (RegGraph.ofRot degree degree_pos (m * m) (rot m) (rot_involutive m)).SpectralBound lam

/-! ### A square between `2n` and `3n` -/

/-- For `n ≥ 10`, `(⌊√(2n)⌋ + 1)²` lies in `[2n, 3n]`. -/
theorem sq_between (n : ℕ) (hn : 10 ≤ n) :
    2 * n ≤ (Nat.sqrt (2 * n) + 1) * (Nat.sqrt (2 * n) + 1)
      ∧ (Nat.sqrt (2 * n) + 1) * (Nat.sqrt (2 * n) + 1) ≤ 3 * n := by
  set s := Nat.sqrt (2 * n) with hs
  have h1 : 2 * n < (s + 1) * (s + 1) := Nat.lt_succ_sqrt (2 * n)
  have h2 : s * s ≤ 2 * n := Nat.sqrt_le (2 * n)
  refine ⟨h1.le, ?_⟩
  -- `2 s + 1 ≤ n` since otherwise `n² ≤ 4 s² ≤ 8 n`
  nlinarith

/-! ### The empty graph -/

/-- The empty graph satisfies every bound. -/
theorem spectralBound_zero (D : ℕ) (hD : 0 < D) (lam : ℝ) :
    (RegGraph.ofRot D hD 0 id (fun _ => rfl)).SpectralBound lam := by
  intro f _
  show (∑ v : Fin 0, ((RegGraph.ofRot D hD 0 id (fun _ => rfl)).step f v) ^ 2)
    ≤ lam ^ 2 * ∑ v : Fin 0, (f v) ^ 2
  simp

namespace SquareFamily

variable (S : SquareFamily)

/-! ### Powering the squares -/

theorem exists_pow_le_half : ∃ t : ℕ, S.lam ^ t ≤ 1 / 2 := by
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) S.lam_lt_one
  exact ⟨t, ht.le⟩

/-- The powering exponent: enough to bring the bound below one half. -/
noncomputable def powExp : ℕ := Classical.choose S.exists_pow_le_half

theorem pow_le_half : S.lam ^ S.powExp ≤ 1 / 2 := Classical.choose_spec S.exists_pow_le_half

theorem pow_nonneg' : 0 ≤ S.lam ^ S.powExp := pow_nonneg S.lam_nonneg _

/-- The degree after powering. -/
noncomputable def powDeg : ℕ := S.degree ^ S.powExp

theorem powDeg_pos : 0 < S.powDeg := pow_pos S.degree_pos _

/-- Walk labels as a `Fin`. -/
noncomputable def dartEquiv : (Fin S.powExp → Fin S.degree) ≃ Fin S.powDeg :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; rfl)

/-- The powered square graph, with `Fin` darts. -/
noncomputable def square (m : ℕ) : RegGraph :=
  ((RegGraph.ofRot S.degree S.degree_pos (m * m) (S.rot m) (S.rot_involutive m)).power
    S.powExp).relabel S.dartEquiv

theorem spectral_square (m : ℕ) : (S.square m).SpectralBound (S.lam ^ S.powExp) :=
  RegGraph.spectralBound_relabel _ _ (RegGraph.spectralBound_power _ (S.spectral m) _)

/-- The powered square as rotation data. -/
noncomputable def squareRot (m : ℕ) : Fin (m * m) × Fin S.powDeg → Fin (m * m) × Fin S.powDeg :=
  (S.square m).rot

theorem squareRot_involutive (m : ℕ) : Function.Involutive (S.squareRot m) :=
  (S.square m).rot_involutive

theorem spectral_squareRot (m : ℕ) :
    (RegGraph.ofRot S.powDeg S.powDeg_pos (m * m) (S.squareRot m)
      (S.squareRot_involutive m)).SpectralBound (S.lam ^ S.powExp) :=
  S.spectral_square m

/-! ### The common degree -/

/-- The degree of the derived family. -/
noncomputable def famDeg : ℕ := 3 * S.powDeg + 10

theorem famDeg_pos : 0 < S.famDeg := by rw [famDeg]; omega

/-! ### Large `n`: merge -/

/-- The side of the square used for `n`. -/
def mVal (n : ℕ) : ℕ := Nat.sqrt (2 * n) + 1

theorem mVal_spec {n : ℕ} (hn : 10 ≤ n) :
    2 * n ≤ mVal n * mVal n ∧ mVal n * mVal n ≤ 3 * n := sq_between n hn

/-- The graph on `n ≥ 10` vertices: the merge of a powered square, padded to the
common degree. -/
noncomputable def bigGraph (n : ℕ) (hn : 10 ≤ n) : RegGraph :=
  (((RegGraph.merged (N := mVal n * mVal n) (d := S.powDeg) (by omega) S.powDeg_pos
      (mVal_spec hn).2 (S.squareRot (mVal n)) (S.squareRot_involutive (mVal n))).relabel
      (finProdFinEquiv : Fin 3 × Fin S.powDeg ≃ Fin (3 * S.powDeg))).padLoops 10).relabel
    (finSumFinEquiv : Fin (3 * S.powDeg) ⊕ Fin 10 ≃ Fin (3 * S.powDeg + 10))

/-- The bound for the large case. -/
noncomputable def bigLam : ℝ :=
  Real.sqrt ((3 * (S.powDeg : ℝ) * (17 / 24) + 10) / (3 * (S.powDeg : ℝ) + 10))

theorem bigLam_lt_one : S.bigLam < 1 := by
  rw [bigLam, Real.sqrt_lt' one_pos, one_pow, div_lt_one (by positivity)]
  have : (0 : ℝ) < S.powDeg := by exact_mod_cast S.powDeg_pos
  nlinarith

theorem bigLam_nonneg : 0 ≤ S.bigLam := Real.sqrt_nonneg _

theorem spectral_bigGraph (n : ℕ) (hn : 10 ≤ n) : (S.bigGraph n hn).SpectralBound S.bigLam := by
  have hl := S.pow_le_half
  have hl0 := S.pow_nonneg'
  have hl2 : (S.lam ^ S.powExp) ^ 2 ≤ 1 := by nlinarith
  have hmerged := RegGraph.spectralBound_merged (N := mVal n * mVal n) (d := S.powDeg)
    (by omega : 0 < n) S.powDeg_pos (mVal_spec hn).2 (S.squareRot (mVal n))
    (S.squareRot_involutive (mVal n)) hl2 (S.spectral_squareRot (mVal n)) (mVal_spec hn).1
  have hrel := RegGraph.spectralBound_relabel _
    (finProdFinEquiv : Fin 3 × Fin S.powDeg ≃ Fin (3 * S.powDeg)) hmerged
  have hpad := RegGraph.spectralBound_padLoops _ 10 hrel
  have hrel2 := RegGraph.spectralBound_relabel _
    (finSumFinEquiv : Fin (3 * S.powDeg) ⊕ Fin 10 ≃ Fin (3 * S.powDeg + 10)) hpad
  refine hrel2.mono (Real.sqrt_nonneg _) ?_
  rw [bigLam]
  apply Real.sqrt_le_sqrt
  rw [RegGraph.deg_relabel, RegGraph.deg_merged]
  push_cast
  rw [Real.sq_sqrt (by positivity)]
  have hD : (0 : ℝ) < 3 * (S.powDeg : ℝ) + 10 := by positivity
  rw [div_le_div_iff_of_pos_right hD]
  have hmu : 1 / 2 + 5 * (S.lam ^ S.powExp) ^ 2 / 6 ≤ 17 / 24 := by nlinarith
  have : (0 : ℝ) ≤ 3 * (S.powDeg : ℝ) := by positivity
  nlinarith

/-! ### Small `n`: cliques -/

/-- The graph on `0 < n < 10` vertices: a clique with loops, padded. -/
noncomputable def smallGraph (n : ℕ) (hn : 0 < n) (hle : n ≤ S.famDeg) : RegGraph :=
  ((RegGraph.cliqueLoops n hn).padLoops (S.famDeg - n)).relabel
    ((finSumFinEquiv : Fin n ⊕ Fin (S.famDeg - n) ≃ Fin (n + (S.famDeg - n))).trans
      (finCongr (Nat.add_sub_cancel' hle) : Fin (n + (S.famDeg - n)) ≃ Fin S.famDeg))

/-- The bound for the small case. -/
noncomputable def smallLam : ℝ := Real.sqrt (((S.famDeg : ℝ) - 1) / S.famDeg)

theorem smallLam_lt_one : S.smallLam < 1 := by
  have : (0 : ℝ) < S.famDeg := by exact_mod_cast S.famDeg_pos
  rw [smallLam, Real.sqrt_lt' one_pos, one_pow, div_lt_one this]
  linarith

theorem smallLam_nonneg : 0 ≤ S.smallLam := Real.sqrt_nonneg _

theorem deg_cliqueLoops (n : ℕ) (hn : 0 < n) : (RegGraph.cliqueLoops n hn).deg = n :=
  Fintype.card_fin n

theorem spectral_smallGraph (n : ℕ) (hn : 0 < n) (hle : n ≤ S.famDeg) :
    (S.smallGraph n hn hle).SpectralBound S.smallLam := by
  have hpad := RegGraph.spectralBound_padLoops _ (S.famDeg - n)
    (RegGraph.spectralBound_cliqueLoops hn)
  have hrel := RegGraph.spectralBound_relabel _
    ((finSumFinEquiv : Fin n ⊕ Fin (S.famDeg - n) ≃ Fin (n + (S.famDeg - n))).trans
      (finCongr (Nat.add_sub_cancel' hle) : Fin (n + (S.famDeg - n)) ≃ Fin S.famDeg)) hpad
  refine hrel.mono (Real.sqrt_nonneg _) ?_
  rw [smallLam]
  apply Real.sqrt_le_sqrt
  rw [deg_cliqueLoops]
  have hcast : ((S.famDeg - n : ℕ) : ℝ) = (S.famDeg : ℝ) - n := by
    rw [Nat.cast_sub hle]
  rw [hcast]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD : (0 : ℝ) < S.famDeg := by exact_mod_cast S.famDeg_pos
  have hsum : (n : ℝ) + ((S.famDeg : ℝ) - n) = S.famDeg := by ring
  rw [hsum, div_le_div_iff_of_pos_right hD]
  nlinarith

/-! ### The family -/

theorem le_famDeg {n : ℕ} (h : ¬ 10 ≤ n) : n ≤ S.famDeg := by rw [famDeg]; omega

/-- The rotation map on `n` vertices, by cases. -/
noncomputable def famRot (n : ℕ) : Fin n × Fin S.famDeg → Fin n × Fin S.famDeg :=
  if h : 10 ≤ n then (S.bigGraph n h).rot
  else if h0 : 0 < n then (S.smallGraph n h0 (S.le_famDeg h)).rot
  else id

theorem famRot_involutive (n : ℕ) : Function.Involutive (S.famRot n) := by
  intro x
  unfold famRot
  split_ifs with h h0
  · exact (S.bigGraph n h).rot_involutive x
  · exact (S.smallGraph n h0 _).rot_involutive x
  · rfl

/-- The uniform bound. -/
noncomputable def famLam : ℝ := max S.bigLam S.smallLam

theorem famLam_nonneg : 0 ≤ S.famLam := le_max_of_le_left S.bigLam_nonneg

theorem famLam_lt_one : S.famLam < 1 := max_lt S.bigLam_lt_one S.smallLam_lt_one

theorem spectral_fam (n : ℕ) :
    (RegGraph.ofRot S.famDeg S.famDeg_pos n (S.famRot n) (S.famRot_involutive n)).SpectralBound
      S.famLam := by
  by_cases h : 10 ≤ n
  · have hb := S.spectral_bigGraph n h
    have heq : RegGraph.ofRot S.famDeg S.famDeg_pos n (S.famRot n) (S.famRot_involutive n)
        = S.bigGraph n h := by
      unfold famRot
      simp only [dif_pos h]
      rfl
    rw [heq]
    exact hb.mono S.bigLam_nonneg (le_max_left _ _)
  · by_cases h0 : 0 < n
    · have hs := S.spectral_smallGraph n h0 (S.le_famDeg h)
      have heq : RegGraph.ofRot S.famDeg S.famDeg_pos n (S.famRot n) (S.famRot_involutive n)
          = S.smallGraph n h0 (S.le_famDeg h) := by
        unfold famRot
        simp only [dif_neg h, dif_pos h0]
        rfl
      rw [heq]
      exact hs.mono S.smallLam_nonneg (le_max_right _ _)
    · have hz : n = 0 := by omega
      subst hz
      exact spectralBound_zero _ _ _

/-- **The derived expander family.** -/
noncomputable def toFamily : ExpanderFamily where
  degree := S.famDeg
  degree_pos := S.famDeg_pos
  rot := S.famRot
  rot_involutive := S.famRot_involutive
  lam := S.famLam
  lam_nonneg := S.famLam_nonneg
  lam_lt_one := S.famLam_lt_one
  spectral := S.spectral_fam

end SquareFamily

end Complexity
