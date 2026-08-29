/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.SizedExpander
public import Complexitylib.Classes.PCP.Internal.MergeGen

/-!
# The exact-size family a tower gives

Assembling the pieces: for a requested size `n`, take the first tower member at
least twice as large, number its vertices and darts, fold it onto `n` at the
width the overshoot dictates, and pad the degree up to a bound that does not
depend on `n`.

Each step has been justified separately — `toFinForm` numbers the types,
`spectralBound_mergedN` folds at any width, `spectralBound_padLoops` pads the
degree — and this module only has to supply the arithmetic linking them.

## Main definitions

- `Complexity.ZigZagBase.famGraph` — the member for a requested size

## Main results

- `Complexity.ZigZagBase.order_famGraph`, `deg_famGraph` — it has exactly the
  requested size, and a degree independent of it
-/

@[expose] public section

namespace Complexity

namespace ZigZagBase

variable (B : ZigZagBase) (hd : 1 < B.base.deg)

/-- The width bound: the overshoot of the tower is at most `2 deg ^ 4`. -/
def widthBound : ℕ := 2 * B.base.deg ^ 4 + 1

/-- The family's degree: the width bound times the tower's degree. -/
def famDegree : ℕ := B.widthBound * B.base.deg ^ 2

theorem famDegree_pos : 0 < B.famDegree := by
  have h1 : 0 < B.widthBound := by
    rw [widthBound]
    omega
  have h2 : 0 < B.base.deg ^ 2 := by
    have := B.base.deg_pos
    positivity
  rw [famDegree]
  exact Nat.mul_pos h1 h2

/-- The size of the tower member used for `n`. -/
noncomputable def fitN (n : ℕ) : ℕ := (tower B (B.fitIndex hd n)).graph.order

/-- The degree of every tower member. -/
def fitD : ℕ := B.base.deg ^ 2

theorem fitD_pos : 0 < B.fitD := by
  have := B.base.deg_pos
  rw [fitD]
  positivity

/-- The tower member used for size `n`, with both its types numbered. -/
noncomputable def fitGraph (n : ℕ) : RegGraph :=
  (tower B (B.fitIndex hd n)).graph.toFinFormOf (B.fitN hd n) B.fitD rfl (deg_fit B hd n)

@[simp] theorem order_fitGraph (n : ℕ) : (B.fitGraph hd n).order = B.fitN hd n :=
  RegGraph.order_toFinFormOf _ _ _ _ _

@[simp] theorem deg_fitGraph (n : ℕ) : (B.fitGraph hd n).deg = B.fitD :=
  RegGraph.deg_toFinFormOf _ _ _ _ _

theorem spectral_fitGraph (n : ℕ) : (B.fitGraph hd n).SpectralBound (2 / 5) :=
  RegGraph.spectralBound_toFinFormOf _ _ _ _ _ (spectral_fit B hd n)

/-- The width used to fold that member onto `n`. -/
noncomputable def fitWidth (n : ℕ) : ℕ := RegGraph.mergeWidth (B.fitN hd n) n

theorem three_le_fitWidth {n : ℕ} (hn : 0 < n) : 3 ≤ B.fitWidth hd n :=
  RegGraph.three_le_mergeWidth hn (two_mul_le_order_fit B hd n)

theorem fitWidth_pos {n : ℕ} (hn : 0 < n) : 0 < B.fitWidth hd n := by
  have := B.three_le_fitWidth hd hn
  omega

theorem fitWidth_le {n : ℕ} (hn : 0 < n) : B.fitWidth hd n ≤ B.widthBound := by
  rw [fitWidth, widthBound]
  exact RegGraph.mergeWidth_le hn (order_fit_le B hd n hn)

theorem fitN_le_fitWidth_mul {n : ℕ} (hn : 0 < n) : B.fitN hd n ≤ B.fitWidth hd n * n :=
  RegGraph.le_mergeWidth_mul _ hn

theorem fitWidth_sub_one_mul_le (n : ℕ) : (B.fitWidth hd n - 1) * n ≤ B.fitN hd n :=
  RegGraph.mergeWidth_sub_one_mul_le _ _

theorem two_mul_le_fitN (n : ℕ) : 2 * n ≤ B.fitN hd n := two_mul_le_order_fit B hd n

/-- The rotation map of that member, at the numeric type it lives on. -/
noncomputable def fitRot (n : ℕ) :
    Fin (B.fitN hd n) × Fin B.fitD → Fin (B.fitN hd n) × Fin B.fitD :=
  (B.fitGraph hd n).rot

theorem fitRot_involutive (n : ℕ) : Function.Involutive (B.fitRot hd n) :=
  (B.fitGraph hd n).rot_involutive

theorem base_fitGraph (n : ℕ) :
    RegGraph.ofRot B.fitD B.fitD_pos (B.fitN hd n) (B.fitRot hd n) (B.fitRot_involutive hd n)
      = B.fitGraph hd n := rfl

/-! ### The fold -/

/-- The tower member folded onto exactly `n` vertices. -/
noncomputable def mergedGraph {n : ℕ} (hn : 0 < n) : RegGraph :=
  RegGraph.mergedN hn B.fitD_pos (B.fitWidth_pos hd hn) (B.fitN_le_fitWidth_mul hd hn)
    (B.fitRot hd n) (B.fitRot_involutive hd n)

@[simp] theorem order_mergedGraph {n : ℕ} (hn : 0 < n) : (B.mergedGraph hd hn).order = n :=
  RegGraph.order_mergedN _ _ _ _ _ _

@[simp] theorem deg_mergedGraph {n : ℕ} (hn : 0 < n) :
    (B.mergedGraph hd hn).deg = B.fitWidth hd n * B.fitD :=
  RegGraph.deg_mergedN _ _ _ _ _ _

/-- Folding at width at least three keeps the contraction below `4/5`. -/
theorem spectral_mergedGraph {n : ℕ} (hn : 0 < n) :
    (B.mergedGraph hd hn).SpectralBound (4 / 5) := by
  have hspec : (RegGraph.base B.fitD_pos (B.fitRot hd n)
      (B.fitRot_involutive hd n)).SpectralBound (2 / 5) := by
    rw [show RegGraph.base B.fitD_pos (B.fitRot hd n) (B.fitRot_involutive hd n)
        = B.fitGraph hd n from B.base_fitGraph hd n]
    exact B.spectral_fitGraph hd n
  have hmerged := RegGraph.spectralBound_mergedN hn B.fitD_pos (B.fitWidth_pos hd hn)
    (B.fitN_le_fitWidth_mul hd hn) (B.fitWidth_sub_one_mul_le hd n) (B.two_mul_le_fitN hd n)
    (B.fitRot hd n) (B.fitRot_involutive hd n) (by norm_num) hspec
  refine hmerged.mono (Real.sqrt_nonneg _) ?_
  rw [show (4 : ℝ) / 5 = Real.sqrt ((4 / 5) ^ 2) by
    rw [Real.sqrt_sq (by norm_num)]]
  refine Real.sqrt_le_sqrt ?_
  have hm3 : (3 : ℝ) ≤ (B.fitWidth hd n : ℝ) := by
    exact_mod_cast B.three_le_fitWidth hd hn
  have hm0 : (0 : ℝ) < (B.fitWidth hd n : ℝ) := by linarith
  set m : ℝ := (B.fitWidth hd n : ℝ)
  have h1 : (1 - (2 / 5 : ℝ) ^ 2) / (2 * m) ≤ (1 - (2 / 5 : ℝ) ^ 2) / (2 * 3) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have h2 : (1 : ℝ) / m ≤ 1 / 3 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm3
  nlinarith [h1, h2]

/-! ### The padding -/

theorem fitWidth_mul_fitD_le {n : ℕ} (hn : 0 < n) :
    B.fitWidth hd n * B.fitD ≤ B.famDegree :=
  Nat.mul_le_mul_right _ (B.fitWidth_le hd hn)

/-- The fold padded up to the family's uniform degree. -/
noncomputable def paddedGraph {n : ℕ} (hn : 0 < n) : RegGraph :=
  (B.mergedGraph hd hn).padLoops (B.famDegree - B.fitWidth hd n * B.fitD)

@[simp] theorem order_paddedGraph {n : ℕ} (hn : 0 < n) : (B.paddedGraph hd hn).order = n :=
  B.order_mergedGraph hd hn

@[simp] theorem deg_paddedGraph {n : ℕ} (hn : 0 < n) :
    (B.paddedGraph hd hn).deg = B.famDegree := by
  rw [paddedGraph, RegGraph.deg_padLoops, deg_mergedGraph]
  have := B.fitWidth_mul_fitD_le hd hn
  omega

/-- The uniform contraction factor of the family. -/
noncomputable def famLam : ℝ := Real.sqrt (1 - 27 / (25 * B.widthBound))

theorem three_le_widthBound : 3 ≤ B.widthBound := by
  have := B.base.deg_pos
  have : 1 ≤ B.base.deg ^ 4 := Nat.one_le_pow _ _ this
  rw [widthBound]
  omega

theorem famLam_nonneg : 0 ≤ B.famLam := Real.sqrt_nonneg _

theorem famLam_lt_one : B.famLam < 1 := by
  have hW : (3 : ℝ) ≤ (B.widthBound : ℝ) := by exact_mod_cast B.three_le_widthBound
  have hWpos : (0 : ℝ) < (B.widthBound : ℝ) := by linarith
  have h0 : (0 : ℝ) ≤ 1 - 27 / (25 * B.widthBound) := by
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  have hlt : (1 : ℝ) - 27 / (25 * B.widthBound) < 1 := by
    have : (0 : ℝ) < 27 / (25 * B.widthBound) := by positivity
    linarith
  calc B.famLam = Real.sqrt (1 - 27 / (25 * B.widthBound)) := rfl
    _ < Real.sqrt 1 := Real.sqrt_lt_sqrt h0 hlt
    _ = 1 := Real.sqrt_one

theorem spectral_paddedGraph {n : ℕ} (hn : 0 < n) :
    (B.paddedGraph hd hn).SpectralBound B.famLam := by
  have hpad := RegGraph.spectralBound_padLoops (G := B.mergedGraph hd hn)
    (B.famDegree - B.fitWidth hd n * B.fitD) (B.spectral_mergedGraph hd hn)
  refine hpad.mono (Real.sqrt_nonneg _) ?_
  rw [famLam]
  refine Real.sqrt_le_sqrt ?_
  have hle : B.fitWidth hd n * B.fitD ≤ B.famDegree := B.fitWidth_mul_fitD_le hd hn
  have hF : (0 : ℝ) < (B.fitD : ℝ) := by exact_mod_cast B.fitD_pos
  have hW : (3 : ℝ) ≤ (B.widthBound : ℝ) := by exact_mod_cast B.three_le_widthBound
  have hm : (3 : ℝ) ≤ (B.fitWidth hd n : ℝ) := by exact_mod_cast B.three_le_fitWidth hd hn
  have hDeg : ((B.famDegree : ℝ)) = (B.widthBound : ℝ) * (B.fitD : ℝ) := by
    rw [famDegree, fitD]; push_cast; ring
  have hk : (((B.famDegree - B.fitWidth hd n * B.fitD : ℕ) : ℝ))
      = (B.famDegree : ℝ) - (B.fitWidth hd n : ℝ) * (B.fitD : ℝ) := by
    rw [Nat.cast_sub hle]; push_cast; ring
  have hWpos : (0 : ℝ) < (B.widthBound : ℝ) := by linarith
  have hDpos : (0 : ℝ) < (B.widthBound : ℝ) * (B.fitD : ℝ) := by positivity
  rw [B.deg_mergedGraph hd hn, hk]
  push_cast
  rw [hDeg, show ((B.fitWidth hd n : ℝ) * (B.fitD : ℝ)
      + ((B.widthBound : ℝ) * (B.fitD : ℝ) - (B.fitWidth hd n : ℝ) * (B.fitD : ℝ)))
      = (B.widthBound : ℝ) * (B.fitD : ℝ) from by ring, div_le_iff₀ hDpos, sub_mul, one_mul,
    show 27 / (25 * (B.widthBound : ℝ)) * ((B.widthBound : ℝ) * (B.fitD : ℝ))
      = 27 * (B.fitD : ℝ) / 25 from by field_simp]
  nlinarith [mul_le_mul_of_nonneg_right hm (le_of_lt hF)]

/-! ### The family -/

/-- The member of the family on `n` vertices, for `n` positive: the padded fold,
with its darts numbered by the family's uniform degree. -/
noncomputable def famGraphPos {n : ℕ} (hn : 0 < n) : RegGraph :=
  (B.paddedGraph hd hn).relabel
    (Fintype.equivFinOfCardEq (B.deg_paddedGraph hd hn))

theorem famGraphPos_V {n : ℕ} (hn : 0 < n) : (B.famGraphPos hd hn).V = Fin n := rfl

theorem famGraphPos_D {n : ℕ} (hn : 0 < n) : (B.famGraphPos hd hn).D = Fin B.famDegree := rfl

theorem spectral_famGraphPos {n : ℕ} (hn : 0 < n) :
    (B.famGraphPos hd hn).SpectralBound B.famLam :=
  RegGraph.spectralBound_relabel _ _ (B.spectral_paddedGraph hd hn)

/-- The family's rotation map: the padded fold when there is anything to fold,
and the identity on the empty vertex set otherwise. -/
noncomputable def famRot (n : ℕ) :
    Fin n × Fin B.famDegree → Fin n × Fin B.famDegree :=
  if hn : 0 < n then (B.famGraphPos hd hn).rot else id

theorem famRot_involutive (n : ℕ) : Function.Involutive (B.famRot hd n) := by
  rw [famRot]
  split
  · exact (B.famGraphPos hd ‹_›).rot_involutive
  · exact fun x => rfl

theorem famRot_eq {n : ℕ} (hn : 0 < n) : B.famRot hd n = (B.famGraphPos hd hn).rot := by
  rw [famRot, dif_pos hn]

theorem spectral_famRot (n : ℕ) :
    (RegGraph.ofRot B.famDegree B.famDegree_pos n (B.famRot hd n)
      (B.famRot_involutive hd n)).SpectralBound B.famLam := by
  rcases Nat.eq_zero_or_pos n with h | hn
  · subst h
    exact RegGraph.spectralBound_of_isEmpty (by exact Fin.isEmpty' ) _
  · have key : ∀ (r : Fin n × Fin B.famDegree → Fin n × Fin B.famDegree)
        (hr : Function.Involutive r), r = (B.famGraphPos hd hn).rot →
        (RegGraph.ofRot B.famDegree B.famDegree_pos n r hr).SpectralBound B.famLam := by
      rintro r hr rfl
      exact B.spectral_famGraphPos hd hn
    exact key _ _ (B.famRot_eq hd hn)

/-- The expander family a zig-zag base generates: one member at every size, of a
degree that does not depend on the size, all contracting by the same factor. -/
noncomputable def family : ExpanderFamily where
  degree := B.famDegree
  degree_pos := B.famDegree_pos
  rot := B.famRot hd
  rot_involutive := B.famRot_involutive hd
  lam := B.famLam
  lam_nonneg := B.famLam_nonneg
  lam_lt_one := B.famLam_lt_one
  spectral := B.spectral_famRot hd

end ZigZagBase

end Complexity
