/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.SuccMachine

/-!
# A layout to run the walk in

⚠️ Unreviewed by Bolton

Every contract of the walk is stated against an abstract `Complexity.WalkLayout` — which register
plays which role, and how wide each is guessed. This file builds one: nine scratch blocks, then
the two code tuples the walk swaps, then as many spare tuples as the caller asks for, one register
per block and in that order.

Nothing about the walk depends on this particular arrangement; it exists so that the assembled
machine has a layout to be instantiated at.

## Main definitions

- `walkJJ` — how many registers the arrangement needs
- `stdLayout`, `stdWidths` — the arrangement, and its widths
-/

@[expose] public section

namespace Complexity

/-- The number of scan registers the arrangement uses, less one. -/
def walkJJ (kk sp : ℕ) : ℕ := 8 + (2 + sp) * (kk + 3)

/-- Which role each block plays: nine scratch blocks, then the code tuples. -/
def stdRole (kk : ℕ) : ℕ → BlockRole kk := fun p =>
  if p = 0 then BlockRole.ruler
  else if p = 1 then BlockRole.par
  else if p = 2 then BlockRole.mv
  else if p = 3 then BlockRole.dr
  else if p = 4 then BlockRole.res
  else if p = 5 then BlockRole.acc
  else if p = 6 then BlockRole.cnt
  else if p = 7 then BlockRole.cnt'
  else if p = 8 then BlockRole.target
  else if (p - 9) / (kk + 3) = 0 then BlockRole.codeA ((p - 9) % (kk + 3))
  else if (p - 9) / (kk + 3) = 1 then BlockRole.codeB ((p - 9) % (kk + 3))
  else BlockRole.spare ((p - 9) / (kk + 3) - 2) ((p - 9) % (kk + 3))

private theorem stdRole_code (kk f p : ℕ) (hp : p < kk + 3) :
    (9 + f * (kk + 3) + p - 9) / (kk + 3) = f ∧
      (9 + f * (kk + 3) + p - 9) % (kk + 3) = p := by
  have he : 9 + f * (kk + 3) + p - 9 = p + f * (kk + 3) := by omega
  rw [he, Nat.add_mul_div_right _ _ (by omega : 0 < kk + 3), Nat.div_eq_of_lt hp,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp]
  exact ⟨by omega, rfl⟩

/-- **The arrangement.** -/
def stdLayout (kk sp : ℕ) (hsp : 0 < sp) : WalkLayout kk (walkJJ kk sp) where
  role := stdRole kk
  reg := fun p => if h : p < walkJJ kk sp + 1 then ⟨p, h⟩ else ⟨0, Nat.zero_lt_succ _⟩
  blocks := 9 + (2 + sp) * (kk + 3)
  reg_inj := by
    intro p q hp hq h
    have hjj : walkJJ kk sp + 1 = 9 + (2 + sp) * (kk + 3) := by
      rw [walkJJ]
      omega
    rw [dif_pos (by omega), dif_pos (by omega)] at h
    exact congrArg Fin.val h
  rulerIdx := 0
  parIdx := 1
  mvIdx := 2
  drIdx := 3
  resIdx := 4
  accIdx := 5
  cntIdx := 6
  cnt'Idx := 7
  targetIdx := 8
  codeAIdx := fun p => 9 + p
  codeBIdx := fun p => 9 + (kk + 3) + p
  spares := sp
  spares_pos := hsp
  spareIdx := fun n p => 9 + (kk + 3) + (kk + 3) + n * (kk + 3) + p
  scratch := 9
  codeA_eq := fun _ _ => rfl
  codeB_eq := fun _ _ => rfl
  spare_eq := fun _ _ _ _ => rfl
  blocks_eq := by ring
  ruler_zero := by
    rw [dif_pos (by rw [walkJJ]; omega)]
    rfl
  ruler_scratch := by omega
  par_scratch := by omega
  mv_scratch := by omega
  dr_scratch := by omega
  res_scratch := by omega
  acc_scratch := by omega
  cnt_scratch := by omega
  cnt'_scratch := by omega
  target_scratch := by omega
  role_ruler := rfl
  role_par := rfl
  role_mv := rfl
  role_dr := rfl
  role_res := rfl
  role_acc := rfl
  role_cnt := rfl
  role_cnt' := rfl
  role_target := rfl
  role_codeA := by
    intro p hp
    obtain ⟨hdiv, hmod⟩ := stdRole_code kk 0 p hp
    show stdRole kk (9 + p) = _
    rw [stdRole]
    rw [show (9 : ℕ) + p = 9 + 0 * (kk + 3) + p by ring]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_pos hdiv, hmod]
  role_codeB := by
    intro p hp
    obtain ⟨hdiv, hmod⟩ := stdRole_code kk 1 p hp
    show stdRole kk (9 + (kk + 3) + p) = _
    rw [stdRole]
    rw [show (9 : ℕ) + (kk + 3) + p = 9 + 1 * (kk + 3) + p by ring]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_pos hdiv, hmod]
  role_spare := by
    intro n p hn hp
    obtain ⟨hdiv, hmod⟩ := stdRole_code kk (2 + n) p hp
    show stdRole kk (9 + (kk + 3) + (kk + 3) + n * (kk + 3) + p) = _
    rw [stdRole]
    rw [show (9 : ℕ) + (kk + 3) + (kk + 3) + n * (kk + 3) + p = 9 + (2 + n) * (kk + 3) + p by
      ring]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by rw [hdiv]; omega), if_neg (by rw [hdiv]; omega), hdiv, hmod]
    congr 1
    omega

/-- How wide each block of the arrangement is guessed. -/
noncomputable def stdWidth {kk : ℕ} (tm : NTM kk) (nn S wc : ℕ) : ℕ → ℕ := fun p =>
  if p = 0 then walkScanLen tm nn S - 1
  else if p = 1 then (succParamsCodec tm.Q kk).width - 1
  else if p ≤ 5 then 0
  else if p ≤ 8 then wc - 1
  else codeWidthScan tm nn S ((p - 9) % (kk + 3))

/-- **The arrangement, with its widths.** -/
noncomputable def stdWidths {kk : ℕ} (tm : NTM kk) (nn S wc sp : ℕ) (hsp : 0 < sp) :
    WalkWidths kk (walkJJ kk sp) tm nn S wc where
  toWalkLayout := stdLayout kk sp hsp
  width := stdWidth tm nn S wc
  width_ruler := rfl
  width_par := rfl
  width_mv := rfl
  width_dr := rfl
  width_res := rfl
  width_acc := rfl
  width_cnt := rfl
  width_cnt' := rfl
  width_target := rfl
  width_codeA := by
    intro p hp
    show stdWidth tm nn S wc (9 + p) = _
    rw [stdWidth]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      show 9 + p - 9 = p by omega, Nat.mod_eq_of_lt hp]
  width_codeB := by
    intro p hp
    show stdWidth tm nn S wc (9 + (kk + 3) + p) = _
    rw [stdWidth]
    obtain ⟨-, hmod⟩ := stdRole_code kk 1 p hp
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [show 9 + (kk + 3) + p = 9 + 1 * (kk + 3) + p by ring] at *
    rw [hmod]
  width_spare := by
    intro n p hn hp
    show stdWidth tm nn S wc (9 + (kk + 3) + (kk + 3) + n * (kk + 3) + p) = _
    rw [stdWidth]
    obtain ⟨-, hmod⟩ := stdRole_code kk (2 + n) p hp
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [show 9 + (kk + 3) + (kk + 3) + n * (kk + 3) + p = 9 + (2 + n) * (kk + 3) + p by ring] at *
    rw [hmod]

end Complexity
