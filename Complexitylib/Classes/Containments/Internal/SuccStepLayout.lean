/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.SuccMachine

/-!
# The tapes a walk step touches

⚠️ Unreviewed by Bolton

`Complexity.walkStepTM_hoareTime` asks its caller for a list of guess targets, an accumulator
tape, and a handful of facts separating them from each other, from the auxiliary tapes and from
the guess tape. All of those are properties of the layout alone, so they are settled here once:
`stepTargets` is the list of scanned tapes, `auxIdx` an auxiliary tape, and the lemmas below are
exactly the side conditions the contract takes.

## Main definitions

- `stepTargets`, `auxIdx`

## Main results

- `stepTargets_nodup`, `mem_stepTargets`, `natAdd_notMem_stepTargets`
- `stepReg_ne_natAdd`, `stepReg_ne_last`, `stepReg_inj`
- `auxIdx_ne_castAdd`, `auxIdx_ne_last`, `WalkLayout.res_ne_zero`
-/

@[expose] public section

namespace Complexity

variable {kk jj r : ℕ}

/-! ## Values of the tape indices -/

@[simp] theorem val_walkReg (i : Fin (jj + 1)) :
    (walkReg (r := r) i : Fin (jj + 2 + r + 1)).val = i.val := rfl

@[simp] theorem val_castAdd_castSucc (i : Fin (jj + 2)) :
    ((Fin.castAdd r i).castSucc : Fin (jj + 2 + r + 1)).val = i.val := rfl

@[simp] theorem val_natAdd_castSucc (c : Fin r) :
    ((Fin.natAdd (jj + 2) c).castSucc : Fin (jj + 2 + r + 1)).val = jj + 2 + c.val := rfl

/-! ## The guess targets -/

/-- The tapes a step's guess stage writes: every scanned register and the verdict tape. -/
def stepTargets (jj r : ℕ) : List (Fin (jj + 2 + r)) :=
  (List.finRange (jj + 2)).map (Fin.castAdd r)

theorem mem_stepTargets (i : Fin (jj + 2)) : Fin.castAdd r i ∈ stepTargets jj r :=
  List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

theorem stepTargets_nodup : (stepTargets jj r).Nodup := by
  refine List.Nodup.map (fun a b h => ?_) (List.nodup_finRange _)
  have := congrArg Fin.val h
  exact Fin.ext (by simpa using this)

theorem natAdd_notMem_stepTargets (c : Fin r) :
    Fin.natAdd (jj + 2) c ∉ stepTargets jj r := by
  intro hc
  rw [stepTargets, List.mem_map] at hc
  obtain ⟨i, -, hi⟩ := hc
  have hv := congrArg Fin.val hi
  have h1 : (Fin.castAdd r i : Fin (jj + 2 + r)).val = i.val := rfl
  have h2 : (Fin.natAdd (jj + 2) c : Fin (jj + 2 + r)).val = jj + 2 + c.val := rfl
  have := i.isLt
  omega

/-! ## The registers a step guesses into -/

variable {tm : NTM kk} {nn S wc : ℕ}

theorem stepReg_ne_natAdd (L : WalkWidths kk jj tm nn S wc) (second : Bool) (p : ℕ)
    (c : Fin r) : stepReg (r := r) L second p ≠ (Fin.natAdd (jj + 2) c).castSucc := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [stepReg, val_walkReg, val_natAdd_castSucc] at hv
  have := (L.toWalkLayout.reg (L.toWalkLayout.stepIdx second p)).isLt
  omega

theorem stepReg_ne_last (L : WalkWidths kk jj tm nn S wc) (second : Bool) (p : ℕ) :
    stepReg (r := r) L second p ≠ Fin.last (jj + 2 + r) :=
  walkReg_ne_last _

theorem stepReg_inj (L : WalkWidths kk jj tm nn S wc) (second : Bool) :
    ∀ p q, p < L.toWalkLayout.stepBlocks → q < L.toWalkLayout.stepBlocks →
      (stepReg (r := r) L second p : Fin (jj + 2 + r + 1)) = stepReg L second q → p = q := by
  intro p q hp hq h
  have hidx := walkReg_reg_inj (r := r) L _ _ (L.toWalkLayout.stepIdx_lt second p hp)
    (L.toWalkLayout.stepIdx_lt second q hq) h
  exact L.toWalkLayout.stepIdx_inj second p q hp hq hidx

/-! ## The accumulator -/

/-- An auxiliary tape, as a tape index of the walk's layout. -/
def auxIdx (jj : ℕ) (c : Fin r) : Fin (jj + 2 + r + 1) := (Fin.natAdd (jj + 2) c).castSucc

theorem auxIdx_ne_castAdd (c : Fin r) (i : Fin (jj + 2)) :
    auxIdx jj c ≠ (Fin.castAdd r i).castSucc := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [auxIdx, val_natAdd_castSucc, val_castAdd_castSucc] at hv
  have := i.isLt
  omega

theorem auxIdx_ne_last (c : Fin r) : auxIdx jj c ≠ Fin.last (jj + 2 + r) := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [auxIdx, val_natAdd_castSucc] at hv
  have h2 : (Fin.last (jj + 2 + r) : Fin (jj + 2 + r + 1)).val = jj + 2 + r := rfl
  have := c.isLt
  omega

theorem walkReg_ne_auxIdx (i : Fin (jj + 1)) (c : Fin r) :
    (walkReg (r := r) i : Fin (jj + 2 + r + 1)) ≠ auxIdx jj c := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [val_walkReg, auxIdx, val_natAdd_castSucc] at hv
  have := i.isLt
  omega

/-! ## The head bound after a guess stage -/

/-- **How far a guess stage moves a head.** A scanned tape that the stage writes ends at
`1 + width + 1`; one it does not write stays where it was. So one bound covers them all. -/
theorem head_guessBlocksTapes_le (L : WalkWidths kk jj tm nn S wc) (second : Bool)
    (W₀ : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W₀ i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W₀ i).head)
    (hone : ∀ i : Fin (jj + 2), (W₀ (Fin.castAdd r i).castSucc).head = 1)
    (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B) :
    ∀ i ∈ stepTargets jj r,
      (TM.guessBlocksTapes (stepReg (r := r) L second) (stepWidth L)
        L.toWalkLayout.stepBlocks W₀ i.castSucc).head ≤ B := by
  classical
  intro i hi
  rw [stepTargets, List.mem_map] at hi
  obtain ⟨i, -, rfl⟩ := hi
  obtain ⟨-, -, -, huntouched, hblk⟩ :=
    TM.guessBlocksTapes_spec (stepReg (r := r) L second) (stepReg_ne_last L second)
      (stepWidth L) L.toWalkLayout.stepBlocks W₀ hinv hh (stepReg_inj L second)
  by_cases hex : ∃ p, p < L.toWalkLayout.stepBlocks ∧
      stepReg (r := r) L second p = (Fin.castAdd r i).castSucc
  · obtain ⟨p, hp, hpi⟩ := hex
    have hhead := (hblk p hp).1
    rw [hpi] at hhead
    rw [hhead, hone i]
    have := hB p hp
    omega
  · rw [huntouched (Fin.castAdd r i).castSucc (by
      intro hc
      exact absurd (congrArg Fin.val hc) (by
        have h1 : ((Fin.castAdd r i).castSucc : Fin (jj + 2 + r + 1)).val = i.val := rfl
        have h2 : (Fin.last (jj + 2 + r) : Fin (jj + 2 + r + 1)).val = jj + 2 + r := rfl
        have := i.isLt
        omega))
      (fun p hp hc => hex ⟨p, hp, hc.symm⟩), hone i]
    exact hB1

/-! ## The scan's boundary conditions -/

theorem read_parkTape_ne_start {t : Tape} (h : t.StartInvariant) :
    (TM.parkTape t).read ≠ Γ.start := by
  show t.cells (max t.head 1) ≠ Γ.start
  exact h.2 _ (le_max_right _ _)

/-- **The three heads a scan needs off the left marker**, after a step's guess stage. -/
theorem scanOk_of_step (L : WalkWidths kk jj tm nn S wc) (second : Bool)
    (W₀ : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W₀ i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W₀ i).head) (inp₀ out₀ : Tape)
    (hinpSI : inp₀.StartInvariant) (houtSI : out₀.StartInvariant) :
    TM.ScanOk (TM.parkTape inp₀)
      (⟨1, (TM.guessBlocksTapes (stepReg (r := r) L second) (stepWidth L)
        L.toWalkLayout.stepBlocks W₀ (Fin.castAdd r (Fin.last (jj + 1))).castSucc).cells⟩ : Tape)
      (TM.parkTape out₀) where
  inp := read_parkTape_ne_start hinpSI
  res := by
    have hSI := (TM.guessBlocksTapes_spec (stepReg (r := r) L second) (stepReg_ne_last L second)
      (stepWidth L) L.toWalkLayout.stepBlocks W₀ hinv hh (stepReg_inj L second)).1
      (Fin.castAdd r (Fin.last (jj + 1))).castSucc
    exact hSI.2 1 le_rfl
  out := read_parkTape_ne_start houtSI

/-! ## Distinct roles sit in distinct registers -/

namespace WalkLayout

variable (L : WalkLayout kk jj)

/-- **The verdict register is not register zero** — the ruler is, and it has a different role.
This is what `Complexity.scanTape_checked` needs. -/
theorem res_ne_zero : L.res ≠ 0 := by
  rw [← L.ruler_zero]
  exact L.reg_ne L.res_lt L.ruler_lt (by
    rw [L.role_res, L.role_ruler]
    exact fun hc => by simp at hc)

end WalkLayout

end Complexity
