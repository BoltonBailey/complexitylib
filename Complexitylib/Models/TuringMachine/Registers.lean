/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Subroutines.Counter

/-!
# Unary registers

A *register* is a work tape holding a natural number in unary: cells `1..v`
hold `1`, everything beyond is blank, and the head is parked at cell 1. All
arithmetic in the Cook–Levin reduction emitter (`docs/A5-ReductionEmitter.md`)
is over registers — the CNF encoding is unary, so no binary arithmetic is
ever needed.

`reg` strengthens `Tape.hasUnaryCounter` with the cell-0 sentinel and
all-blanks-beyond, making registers literally preserved by parked no-op
actions and stable under the combinator phase transitions.

## Main definitions

- `TM.Parked` — a tape whose head is off `▷` and which has no spurious `▷`s
- `TM.reg` — the register predicate

## Main results

- `TM.reg.parked`, `TM.reg.hasUnaryCounter` — bridges
- `TM.reg_zero_init` — a freshly bumped blank tape is `reg 0`
-/

namespace Complexity

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Parked tapes
-- ════════════════════════════════════════════════════════════════════════

/-- A tape parked for preservation: head off `▷` (so `idleDir` stays put and
    `δ_right_of_start` is moot) and no `▷` outside cell 0 (so `readBackWrite`
    writes back the read symbol verbatim). Machines that do not use a tape
    keep it parked and literally unchanged. -/
def Parked (t : Tape) : Prop :=
  1 ≤ t.head ∧ ∀ j, 1 ≤ j → t.cells j ≠ Γ.start

theorem Parked.read_ne_start {t : Tape} (h : Parked t) : t.read ≠ Γ.start :=
  h.2 t.head h.1

/-- A parked tape is untouched by the no-op action `writeAndMove (readBackWrite
    read) (idleDir read)`. -/
theorem Parked.writeAndMove_readBack_idle {t : Tape} (h : Parked t) :
    t.writeAndMove (readBackWrite t.read) (idleDir t.read) = t :=
  Tape.writeAndMove_readBack_idle_of_ne_start t h.read_ne_start

/-- A parked tape's head does not move under `idleDir`. -/
theorem Parked.move_idle {t : Tape} (h : Parked t) :
    t.move (idleDir t.read) = t := by
  rw [idleDir, if_neg h.read_ne_start]
  rfl

/-- Writing back the read symbol is a no-op (off `▷` the symbol round-trips;
    on `▷` the write is structurally void). -/
theorem write_readBack (t : Tape) (hread : t.read ≠ Γ.start) :
    t.write (readBackWrite t.read) = t := by
  rw [Tape.write]
  split
  · rfl
  · refine Tape.ext rfl ?_
    show Function.update t.cells t.head (readBackWrite t.read).toΓ = t.cells
    rw [readBackWrite_toΓ_eq hread, Tape.read, Function.update_eq_self]

/-- Writing back the read symbol and moving is just the move. -/
theorem writeAndMove_readBack (t : Tape) (hread : t.read ≠ Γ.start) (d : Dir3) :
    t.writeAndMove (readBackWrite t.read) d = t.move d := by
  show (t.write _).move d = t.move d
  rw [write_readBack t hread]

/-- Parked tapes pass through combinator phase boundaries unchanged. -/
theorem Parked.transitionTape_id {t : Tape} (h : Parked t) : transitionTape t = t :=
  TM.transitionTape_id h.read_ne_start

/-- Parked input tapes pass through combinator phase boundaries unchanged. -/
theorem Parked.transitionInput_id {t : Tape} (h : Parked t) : transitionInput t = t :=
  TM.transitionInput_id h.read_ne_start

-- ════════════════════════════════════════════════════════════════════════
-- Registers
-- ════════════════════════════════════════════════════════════════════════

/-- **Register.** The tape holds `v` in unary: `▷` at cell 0, `1` at cells
    `1..v`, blank everywhere beyond, head parked at cell 1. -/
def reg (v : ℕ) (t : Tape) : Prop :=
  t.head = 1 ∧
  t.cells 0 = Γ.start ∧
  (∀ i, i < v → t.cells (i + 1) = Γ.one) ∧
  (∀ j, v + 1 ≤ j → t.cells j = Γ.blank)

namespace reg

theorem head_eq {v : ℕ} {t : Tape} (h : reg v t) : t.head = 1 := h.1

theorem cell0 {v : ℕ} {t : Tape} (h : reg v t) : t.cells 0 = Γ.start := h.2.1

theorem cells_one {v : ℕ} {t : Tape} (h : reg v t) {i : ℕ} (hi : i < v) :
    t.cells (i + 1) = Γ.one := h.2.2.1 i hi

theorem cells_blank {v : ℕ} {t : Tape} (h : reg v t) {j : ℕ} (hj : v + 1 ≤ j) :
    t.cells j = Γ.blank := h.2.2.2 j hj

/-- Register cells off the sentinel are `1` or blank — never `▷`. -/
theorem cells_ne_start {v : ℕ} {t : Tape} (h : reg v t) {j : ℕ} (hj : 1 ≤ j) :
    t.cells j ≠ Γ.start := by
  rcases Nat.lt_or_ge j (v + 1) with hlt | hge
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [h.cells_one (by omega)]; decide
  · rw [h.cells_blank hge]; decide

/-- A register tape is parked. -/
theorem parked {v : ℕ} {t : Tape} (h : reg v t) : Parked t :=
  ⟨by rw [h.head_eq], fun _ hj => h.cells_ne_start hj⟩

/-- A register is a unary counter (the weaker shape used by the counter
    subroutines). -/
theorem hasUnaryCounter {v : ℕ} {t : Tape} (h : reg v t) :
    t.hasUnaryCounter v :=
  ⟨h.head_eq, fun _ hi => h.cells_one hi, h.cells_blank (le_refl _)⟩

/-- The register's read: `1` when nonempty, blank when zero. -/
theorem read_eq {v : ℕ} {t : Tape} (h : reg v t) :
    t.read = if v = 0 then Γ.blank else Γ.one := by
  rw [Tape.read, h.head_eq]
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [if_pos rfl]; exact h.cells_blank (le_refl _)
  · rw [if_neg (by omega)]; exact h.cells_one hv

end reg

/-- A blank tape with the head bumped to cell 1 is the zero register. -/
theorem reg_zero_init : reg 0 { head := 1, cells := (Tape.init []).cells } := by
  refine ⟨rfl, by simp [Tape.init], fun _ hi => by omega, fun j hj => ?_⟩
  show (Tape.init []).cells j = Γ.blank
  simp only [Tape.init]
  rw [if_neg (by omega : ¬ j = 0)]
  simp

-- ════════════════════════════════════════════════════════════════════════
-- The canonical register tape
-- ════════════════════════════════════════════════════════════════════════

/-- Canonical register cells holding `v` in unary. -/
def regCells (v : ℕ) : ℕ → Γ := fun j =>
  if j = 0 then Γ.start else if j ≤ v then Γ.one else Γ.blank

/-- The canonical register tape holding `v`. -/
def regT (v : ℕ) : Tape := ⟨1, regCells v⟩

@[simp] theorem regT_head (v : ℕ) : (regT v).head = 1 := rfl

@[simp] theorem regT_cells (v : ℕ) : (regT v).cells = regCells v := rfl

@[simp] theorem regCells_zero (v : ℕ) : regCells v 0 = Γ.start := rfl

theorem regCells_one {v j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ v) : regCells v j = Γ.one := by
  rw [regCells, if_neg (by omega), if_pos h2]

theorem regCells_blank {v j : ℕ} (h : v + 1 ≤ j) : regCells v j = Γ.blank := by
  rw [regCells, if_neg (by omega), if_neg (by omega)]

/-- Register cells away from the sentinel are never `▷`. -/
theorem regCells_ne_start {v j : ℕ} (hj : 1 ≤ j) :
    regCells v j ≠ Γ.start := by
  rw [regCells, if_neg (by omega)]
  split <;> decide

theorem reg_regT (v : ℕ) : reg v (regT v) :=
  ⟨rfl, rfl, fun _ hi => by rw [regT_cells]; exact regCells_one (by omega) (by omega),
   fun _ hj => by rw [regT_cells]; exact regCells_blank hj⟩

/-- **A register's tape is canonical**: the `reg` predicate pins every cell and
    the head, so it is an equation. -/
theorem reg.eq_regT {v : ℕ} {t : Tape} (h : reg v t) : t = regT v := by
  refine Tape.ext h.head_eq ?_
  funext j
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [h.cell0]; rfl
  · rcases Nat.lt_or_ge v j with hlt | hge
    · rw [h.cells_blank (by omega), regT_cells]
      exact (regCells_blank (by omega)).symm
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [h.cells_one (by omega), regT_cells]
      exact (regCells_one (by omega) (by omega)).symm

theorem regT_parked (v : ℕ) : Parked (regT v) := (reg_regT v).parked

/-- Register cells with the head anywhere off `▷` form a parked tape. -/
theorem parked_regCells {h v : ℕ} (hh : 1 ≤ h) :
    Parked (⟨h, regCells v⟩ : Tape) := by
  exact ⟨hh, fun _ hj => regCells_ne_start hj⟩

/-- Writing the next mark turns `regCells d` into `regCells (d + 1)`. -/
theorem regCells_update_succ (d : ℕ) :
    Function.update (regCells d) (d + 1) Γ.one = regCells (d + 1) := by
  funext j
  rw [Function.update_apply]
  split
  · next h =>
    subst h
    exact (regCells_one (by omega) (by omega)).symm
  · next h =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rfl
    · rcases Nat.lt_or_ge d j with hlt | hge
      · rw [regCells_blank (by omega), regCells_blank (by omega)]
      · rw [regCells_one (by omega) (by omega), regCells_one (by omega) (by omega)]

/-- Erasing the final mark turns `regCells (d + 1)` into `regCells d`. -/
theorem regCells_erase (d : ℕ) :
    Function.update (regCells (d + 1)) (d + 1) Γ.blank = regCells d := by
  funext j
  rw [Function.update_apply]
  split
  · next hj =>
    subst hj
    exact (regCells_blank (by omega)).symm
  · next hj =>
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · rfl
    · rcases Nat.lt_or_ge d j with hlt | hge
      · rw [regCells_blank (by omega), regCells_blank (by omega)]
      · rw [regCells_one (by omega) (by omega), regCells_one (by omega) (by omega)]

end TM

end Complexity
