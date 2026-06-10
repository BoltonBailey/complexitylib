import Complexitylib.Models.TuringMachine.CounterSubroutines

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

/-- Tapes are equal when their heads and cells agree. -/
theorem Tape.ext' {a b : Tape} (hhead : a.head = b.head) (hcells : a.cells = b.cells) :
    a = b := by
  cases a; cases b; cases hhead; cases hcells; rfl

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
  · refine Tape.ext' rfl ?_
    show Function.update t.cells t.head (readBackWrite t.read).toΓ = t.cells
    rw [readBackWrite_toΓ_eq hread, Tape.read, Function.update_eq_self]

/-- Writing back the read symbol and moving is just the move. -/
theorem writeAndMove_readBack (t : Tape) (hread : t.read ≠ Γ.start) (d : Dir3) :
    t.writeAndMove (readBackWrite t.read) d = t.move d := by
  show (t.write _).move d = t.move d
  rw [write_readBack t hread]

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
theorem reg_zero_init : reg 0 { head := 1, cells := (initTape []).cells } := by
  refine ⟨rfl, by simp [initTape], fun _ hi => by omega, fun j hj => ?_⟩
  show (initTape []).cells j = Γ.blank
  simp only [initTape]
  rw [if_neg (by omega : ¬ j = 0)]
  simp

end TM
