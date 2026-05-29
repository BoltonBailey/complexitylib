import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
import Complexitylib.Models.TuringMachine.Hoare.Defs

/-!
# Counter-building TM subroutines

Deterministic helper machines for materializing unary counters on work tapes.

The SAT-specific NP construction only needs a linear witness bound:
`assignment.length ≤ input.length + 1`. This file defines a small machine
that writes exactly `|input| + 1` unary marks to a designated counter tape.
-/

namespace Tape

/-- A counter tape while it is being built: cells `1..used` contain unary
    marks, the head is at cell `used + 1`, and the tail from that cell onward
    is blank. -/
def hasUnaryPrefix (t : Tape) (used : ℕ) : Prop :=
  t.head = used + 1 ∧
  (∀ i, i < used → t.cells (i + 1) = Γ.one) ∧
  (∀ i, used ≤ i → t.cells (i + 1) = Γ.blank)

theorem initTape_nil_move_right_hasUnaryPrefix_zero :
    ((_root_.initTape []).move Dir3.right).hasUnaryPrefix 0 := by
  simp [hasUnaryPrefix, _root_.initTape, Tape.move]

/-- Writing one mark at the current head and moving right extends a unary
    prefix by one cell. -/
theorem hasUnaryPrefix_write_one {t : Tape} {used : ℕ}
    (h : t.hasUnaryPrefix used) :
    (t.writeAndMove Γ.one Dir3.right).hasUnaryPrefix (used + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Tape.writeAndMove, Tape.write, Tape.move, h.1]
  · intro i hi
    unfold Tape.writeAndMove
    simp only [Tape.move]
    unfold Tape.write
    have hhead_ne : ¬t.head = 0 := by rw [h.1]; omega
    simp only [hhead_ne, ↓reduceIte]
    by_cases hidx : i = used
    · have hcellidx : i + 1 = t.head := by rw [h.1, hidx]
      rw [hcellidx, Function.update_self]
    · have hi_used : i < used := by omega
      have hcell := h.2.1 i hi_used
      have hne : t.head ≠ i + 1 := by rw [h.1]; omega
      rw [Function.update_of_ne (Ne.symm hne)]
      exact hcell
  · intro i hi
    unfold Tape.writeAndMove
    simp only [Tape.move]
    unfold Tape.write
    have hhead_ne : ¬t.head = 0 := by rw [h.1]; omega
    simp only [hhead_ne, ↓reduceIte]
    have hne : t.head ≠ i + 1 := by rw [h.1]; omega
    rw [Function.update_of_ne (Ne.symm hne)]
    exact h.2.2 i (by omega)

/-- Writing the next unary mark preserves the left-end marker cell. -/
theorem hasUnaryPrefix_write_one_cell0 {t : Tape} {used : ℕ}
    (h : t.hasUnaryPrefix used) (h0 : t.cells 0 = Γ.start) :
    (t.writeAndMove Γ.one Dir3.right).cells 0 = Γ.start := by
  unfold Tape.writeAndMove
  rw [TM.tape_move_cells]
  unfold Tape.write
  have hhead_ne : ¬t.head = 0 := by rw [h.1]; omega
  simp only [hhead_ne, ↓reduceIte]
  have hne : t.head ≠ 0 := by rw [h.1]; omega
  rw [Function.update_of_ne (Ne.symm hne)]
  exact h0

/-- A unary prefix never contains `▷` after the left-end marker. -/
theorem hasUnaryPrefix_cells_ne_start {t : Tape} {used : ℕ}
    (h : t.hasUnaryPrefix used) :
    ∀ j, j ≥ 1 → t.cells j ≠ Γ.start := by
  intro j hj
  let i := j - 1
  have hj_eq : j = i + 1 := by omega
  by_cases hi : i < used
  · rw [hj_eq, h.2.1 i hi]
    decide
  · have hge : used ≤ i := by omega
    rw [hj_eq, h.2.2 i hge]
    decide

/-- A unary counter tape positioned at its first data cell.

`hasUnaryCounter t B` means cells `1..B` contain `1`, cell `B+1` is blank,
and the head is at cell `1`. -/
def hasUnaryCounter (t : Tape) (B : ℕ) : Prop :=
  t.head = 1 ∧
  (∀ i, i < B → t.cells (i + 1) = Γ.one) ∧
  t.cells (B + 1) = Γ.blank

/-- Rewinding a built unary prefix to cell 1 yields the public counter shape. -/
theorem hasUnaryPrefix_to_hasUnaryCounter {t t' : Tape} {B : ℕ}
    (hprefix : t.hasUnaryPrefix B)
    (hhead : t'.head = 1)
    (hcells : t'.cells = t.cells) :
    t'.hasUnaryCounter B := by
  refine ⟨hhead, ?_, ?_⟩
  · intro i hi
    rw [hcells]
    exact hprefix.2.1 i hi
  · rw [hcells]
    exact hprefix.2.2 B le_rfl

theorem hasUnaryCounter_read_zero {t : Tape}
    (h : t.hasUnaryCounter 0) : t.read = Γ.blank := by
  simp [Tape.read, h.1, h.2.2]

theorem hasUnaryCounter_read_pos {t : Tape} {B : ℕ}
    (h : t.hasUnaryCounter B) (hB : 0 < B) : t.read = Γ.one := by
  have hcell := h.2.1 0 hB
  simp [Tape.read, h.1, hcell]

/-- Counter shape after `used` marks have already been consumed. The head is
at the next unconsumed counter cell, previous cells are blanked, remaining
marks are `1`, and the first cell after the total bound is blank. -/
def hasCounterRemainder (t : Tape) (used total : ℕ) : Prop :=
  used ≤ total ∧
  t.head = used + 1 ∧
  (∀ i, i < used → t.cells (i + 1) = Γ.blank) ∧
  (∀ i, used ≤ i → i < total → t.cells (i + 1) = Γ.one) ∧
  t.cells (total + 1) = Γ.blank

theorem hasUnaryCounter_iff_remainder_zero {t : Tape} {B : ℕ} :
    t.hasUnaryCounter B ↔ t.hasCounterRemainder 0 B := by
  constructor
  · intro h
    refine ⟨Nat.zero_le B, h.1, ?_, ?_, h.2.2⟩
    · intro i hi
      omega
    · intro i _ hi
      exact h.2.1 i hi
  · intro h
    exact ⟨h.2.1, fun i hi => h.2.2.2.1 i (by omega) hi, h.2.2.2.2⟩

theorem hasCounterRemainder_read_blank_of_done {t : Tape} {B : ℕ}
    (h : t.hasCounterRemainder B B) : t.read = Γ.blank := by
  simp [Tape.read, h.2.1, h.2.2.2.2]

theorem hasCounterRemainder_read_one_of_remaining {t : Tape} {used total : ℕ}
    (h : t.hasCounterRemainder used total) (hlt : used < total) :
    t.read = Γ.one := by
  have hcell := h.2.2.2.1 used (le_rfl) hlt
  simp [Tape.read, h.2.1, hcell]

/-- Blanking the current counter mark and moving right advances the unary
    counter remainder by one. -/
theorem hasCounterRemainder_consume {t : Tape} {used total : ℕ}
    (h : t.hasCounterRemainder used total) (hlt : used < total) :
    (t.writeAndMove Γ.blank Dir3.right).hasCounterRemainder (used + 1) total := by
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · simp [Tape.writeAndMove, Tape.write, Tape.move, h.2.1]
  · intro i hi
    unfold Tape.writeAndMove
    simp only [Tape.move]
    unfold Tape.write
    have hhead_ne : ¬t.head = 0 := by rw [h.2.1]; omega
    simp only [hhead_ne, ↓reduceIte]
    by_cases hidx : i = used
    · have hcellidx : i + 1 = t.head := by rw [h.2.1, hidx]
      rw [hcellidx, Function.update_self]
    · have hi_used : i < used := by omega
      have hcell := h.2.2.1 i hi_used
      have hne : t.head ≠ i + 1 := by rw [h.2.1]; omega
      rw [Function.update_of_ne (Ne.symm hne)]
      exact hcell
  · intro i hge hltotal
    have hcell := h.2.2.2.1 i (by omega) hltotal
    unfold Tape.writeAndMove
    simp only [Tape.move]
    unfold Tape.write
    have hhead_ne : ¬t.head = 0 := by rw [h.2.1]; omega
    simp only [hhead_ne, ↓reduceIte]
    have hne : t.head ≠ i + 1 := by rw [h.2.1]; omega
    rw [Function.update_of_ne (Ne.symm hne)]
    exact hcell
  · unfold Tape.writeAndMove
    simp only [Tape.move]
    unfold Tape.write
    have hhead_ne : ¬t.head = 0 := by rw [h.2.1]; omega
    simp only [hhead_ne, ↓reduceIte]
    have hne : t.head ≠ total + 1 := by rw [h.2.1]; omega
    rw [Function.update_of_ne (Ne.symm hne)]
    exact h.2.2.2.2

/-- Writing back the currently read non-start symbol and idling preserves a
    tape. This is the basic preservation fact for non-active tapes in the
    counter and guessing machines. -/
theorem writeAndMove_readBack_idle_of_ne_start (t : Tape)
    (hread : t.read ≠ Γ.start) :
    t.writeAndMove (TM.readBackWrite t.read) (TM.idleDir t.read) = t := by
  have hback : (TM.readBackWrite t.read).toΓ = t.read := by
    cases h : t.read with
    | zero => rfl
    | one => rfl
    | blank => rfl
    | start => exact (hread h).elim
  have hdir : TM.idleDir t.read = Dir3.stay := by
    simp [TM.idleDir, hread]
  rw [hback]
  simp only [Tape.writeAndMove, hdir, Tape.move]
  by_cases h0 : t.head = 0
  · simp [Tape.write, h0]
  · simp [Tape.write, h0, Tape.read, Function.update_eq_self]

end Tape

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- Small alphabet / initTape helpers
-- ════════════════════════════════════════════════════════════════════════

/-- `Γ.ofBool b` is never the start symbol `▷`. -/
private theorem ofBool_ne_start (b : Bool) : Γ.ofBool b ≠ Γ.start := by
  cases b <;> simp [Γ.ofBool]

/-- `Γ.ofBool b` is never the blank symbol `□`. -/
private theorem ofBool_ne_blank (b : Bool) : Γ.ofBool b ≠ Γ.blank := by
  cases b <;> simp [Γ.ofBool]

/-- `initTape` cell-access at `i+1`. -/
private theorem initTape_cells_succ (l : List Γ) (i : ℕ) :
    (_root_.initTape l).cells (i + 1) = (l[i]?).getD Γ.blank := by
  show (if i + 1 = 0 then Γ.start else (l[i + 1 - 1]?).getD Γ.blank) = _
  simp

/-- `initTape (l.map Γ.ofBool)` cells at `i+1` for `i < |l|` equal `Γ.ofBool l[i]`. -/
private theorem initTape_ofBool_cells_lt (l : List Bool) (i : ℕ) (h : i < l.length) :
    (_root_.initTape (l.map Γ.ofBool)).cells (i + 1) = Γ.ofBool (l[i]'h) := by
  rw [initTape_cells_succ]
  have hmap : i < (l.map Γ.ofBool).length := by simp; exact h
  rw [List.getElem?_eq_getElem hmap]
  simp

/-- `initTape (l.map Γ.ofBool)` cells at `i+1` for `i ≥ |l|` equal `Γ.blank`. -/
private theorem initTape_ofBool_cells_ge (l : List Bool) (i : ℕ) (h : i ≥ l.length) :
    (_root_.initTape (l.map Γ.ofBool)).cells (i + 1) = Γ.blank := by
  rw [initTape_cells_succ]
  have hmap : (l.map Γ.ofBool).length ≤ i := by simp; exact h
  rw [List.getElem?_eq_none hmap]
  simp

private theorem initTape_ofBool_cells_ne_start (l : List Bool) (j : ℕ) (hj : j ≥ 1) :
    (_root_.initTape (l.map Γ.ofBool)).cells j ≠ Γ.start := by
  cases j with
  | zero =>
      omega
  | succ i =>
      by_cases hi : i < l.length
      · rw [initTape_ofBool_cells_lt l i hi]
        cases l[i]'hi <;> simp [Γ.ofBool]
      · have hge : i ≥ l.length := by omega
        rw [initTape_ofBool_cells_ge l i hge]
        simp

private theorem started_ofBool_tape_read_ne_start (x : List Bool) :
    (((_root_.initTape (x.map Γ.ofBool)).move Dir3.right).read) ≠ Γ.start := by
  simp [Tape.read, Tape.move]
  exact initTape_ofBool_cells_ne_start x 1 (by omega)

-- ════════════════════════════════════════════════════════════════════════
-- inputLengthPlusOneCounterTM
-- ════════════════════════════════════════════════════════════════════════

/-- Control states for `inputLengthPlusOneCounterTM`. -/
inductive LinearCounterPhase where
  | scan
  | rewind
  | done
  deriving DecidableEq

instance : Fintype LinearCounterPhase where
  elems := {.scan, .rewind, .done}
  complete := fun x => by cases x <;> simp

private def counterPreserveWork (wHeads : Fin n → Γ) : Fin n → Γw :=
  fun i => readBackWrite (wHeads i)

private def counterIdleDirs (wHeads : Fin n → Γ) : Fin n → Dir3 :=
  fun i => idleDir (wHeads i)

private theorem counterIdleDirs_right_of_start (wHeads : Fin n → Γ) :
    ∀ i, wHeads i = Γ.start → counterIdleDirs wHeads i = Dir3.right := by
  intro i hi
  exact idleDir_right_of_start hi

private def counterWriteOneWork (counterIdx : Fin n) (wHeads : Fin n → Γ) :
    Fin n → Γw :=
  fun i => if i = counterIdx then Γw.one else readBackWrite (wHeads i)

private def counterAdvanceDirs (counterIdx : Fin n) (wHeads : Fin n → Γ) :
    Fin n → Dir3 :=
  fun i => if i = counterIdx then Dir3.right else idleDir (wHeads i)

private theorem counterAdvanceDirs_right_of_start (counterIdx : Fin n)
    (wHeads : Fin n → Γ) :
    ∀ i, wHeads i = Γ.start → counterAdvanceDirs counterIdx wHeads i = Dir3.right := by
  intro i hi
  by_cases hidx : i = counterIdx
  · simp [counterAdvanceDirs, hidx]
  · simp [counterAdvanceDirs, hidx, idleDir_right_of_start hi]

private def counterRewindDirs (counterIdx : Fin n) (wHeads : Fin n → Γ) :
    Fin n → Dir3 :=
  fun i => if i = counterIdx then moveLeftDir (wHeads i) else idleDir (wHeads i)

private theorem moveLeftDir_right_of_start' {g : Γ} (h : g = Γ.start) :
    moveLeftDir g = Dir3.right := by
  subst h
  rfl

private theorem counterRewindDirs_right_of_start (counterIdx : Fin n)
    (wHeads : Fin n → Γ) :
    ∀ i, wHeads i = Γ.start → counterRewindDirs counterIdx wHeads i = Dir3.right := by
  intro i hi
  by_cases hidx : i = counterIdx
  · subst hidx
    simp [counterRewindDirs, moveLeftDir_right_of_start' hi]
  · simp [counterRewindDirs, hidx, idleDir_right_of_start hi]

private theorem counterRightOfStart_idle (iHead : Γ) (wHeads : Fin n → Γ) (oHead : Γ) :
    (iHead = Γ.start → idleDir iHead = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → counterIdleDirs wHeads i = Dir3.right) ∧
    (oHead = Γ.start → idleDir oHead = Dir3.right) :=
  ⟨idleDir_right_of_start, counterIdleDirs_right_of_start wHeads,
    idleDir_right_of_start⟩

private theorem counterRightOfStart_advance (counterIdx : Fin n)
    (iHead : Γ) (wHeads : Fin n → Γ) (oHead : Γ) :
    (iHead = Γ.start → Dir3.right = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → counterAdvanceDirs counterIdx wHeads i = Dir3.right) ∧
    (oHead = Γ.start → idleDir oHead = Dir3.right) :=
  ⟨fun _ => rfl, counterAdvanceDirs_right_of_start counterIdx wHeads,
    idleDir_right_of_start⟩

private theorem counterRightOfStart_scanStart
    (iHead : Γ) (wHeads : Fin n → Γ) (oHead : Γ) :
    (iHead = Γ.start → Dir3.right = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → counterIdleDirs wHeads i = Dir3.right) ∧
    (oHead = Γ.start → idleDir oHead = Dir3.right) :=
  ⟨fun _ => rfl, counterIdleDirs_right_of_start wHeads, idleDir_right_of_start⟩

private theorem counterRightOfStart_idleInput_advance (counterIdx : Fin n)
    (iHead : Γ) (wHeads : Fin n → Γ) (oHead : Γ) :
    (iHead = Γ.start → idleDir iHead = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → counterAdvanceDirs counterIdx wHeads i = Dir3.right) ∧
    (oHead = Γ.start → idleDir oHead = Dir3.right) :=
  ⟨idleDir_right_of_start, counterAdvanceDirs_right_of_start counterIdx wHeads,
    idleDir_right_of_start⟩

private theorem counterRightOfStart_rewind (counterIdx : Fin n)
    (iHead : Γ) (wHeads : Fin n → Γ) (oHead : Γ) :
    (iHead = Γ.start → idleDir iHead = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → counterRewindDirs counterIdx wHeads i = Dir3.right) ∧
    (oHead = Γ.start → idleDir oHead = Dir3.right) :=
  ⟨idleDir_right_of_start, counterRewindDirs_right_of_start counterIdx wHeads,
    idleDir_right_of_start⟩

/-- Write a unary counter of length `|input| + 1` to `counterIdx`.

Starting with the input head on `▷` and an empty counter tape, the `scan`
phase skips the input start cell, writes one counter mark per input bit,
then writes one extra mark when the input head reaches blank. The `rewind`
phase rewinds the counter tape to cell 1 and halts.

The machine does not try to restore the input head; later composition layers
can rewind or retarget input as needed. -/
def inputLengthPlusOneCounterTM (counterIdx : Fin n) : TM n where
  Q := LinearCounterPhase
  qstart := .scan
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .scan =>
      if iHead = Γ.start then
        (.scan, counterPreserveWork wHeads, readBackWrite oHead,
          Dir3.right, counterIdleDirs wHeads, idleDir oHead)
      else if iHead = Γ.blank then
        (.rewind, counterWriteOneWork counterIdx wHeads, readBackWrite oHead,
          idleDir iHead, counterAdvanceDirs counterIdx wHeads, idleDir oHead)
      else
        (.scan, counterWriteOneWork counterIdx wHeads, readBackWrite oHead,
          Dir3.right, counterAdvanceDirs counterIdx wHeads, idleDir oHead)
    | .rewind =>
      if wHeads counterIdx = Γ.start then
        (.done, counterPreserveWork wHeads, readBackWrite oHead,
          idleDir iHead, counterAdvanceDirs counterIdx wHeads, idleDir oHead)
      else
        (.rewind, counterPreserveWork wHeads, readBackWrite oHead,
          idleDir iHead, counterRewindDirs counterIdx wHeads, idleDir oHead)
    | .done =>
      (.done, counterPreserveWork wHeads, readBackWrite oHead,
        idleDir iHead, counterIdleDirs wHeads, idleDir oHead)
  δ_right_of_start := by
    intro state iHead wHeads oHead
    cases state
    · by_cases hiStart : iHead = Γ.start
      · simpa [hiStart] using counterRightOfStart_scanStart iHead wHeads oHead
      · by_cases hiBlank : iHead = Γ.blank
        · simpa [hiStart, hiBlank] using
            counterRightOfStart_idleInput_advance counterIdx iHead wHeads oHead
        · simpa [hiStart, hiBlank] using
            counterRightOfStart_advance counterIdx iHead wHeads oHead
    · by_cases hcounter : wHeads counterIdx = Γ.start
      · simpa [hcounter] using
          counterRightOfStart_idleInput_advance counterIdx iHead wHeads oHead
      · simpa [hcounter] using
          counterRightOfStart_rewind counterIdx iHead wHeads oHead
    · exact counterRightOfStart_idle iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- One-step transition API
-- ════════════════════════════════════════════════════════════════════════

theorem inputLengthPlusOneCounterTM_scan_start_state
    (counterIdx : Fin n) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hinp : inp.read = Γ.start) :
    (((inputLengthPlusOneCounterTM counterIdx).step
      { state := LinearCounterPhase.scan, input := inp, work := work, output := out }).get
        (by simp [TM.step, inputLengthPlusOneCounterTM])).state =
      LinearCounterPhase.scan := by
  simp [TM.step, inputLengthPlusOneCounterTM, hinp]

/-- The start-skip step positions an initially empty counter tape at cell 1,
    giving the zero-length unary-prefix invariant. -/
theorem inputLengthPlusOneCounterTM_scan_start_initializes_counter
    (counterIdx : Fin n) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hinp : inp.read = Γ.start)
    (hcounter : work counterIdx = _root_.initTape []) :
    ((((inputLengthPlusOneCounterTM counterIdx).step
      { state := LinearCounterPhase.scan, input := inp, work := work, output := out }).get
        (by simp [TM.step, inputLengthPlusOneCounterTM])).work counterIdx).hasUnaryPrefix 0 := by
  simp [TM.step, inputLengthPlusOneCounterTM, hinp, counterPreserveWork,
    counterIdleDirs, hcounter]
  simpa [Tape.writeAndMove, Tape.write] using
    Tape.initTape_nil_move_right_hasUnaryPrefix_zero

theorem inputLengthPlusOneCounterTM_scan_blank_state
    (counterIdx : Fin n) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hinp : inp.read = Γ.blank) :
    (((inputLengthPlusOneCounterTM counterIdx).step
      { state := LinearCounterPhase.scan, input := inp, work := work, output := out }).get
        (by simp [TM.step, inputLengthPlusOneCounterTM])).state =
      LinearCounterPhase.rewind := by
  simp [TM.step, inputLengthPlusOneCounterTM, hinp]

theorem inputLengthPlusOneCounterTM_scan_bit_state
    (counterIdx : Fin n) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hstart : inp.read ≠ Γ.start) (hblank : inp.read ≠ Γ.blank) :
    (((inputLengthPlusOneCounterTM counterIdx).step
      { state := LinearCounterPhase.scan, input := inp, work := work, output := out }).get
        (by simp [TM.step, inputLengthPlusOneCounterTM])).state =
      LinearCounterPhase.scan := by
  simp [TM.step, inputLengthPlusOneCounterTM, hstart, hblank]

/-- Scanning an input bit writes one unary mark and advances the counter
    prefix by one. -/
theorem inputLengthPlusOneCounterTM_scan_bit_extends_counter
    (counterIdx : Fin n) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    {used : ℕ}
    (hprefix : (work counterIdx).hasUnaryPrefix used)
    (hstart : inp.read ≠ Γ.start) (hblank : inp.read ≠ Γ.blank) :
    ((((inputLengthPlusOneCounterTM counterIdx).step
      { state := LinearCounterPhase.scan, input := inp, work := work, output := out }).get
        (by simp [TM.step, inputLengthPlusOneCounterTM])).work counterIdx).hasUnaryPrefix
      (used + 1) := by
  simp [TM.step, inputLengthPlusOneCounterTM, hstart, hblank,
    counterWriteOneWork, counterAdvanceDirs, Tape.hasUnaryPrefix_write_one hprefix]

/-- Scanning the input blank writes the final extra unary mark and enters the
    rewind phase. -/
theorem inputLengthPlusOneCounterTM_scan_blank_extends_counter
    (counterIdx : Fin n) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    {used : ℕ}
    (hprefix : (work counterIdx).hasUnaryPrefix used)
    (hinp : inp.read = Γ.blank) :
    ((((inputLengthPlusOneCounterTM counterIdx).step
      { state := LinearCounterPhase.scan, input := inp, work := work, output := out }).get
        (by simp [TM.step, inputLengthPlusOneCounterTM])).work counterIdx).hasUnaryPrefix
      (used + 1) := by
  have hstart : inp.read ≠ Γ.start := by rw [hinp]; simp
  simp [TM.step, inputLengthPlusOneCounterTM, hinp,
    counterWriteOneWork, counterAdvanceDirs, Tape.hasUnaryPrefix_write_one hprefix]

theorem inputLengthPlusOneCounterTM_rewind_start_state
    (counterIdx : Fin n) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hcounter : (work counterIdx).read = Γ.start) :
    (((inputLengthPlusOneCounterTM counterIdx).step
      { state := LinearCounterPhase.rewind, input := inp, work := work, output := out }).get
        (by simp [TM.step, inputLengthPlusOneCounterTM])).state =
      LinearCounterPhase.done := by
  simp [TM.step, inputLengthPlusOneCounterTM, hcounter]

theorem inputLengthPlusOneCounterTM_rewind_left_state
    (counterIdx : Fin n) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hcounter : (work counterIdx).read ≠ Γ.start) :
    (((inputLengthPlusOneCounterTM counterIdx).step
      { state := LinearCounterPhase.rewind, input := inp, work := work, output := out }).get
        (by simp [TM.step, inputLengthPlusOneCounterTM])).state =
      LinearCounterPhase.rewind := by
  simp [TM.step, inputLengthPlusOneCounterTM, hcounter]

theorem inputLengthPlusOneCounterTM_toNTM_trace_one_preserves_started_blank_other_work
    (counterIdx : Fin n) (choice : Bool)
    (c : Cfg n (inputLengthPlusOneCounterTM counterIdx).Q)
    (i : Fin n) (hi : i ≠ counterIdx)
    (hwork : c.work i = (_root_.initTape []).move Dir3.right) :
    (((inputLengthPlusOneCounterTM counterIdx).toNTM).trace 1
      (fun _ => choice) c).work i = (_root_.initTape []).move Dir3.right := by
  cases c with
  | mk state input work output =>
      change work i = (_root_.initTape []).move Dir3.right at hwork
      cases state
      · by_cases hstart : input.cells input.head = Γ.start
        · simp [NTM.trace, TM.toNTM, inputLengthPlusOneCounterTM, hstart,
            counterPreserveWork, counterIdleDirs, hwork, Tape.writeAndMove,
            Tape.write, Tape.move, Tape.read, readBackWrite, idleDir, _root_.initTape]
        · by_cases hblank : input.cells input.head = Γ.blank
          · simp [NTM.trace, TM.toNTM, inputLengthPlusOneCounterTM, hblank,
              counterWriteOneWork, counterAdvanceDirs, hwork, hi,
              Tape.writeAndMove, Tape.write, Tape.move, Tape.read, readBackWrite,
              idleDir, _root_.initTape]
          · simp [NTM.trace, TM.toNTM, inputLengthPlusOneCounterTM, hstart, hblank,
              counterWriteOneWork, counterAdvanceDirs, hwork, hi,
              Tape.writeAndMove, Tape.write, Tape.move, Tape.read, readBackWrite,
              idleDir, _root_.initTape]
      · by_cases hcounter : (work counterIdx).cells (work counterIdx).head = Γ.start
        · simp [NTM.trace, TM.toNTM, inputLengthPlusOneCounterTM, hcounter,
            counterPreserveWork, counterAdvanceDirs, hwork, hi, Tape.writeAndMove,
            Tape.write, Tape.move, Tape.read, readBackWrite, idleDir, _root_.initTape]
        · simp [NTM.trace, TM.toNTM, inputLengthPlusOneCounterTM, hcounter,
            counterPreserveWork, counterRewindDirs, hwork, hi, Tape.writeAndMove,
            Tape.write, Tape.move, Tape.read, readBackWrite, idleDir, _root_.initTape]
      · simp [NTM.trace, TM.toNTM, inputLengthPlusOneCounterTM, hwork]

theorem inputLengthPlusOneCounterTM_toNTM_trace_one_initializes_blank_other_work
    (counterIdx : Fin n) (choice : Bool)
    (c : Cfg n (inputLengthPlusOneCounterTM counterIdx).Q)
    (i : Fin n) (hi : i ≠ counterIdx)
    (hstate : c.state ≠ LinearCounterPhase.done)
    (hwork : c.work i = _root_.initTape []) :
    (((inputLengthPlusOneCounterTM counterIdx).toNTM).trace 1
      (fun _ => choice) c).work i = (_root_.initTape []).move Dir3.right := by
  cases c with
  | mk state input work output =>
      change work i = _root_.initTape [] at hwork
      cases state
      · by_cases hstart : input.cells input.head = Γ.start
        · simp [NTM.trace, TM.toNTM, inputLengthPlusOneCounterTM, hstart,
            counterPreserveWork, counterIdleDirs, hwork, Tape.writeAndMove,
            Tape.write, Tape.move, Tape.read, readBackWrite, idleDir, _root_.initTape]
        · by_cases hblank : input.cells input.head = Γ.blank
          · simp [NTM.trace, TM.toNTM, inputLengthPlusOneCounterTM, hblank,
              counterWriteOneWork, counterAdvanceDirs, hwork, hi,
              Tape.writeAndMove, Tape.write, Tape.move, Tape.read, readBackWrite,
              idleDir, _root_.initTape]
          · simp [NTM.trace, TM.toNTM, inputLengthPlusOneCounterTM, hstart, hblank,
              counterWriteOneWork, counterAdvanceDirs, hwork, hi,
              Tape.writeAndMove, Tape.write, Tape.move, Tape.read, readBackWrite,
              idleDir, _root_.initTape]
      · by_cases hcounter : (work counterIdx).cells (work counterIdx).head = Γ.start
        · simp [NTM.trace, TM.toNTM, inputLengthPlusOneCounterTM, hcounter,
            counterPreserveWork, counterAdvanceDirs, hwork, hi, Tape.writeAndMove,
            Tape.write, Tape.move, Tape.read, readBackWrite, idleDir, _root_.initTape]
        · simp [NTM.trace, TM.toNTM, inputLengthPlusOneCounterTM, hcounter,
            counterPreserveWork, counterRewindDirs, hwork, hi, Tape.writeAndMove,
            Tape.write, Tape.move, Tape.read, readBackWrite, idleDir, _root_.initTape]
      · exact (hstate rfl).elim

theorem inputLengthPlusOneCounterTM_toNTM_trace_one_preserves_started_blank_output
    (counterIdx : Fin n) (choice : Bool)
    (c : Cfg n (inputLengthPlusOneCounterTM counterIdx).Q)
    (houtput : c.output = (_root_.initTape []).move Dir3.right) :
    (((inputLengthPlusOneCounterTM counterIdx).toNTM).trace 1
      (fun _ => choice) c).output = (_root_.initTape []).move Dir3.right := by
  cases c with
  | mk state input work output =>
      change output = (_root_.initTape []).move Dir3.right at houtput
      cases state
      · by_cases hstart : input.cells input.head = Γ.start
        · simp [NTM.trace, TM.toNTM, inputLengthPlusOneCounterTM, hstart,
            houtput, Tape.writeAndMove, Tape.write, Tape.move, Tape.read,
            readBackWrite, idleDir, _root_.initTape]
        · by_cases hblank : input.cells input.head = Γ.blank
          · simp [NTM.trace, TM.toNTM, inputLengthPlusOneCounterTM, hblank,
              houtput, Tape.writeAndMove, Tape.write, Tape.move, Tape.read,
              readBackWrite, idleDir, _root_.initTape]
          · simp [NTM.trace, TM.toNTM, inputLengthPlusOneCounterTM, hstart, hblank,
              houtput, Tape.writeAndMove, Tape.write, Tape.move, Tape.read,
              readBackWrite, idleDir, _root_.initTape]
      · by_cases hcounter : (work counterIdx).cells (work counterIdx).head = Γ.start
        · simp [NTM.trace, TM.toNTM, inputLengthPlusOneCounterTM, hcounter,
            houtput, Tape.writeAndMove, Tape.write, Tape.move, Tape.read,
            readBackWrite, idleDir, _root_.initTape]
        · simp [NTM.trace, TM.toNTM, inputLengthPlusOneCounterTM, hcounter,
            houtput, Tape.writeAndMove, Tape.write, Tape.move, Tape.read,
            readBackWrite, idleDir, _root_.initTape]
      · simp [NTM.trace, TM.toNTM, inputLengthPlusOneCounterTM, houtput]

theorem inputLengthPlusOneCounterTM_toNTM_trace_one_initializes_blank_output
    (counterIdx : Fin n) (choice : Bool)
    (c : Cfg n (inputLengthPlusOneCounterTM counterIdx).Q)
    (hstate : c.state ≠ LinearCounterPhase.done)
    (houtput : c.output = _root_.initTape []) :
    (((inputLengthPlusOneCounterTM counterIdx).toNTM).trace 1
      (fun _ => choice) c).output = (_root_.initTape []).move Dir3.right := by
  cases c with
  | mk state input work output =>
      change output = _root_.initTape [] at houtput
      cases state
      · by_cases hstart : input.cells input.head = Γ.start
        · simp [NTM.trace, TM.toNTM, inputLengthPlusOneCounterTM, hstart,
            houtput, Tape.writeAndMove, Tape.write, Tape.move, Tape.read,
            readBackWrite, idleDir, _root_.initTape]
        · by_cases hblank : input.cells input.head = Γ.blank
          · simp [NTM.trace, TM.toNTM, inputLengthPlusOneCounterTM, hblank,
              houtput, Tape.writeAndMove, Tape.write, Tape.move, Tape.read,
              readBackWrite, idleDir, _root_.initTape]
          · simp [NTM.trace, TM.toNTM, inputLengthPlusOneCounterTM, hstart, hblank,
              houtput, Tape.writeAndMove, Tape.write, Tape.move, Tape.read,
              readBackWrite, idleDir, _root_.initTape]
      · by_cases hcounter : (work counterIdx).cells (work counterIdx).head = Γ.start
        · simp [NTM.trace, TM.toNTM, inputLengthPlusOneCounterTM, hcounter,
            houtput, Tape.writeAndMove, Tape.write, Tape.move, Tape.read,
            readBackWrite, idleDir, _root_.initTape]
        · simp [NTM.trace, TM.toNTM, inputLengthPlusOneCounterTM, hcounter,
            houtput, Tape.writeAndMove, Tape.write, Tape.move, Tape.read,
            readBackWrite, idleDir, _root_.initTape]
      · exact (hstate rfl).elim

-- ════════════════════════════════════════════════════════════════════════
-- Multi-step correctness for inputLengthPlusOneCounterTM
-- ════════════════════════════════════════════════════════════════════════

private theorem inputLengthPlusOneCounterTM_start_step
    (counterIdx : Fin n) (x : List Bool) (work : Fin n → Tape) (out : Tape)
    (hcounter : work counterIdx = _root_.initTape []) :
    ∃ c₁,
      (inputLengthPlusOneCounterTM counterIdx).step
        { state := LinearCounterPhase.scan,
          input := _root_.initTape (x.map Γ.ofBool),
          work := work, output := out } = some c₁ ∧
      c₁.state = LinearCounterPhase.scan ∧
      c₁.input.cells = (_root_.initTape (x.map Γ.ofBool)).cells ∧
      c₁.input.head = 1 ∧
      (c₁.work counterIdx).hasUnaryPrefix 0 ∧
      (c₁.work counterIdx).cells 0 = Γ.start := by
  have hread : (_root_.initTape (x.map Γ.ofBool)).read = Γ.start := by
    simp [Tape.read, _root_.initTape]
  simp [TM.step, inputLengthPlusOneCounterTM, hread]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [tape_move_cells]
  · simp [_root_.initTape, Tape.move]
  · have hcounter_read : (work counterIdx).read = Γ.start := by
      rw [hcounter]
      simp [Tape.read, _root_.initTape]
    simpa [counterPreserveWork, counterIdleDirs, hcounter, hcounter_read,
      Tape.writeAndMove, Tape.write] using
      Tape.initTape_nil_move_right_hasUnaryPrefix_zero
  · simp [counterIdleDirs, hcounter, Tape.writeAndMove, tape_move_cells,
      Tape.write, _root_.initTape]

private theorem inputLengthPlusOneCounterTM_scan_bit_step
    (counterIdx : Fin n) (x : List Bool) (k : ℕ)
    (c : Cfg n (inputLengthPlusOneCounterTM counterIdx).Q)
    (hk : k < x.length)
    (hstate : c.state = LinearCounterPhase.scan)
    (hinput_cells : c.input.cells = (_root_.initTape (x.map Γ.ofBool)).cells)
    (hinput_head : c.input.head = k + 1)
    (hprefix : (c.work counterIdx).hasUnaryPrefix k)
    (hcell0 : (c.work counterIdx).cells 0 = Γ.start) :
    ∃ c',
      (inputLengthPlusOneCounterTM counterIdx).step c = some c' ∧
      c'.state = LinearCounterPhase.scan ∧
      c'.input.cells = (_root_.initTape (x.map Γ.ofBool)).cells ∧
      c'.input.head = k + 2 ∧
      (c'.work counterIdx).hasUnaryPrefix (k + 1) ∧
      (c'.work counterIdx).cells 0 = Γ.start := by
  have hread : c.input.read = Γ.ofBool (x[k]'hk) := by
    show c.input.cells c.input.head = _
    rw [hinput_head, hinput_cells]
    exact initTape_ofBool_cells_lt x k hk
  have hstart : c.input.read ≠ Γ.start := by
    rw [hread]
    exact ofBool_ne_start _
  have hblank : c.input.read ≠ Γ.blank := by
    rw [hread]
    exact ofBool_ne_blank _
  simp only [TM.step, hstate, inputLengthPlusOneCounterTM, hstart, hblank]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [tape_move_cells]
    exact hinput_cells
  · simp [Tape.move, hinput_head]
  · simpa [counterWriteOneWork, counterAdvanceDirs] using
      Tape.hasUnaryPrefix_write_one hprefix
  · simpa [counterWriteOneWork, counterAdvanceDirs] using
      Tape.hasUnaryPrefix_write_one_cell0 hprefix hcell0

private theorem inputLengthPlusOneCounterTM_scan_bits_loop
    (counterIdx : Fin n) (x : List Bool) :
    ∀ (m k : ℕ) (c : Cfg n (inputLengthPlusOneCounterTM counterIdx).Q),
      k + m ≤ x.length →
      c.state = LinearCounterPhase.scan →
      c.input.cells = (_root_.initTape (x.map Γ.ofBool)).cells →
      c.input.head = k + 1 →
      (c.work counterIdx).hasUnaryPrefix k →
      (c.work counterIdx).cells 0 = Γ.start →
      ∃ c',
        (inputLengthPlusOneCounterTM counterIdx).reachesIn m c c' ∧
        c'.state = LinearCounterPhase.scan ∧
        c'.input.cells = (_root_.initTape (x.map Γ.ofBool)).cells ∧
        c'.input.head = k + m + 1 ∧
        (c'.work counterIdx).hasUnaryPrefix (k + m) ∧
        (c'.work counterIdx).cells 0 = Γ.start := by
  intro m
  induction m with
  | zero =>
    intro k c _ hstate hcells hhead hprefix hcell0
    refine ⟨c, .zero, hstate, hcells, ?_, ?_, hcell0⟩
    · omega
    · simpa using hprefix
  | succ m ih =>
    intro k c hle hstate hcells hhead hprefix hcell0
    have hk : k < x.length := by omega
    obtain ⟨c₁, hstep, hstate₁, hcells₁, hhead₁, hprefix₁, hcell0₁⟩ :=
      inputLengthPlusOneCounterTM_scan_bit_step counterIdx x k c hk hstate
        hcells hhead hprefix hcell0
    have hle₁ : (k + 1) + m ≤ x.length := by omega
    obtain ⟨c', hreach, hstate', hcells', hhead', hprefix', hcell0'⟩ :=
      ih (k + 1) c₁ hle₁ hstate₁ hcells₁ (by omega) hprefix₁ hcell0₁
    refine ⟨c', .step hstep hreach, hstate', hcells', ?_, ?_, hcell0'⟩
    · rw [hhead']
      omega
    · convert hprefix' using 1
      omega

private theorem inputLengthPlusOneCounterTM_scan_blank_step
    (counterIdx : Fin n) (x : List Bool)
    (c : Cfg n (inputLengthPlusOneCounterTM counterIdx).Q)
    (hstate : c.state = LinearCounterPhase.scan)
    (hinput_cells : c.input.cells = (_root_.initTape (x.map Γ.ofBool)).cells)
    (hinput_head : c.input.head = x.length + 1)
    (hprefix : (c.work counterIdx).hasUnaryPrefix x.length)
    (hcell0 : (c.work counterIdx).cells 0 = Γ.start) :
    ∃ c',
      (inputLengthPlusOneCounterTM counterIdx).step c = some c' ∧
      c'.state = LinearCounterPhase.rewind ∧
      c'.input = c.input ∧
      (c'.work counterIdx).hasUnaryPrefix (x.length + 1) ∧
      (c'.work counterIdx).cells 0 = Γ.start := by
  have hread : c.input.read = Γ.blank := by
    show c.input.cells c.input.head = _
    rw [hinput_head, hinput_cells]
    exact initTape_ofBool_cells_ge x x.length le_rfl
  simp only [TM.step, hstate, inputLengthPlusOneCounterTM, hread]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · simp [TM.idleDir, Tape.move]
  · simpa [counterWriteOneWork, counterAdvanceDirs] using
      Tape.hasUnaryPrefix_write_one hprefix
  · simpa [counterWriteOneWork, counterAdvanceDirs] using
      Tape.hasUnaryPrefix_write_one_cell0 hprefix hcell0

private theorem inputLengthPlusOneCounterTM_rewind_step_left
    (counterIdx : Fin n) (c : Cfg n (inputLengthPlusOneCounterTM counterIdx).Q)
    (hstate : c.state = LinearCounterPhase.rewind)
    (hinp : c.input.read ≠ Γ.start)
    (hread : (c.work counterIdx).read ≠ Γ.start)
    (_ : (c.work counterIdx).cells 0 = Γ.start)
    (_ : ∀ j, j ≥ 1 → (c.work counterIdx).cells j ≠ Γ.start) :
    ∃ c',
      (inputLengthPlusOneCounterTM counterIdx).step c = some c' ∧
      c'.state = LinearCounterPhase.rewind ∧
      c'.input = c.input ∧
      (c'.work counterIdx).head = (c.work counterIdx).head - 1 ∧
      (c'.work counterIdx).cells = (c.work counterIdx).cells := by
  simp only [TM.step, hstate, inputLengthPlusOneCounterTM, hread]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · show c.input.move (TM.idleDir c.input.read) = c.input
    exact TM.transitionInput_id hinp
  · by_cases h0 : (c.work counterIdx).head = 0
    · simp [counterRewindDirs, moveLeftDir, hread, Tape.writeAndMove, Tape.move,
        Tape.write, h0]
    · simp [counterRewindDirs, moveLeftDir, hread, Tape.writeAndMove, Tape.move,
        Tape.write, h0]
  · simp [counterRewindDirs, moveLeftDir, hread,
      Tape.writeAndMove, tape_move_cells]
    change ((c.work counterIdx).write
        ((readBackWrite (c.work counterIdx).read).toΓ)).cells =
      (c.work counterIdx).cells
    rw [readBackWrite_toΓ_eq hread]
    simp only [Tape.write, Tape.read]
    split
    · rfl
    · exact Function.update_eq_self _ _

private theorem inputLengthPlusOneCounterTM_rewind_step_base
    (counterIdx : Fin n) (c : Cfg n (inputLengthPlusOneCounterTM counterIdx).Q)
    (hstate : c.state = LinearCounterPhase.rewind)
    (hinp : c.input.read ≠ Γ.start)
    (hread : (c.work counterIdx).read = Γ.start)
    (_ : (c.work counterIdx).cells 0 = Γ.start)
    (hnostart : ∀ j, j ≥ 1 → (c.work counterIdx).cells j ≠ Γ.start) :
    ∃ c',
      (inputLengthPlusOneCounterTM counterIdx).step c = some c' ∧
      c'.state = LinearCounterPhase.done ∧
      c'.input = c.input ∧
      (c'.work counterIdx).head = 1 ∧
      (c'.work counterIdx).cells = (c.work counterIdx).cells := by
  have hhead : (c.work counterIdx).head = 0 := by
    by_contra h
    exact hnostart (c.work counterIdx).head (by omega) (by rwa [Tape.read] at hread)
  simp only [TM.step, hstate, inputLengthPlusOneCounterTM, hread]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · show c.input.move (TM.idleDir c.input.read) = c.input
    exact TM.transitionInput_id hinp
  · simp [counterAdvanceDirs, Tape.writeAndMove, Tape.move, Tape.write, hhead]
  · simp [counterAdvanceDirs, Tape.writeAndMove, tape_move_cells, Tape.write, hhead]

private theorem inputLengthPlusOneCounterTM_rewind_loop (counterIdx : Fin n) :
    ∀ (h : ℕ) (c : Cfg n (inputLengthPlusOneCounterTM counterIdx).Q),
      c.state = LinearCounterPhase.rewind →
      c.input.read ≠ Γ.start →
      (c.work counterIdx).cells 0 = Γ.start →
      (∀ j, j ≥ 1 → (c.work counterIdx).cells j ≠ Γ.start) →
      (c.work counterIdx).head = h →
      ∃ c',
        (inputLengthPlusOneCounterTM counterIdx).reachesIn (h + 1) c c' ∧
        (inputLengthPlusOneCounterTM counterIdx).halted c' ∧
        c'.input = c.input ∧
        (c'.work counterIdx).head = 1 ∧
        (c'.work counterIdx).cells = (c.work counterIdx).cells := by
  intro h
  induction h with
  | zero =>
      intro c hstate hinp hcell0 hnostart hhead
      have hread : (c.work counterIdx).read = Γ.start := by
        simp [Tape.read, hhead, hcell0]
      obtain ⟨c', hstep, hstate', hinp', hhead', hcells'⟩ :=
        inputLengthPlusOneCounterTM_rewind_step_base counterIdx c hstate hinp hread hcell0 hnostart
      exact ⟨c', .step hstep .zero, hstate', hinp', hhead', hcells'⟩
  | succ h ih =>
      intro c hstate hinp hcell0 hnostart hhead
      have hread : (c.work counterIdx).read ≠ Γ.start := by
        simp [Tape.read, hhead]
        exact hnostart (h + 1) (by omega)
      obtain ⟨c1, hstep, hstate1, hinput1_eq, hhead1, hcells1⟩ :=
        inputLengthPlusOneCounterTM_rewind_step_left counterIdx c hstate hinp hread hcell0 hnostart
      have hinp1_ns : c1.input.read ≠ Γ.start := by
        rw [hinput1_eq]
        exact hinp
      have hhead1' : (c1.work counterIdx).head = h := by
        rw [hhead1, hhead]
        omega
      obtain ⟨c', hreach, hhalt, hinp', hhead', hcells'⟩ :=
        ih c1 hstate1 hinp1_ns (by rw [hcells1]; exact hcell0)
          (by intro j hj; rw [hcells1]; exact hnostart j hj) hhead1'
      exact ⟨c', .step hstep hreach, hhalt, by rw [hinp', hinput1_eq], hhead',
        by rw [hcells', hcells1]⟩

/-- A convenient linear upper bound for `inputLengthPlusOneCounterTM`. -/
def inputLengthPlusOneCounterTime (xLen : ℕ) : ℕ :=
  3 * xLen + 10

/-- `inputLengthPlusOneCounterTM` materializes a unary counter of length
    `|x| + 1` on the designated work tape and rewinds it to cell 1. -/
theorem inputLengthPlusOneCounterTM_hoareTime
    (counterIdx : Fin n) (x : List Bool) :
    (inputLengthPlusOneCounterTM counterIdx).HoareTime
      (fun inp work _ =>
        inp = _root_.initTape (x.map Γ.ofBool) ∧
        work counterIdx = _root_.initTape [])
      (fun _ work _ =>
        (work counterIdx).hasUnaryCounter (x.length + 1))
      (inputLengthPlusOneCounterTime x.length) := by
  intro inp work out ⟨hinput, hcounter⟩
  subst inp
  let c0 : Cfg n (inputLengthPlusOneCounterTM counterIdx).Q :=
    { state := LinearCounterPhase.scan,
      input := _root_.initTape (x.map Γ.ofBool),
      work := work,
      output := out }
  obtain ⟨c1, hstep_start, hstate1, hcells1, hhead1, hprefix1, hcell01⟩ :=
    inputLengthPlusOneCounterTM_start_step counterIdx x work out hcounter
  obtain ⟨c2, hreach_scan, hstate2, hcells2, hhead2, hprefix2, hcell02⟩ :=
    inputLengthPlusOneCounterTM_scan_bits_loop counterIdx x x.length 0 c1
      (by omega) hstate1 hcells1 hhead1 hprefix1 hcell01
  have hhead2' : c2.input.head = x.length + 1 := by
    rw [hhead2]
    omega
  have hprefix2' : (c2.work counterIdx).hasUnaryPrefix x.length := by
    simpa using hprefix2
  obtain ⟨c3, hstep_blank, hstate3, hinput3, hprefix3, hcell03⟩ :=
    inputLengthPlusOneCounterTM_scan_blank_step counterIdx x c2
      hstate2 hcells2 hhead2' hprefix2' hcell02
  have hinp3 : c3.input.read ≠ Γ.start := by
    rw [hinput3]
    show c2.input.read ≠ Γ.start
    rw [show c2.input.read = c2.input.cells c2.input.head by rfl, hhead2', hcells2]
    rw [initTape_ofBool_cells_ge x x.length le_rfl]
    decide
  have hnostart3 : ∀ j, j ≥ 1 → (c3.work counterIdx).cells j ≠ Γ.start :=
    Tape.hasUnaryPrefix_cells_ne_start hprefix3
  have hhead3 : (c3.work counterIdx).head = x.length + 2 := by
    rw [hprefix3.1]
  obtain ⟨c4, hreach_rewind, hhalt4, hinput4, hhead4, hcells4⟩ :=
    inputLengthPlusOneCounterTM_rewind_loop counterIdx (x.length + 2) c3
      hstate3 hinp3 hcell03 hnostart3 hhead3
  have hpost : (c4.work counterIdx).hasUnaryCounter (x.length + 1) :=
    Tape.hasUnaryPrefix_to_hasUnaryCounter hprefix3 hhead4 hcells4
  have hreach_start : (inputLengthPlusOneCounterTM counterIdx).reachesIn 1 c0 c1 := by
    exact .step hstep_start .zero
  have hreach_02 : (inputLengthPlusOneCounterTM counterIdx).reachesIn
      (1 + x.length) c0 c2 :=
    reachesIn_trans _ hreach_start hreach_scan
  have hreach_03 : (inputLengthPlusOneCounterTM counterIdx).reachesIn
      (1 + x.length + 1) c0 c3 := by
    simpa [Nat.add_assoc] using
      reachesIn_trans _ hreach_02 (.step hstep_blank .zero)
  have hreach_04 : (inputLengthPlusOneCounterTM counterIdx).reachesIn
      (1 + x.length + 1 + (x.length + 2 + 1)) c0 c4 := by
    simpa [Nat.add_assoc] using
      reachesIn_trans _ hreach_03 hreach_rewind
  refine ⟨c4, 1 + x.length + 1 + (x.length + 2 + 1), ?_, ?_, hhalt4, hpost⟩
  · simp [inputLengthPlusOneCounterTime]
    omega
  · simpa [c0] using hreach_04

/-- Started-tape variant of `inputLengthPlusOneCounterTM_hoareTime`: if the
input is already positioned at cell `1` and the counter tape is the started
blank tape, the machine still builds a unary counter of length `|x| + 1`.
The postcondition also exposes the structural fact that the resulting counter
tape has no `▷` markers beyond cell `0`. -/
theorem inputLengthPlusOneCounterTM_started_hoareTime
    (counterIdx : Fin n) (x : List Bool) :
    (inputLengthPlusOneCounterTM counterIdx).HoareTime
      (fun inp work _ =>
        inp = (_root_.initTape (x.map Γ.ofBool)).move Dir3.right ∧
        work counterIdx = (_root_.initTape []).move Dir3.right)
      (fun _ work _ =>
        (work counterIdx).hasUnaryCounter (x.length + 1) ∧
        (work counterIdx).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (work counterIdx).cells j ≠ Γ.start))
      (inputLengthPlusOneCounterTime x.length) := by
  intro inp work out hpre
  rcases hpre with ⟨hinput, hcounter⟩
  subst inp
  let c0 : Cfg n (inputLengthPlusOneCounterTM counterIdx).Q :=
    { state := LinearCounterPhase.scan,
      input := (_root_.initTape (x.map Γ.ofBool)).move Dir3.right,
      work := work,
      output := out }
  have hcells0 : c0.input.cells = (_root_.initTape (x.map Γ.ofBool)).cells := by
    simp [c0, tape_move_cells]
  have hhead0 : c0.input.head = 1 := by
    simp [c0, Tape.move, _root_.initTape]
  have hprefix0 : (c0.work counterIdx).hasUnaryPrefix 0 := by
    rw [show c0.work counterIdx = work counterIdx by rfl, hcounter]
    exact Tape.initTape_nil_move_right_hasUnaryPrefix_zero
  have hcell00 : (c0.work counterIdx).cells 0 = Γ.start := by
    rw [show c0.work counterIdx = work counterIdx by rfl, hcounter]
    simp [Tape.move, _root_.initTape]
  obtain ⟨c2, hreach_scan, hstate2, hcells2, hhead2, hprefix2, hcell02⟩ :=
    inputLengthPlusOneCounterTM_scan_bits_loop counterIdx x x.length 0 c0
      (by omega) rfl hcells0 hhead0 hprefix0 hcell00
  have hhead2' : c2.input.head = x.length + 1 := by
    rw [hhead2]
    omega
  have hprefix2' : (c2.work counterIdx).hasUnaryPrefix x.length := by
    simpa using hprefix2
  obtain ⟨c3, hstep_blank, hstate3, hinput3, hprefix3, hcell03⟩ :=
    inputLengthPlusOneCounterTM_scan_blank_step counterIdx x c2
      hstate2 hcells2 hhead2' hprefix2' hcell02
  have hinp3 : c3.input.read ≠ Γ.start := by
    rw [hinput3]
    show c2.input.read ≠ Γ.start
    rw [show c2.input.read = c2.input.cells c2.input.head by rfl, hhead2', hcells2]
    rw [initTape_ofBool_cells_ge x x.length le_rfl]
    decide
  have hnostart3 : ∀ j, j ≥ 1 → (c3.work counterIdx).cells j ≠ Γ.start :=
    Tape.hasUnaryPrefix_cells_ne_start hprefix3
  have hhead3 : (c3.work counterIdx).head = x.length + 2 := by
    rw [hprefix3.1]
  obtain ⟨c4, hreach_rewind, hhalt4, hinput4, hhead4, hcells4⟩ :=
    inputLengthPlusOneCounterTM_rewind_loop counterIdx (x.length + 2) c3
      hstate3 hinp3 hcell03 hnostart3 hhead3
  have hcounter4 : (c4.work counterIdx).hasUnaryCounter (x.length + 1) :=
    Tape.hasUnaryPrefix_to_hasUnaryCounter hprefix3 hhead4 hcells4
  have hcell04 : (c4.work counterIdx).cells 0 = Γ.start := by
    rw [hcells4]
    exact hcell03
  have hnostart4 : ∀ j, j ≥ 1 → (c4.work counterIdx).cells j ≠ Γ.start := by
    intro j hj
    rw [hcells4]
    exact hnostart3 j hj
  have hreach_03 : (inputLengthPlusOneCounterTM counterIdx).reachesIn
      (x.length + 1) c0 c3 := by
    simpa [Nat.add_assoc] using
      reachesIn_trans _ hreach_scan (.step hstep_blank .zero)
  have hreach_04 : (inputLengthPlusOneCounterTM counterIdx).reachesIn
      (x.length + 1 + (x.length + 2 + 1)) c0 c4 := by
    simpa [Nat.add_assoc] using
      reachesIn_trans _ hreach_03 hreach_rewind
  refine ⟨c4, x.length + 1 + (x.length + 2 + 1), ?_, ?_, hhalt4,
    ⟨hcounter4, hcell04, hnostart4⟩⟩
  · simp [inputLengthPlusOneCounterTime]
    omega
  · simpa [c0] using hreach_04

/-- Started-tape variant of the unary counter builder that also records the
final input position. The input cells are unchanged, and the input head ends at
the first blank after the scanned Boolean string. -/
theorem inputLengthPlusOneCounterTM_started_tracksInput_hoareTime
    (counterIdx : Fin n) (x : List Bool) :
    (inputLengthPlusOneCounterTM counterIdx).HoareTime
      (fun inp work _ =>
        inp = (_root_.initTape (x.map Γ.ofBool)).move Dir3.right ∧
        work counterIdx = (_root_.initTape []).move Dir3.right)
      (fun inp work _ =>
        inp.cells = (_root_.initTape (x.map Γ.ofBool)).cells ∧
        inp.head = x.length + 1 ∧
        (work counterIdx).hasUnaryCounter (x.length + 1) ∧
        (work counterIdx).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (work counterIdx).cells j ≠ Γ.start))
      (inputLengthPlusOneCounterTime x.length) := by
  intro inp work out hpre
  rcases hpre with ⟨hinput, hcounter⟩
  subst inp
  let c0 : Cfg n (inputLengthPlusOneCounterTM counterIdx).Q :=
    { state := LinearCounterPhase.scan,
      input := (_root_.initTape (x.map Γ.ofBool)).move Dir3.right,
      work := work,
      output := out }
  have hcells0 : c0.input.cells = (_root_.initTape (x.map Γ.ofBool)).cells := by
    simp [c0, tape_move_cells]
  have hhead0 : c0.input.head = 1 := by
    simp [c0, Tape.move, _root_.initTape]
  have hprefix0 : (c0.work counterIdx).hasUnaryPrefix 0 := by
    rw [show c0.work counterIdx = work counterIdx by rfl, hcounter]
    exact Tape.initTape_nil_move_right_hasUnaryPrefix_zero
  have hcell00 : (c0.work counterIdx).cells 0 = Γ.start := by
    rw [show c0.work counterIdx = work counterIdx by rfl, hcounter]
    simp [Tape.move, _root_.initTape]
  obtain ⟨c2, hreach_scan, hstate2, hcells2, hhead2, hprefix2, hcell02⟩ :=
    inputLengthPlusOneCounterTM_scan_bits_loop counterIdx x x.length 0 c0
      (by omega) rfl hcells0 hhead0 hprefix0 hcell00
  have hhead2' : c2.input.head = x.length + 1 := by
    rw [hhead2]
    omega
  have hprefix2' : (c2.work counterIdx).hasUnaryPrefix x.length := by
    simpa using hprefix2
  obtain ⟨c3, hstep_blank, hstate3, hinput3, hprefix3, hcell03⟩ :=
    inputLengthPlusOneCounterTM_scan_blank_step counterIdx x c2
      hstate2 hcells2 hhead2' hprefix2' hcell02
  have hinp3 : c3.input.read ≠ Γ.start := by
    rw [hinput3]
    show c2.input.read ≠ Γ.start
    rw [show c2.input.read = c2.input.cells c2.input.head by rfl, hhead2', hcells2]
    rw [initTape_ofBool_cells_ge x x.length le_rfl]
    decide
  have hnostart3 : ∀ j, j ≥ 1 → (c3.work counterIdx).cells j ≠ Γ.start :=
    Tape.hasUnaryPrefix_cells_ne_start hprefix3
  have hhead3 : (c3.work counterIdx).head = x.length + 2 := by
    rw [hprefix3.1]
  obtain ⟨c4, hreach_rewind, hhalt4, hinput4, hhead4, hcells4⟩ :=
    inputLengthPlusOneCounterTM_rewind_loop counterIdx (x.length + 2) c3
      hstate3 hinp3 hcell03 hnostart3 hhead3
  have hcounter4 : (c4.work counterIdx).hasUnaryCounter (x.length + 1) :=
    Tape.hasUnaryPrefix_to_hasUnaryCounter hprefix3 hhead4 hcells4
  have hcell04 : (c4.work counterIdx).cells 0 = Γ.start := by
    rw [hcells4]
    exact hcell03
  have hnostart4 : ∀ j, j ≥ 1 → (c4.work counterIdx).cells j ≠ Γ.start := by
    intro j hj
    rw [hcells4]
    exact hnostart3 j hj
  have hinput4_cells : c4.input.cells = (_root_.initTape (x.map Γ.ofBool)).cells := by
    rw [hinput4, hinput3]
    exact hcells2
  have hinput4_head : c4.input.head = x.length + 1 := by
    rw [hinput4, hinput3]
    exact hhead2'
  have hreach_03 : (inputLengthPlusOneCounterTM counterIdx).reachesIn
      (x.length + 1) c0 c3 := by
    simpa [Nat.add_assoc] using
      reachesIn_trans _ hreach_scan (.step hstep_blank .zero)
  have hreach_04 : (inputLengthPlusOneCounterTM counterIdx).reachesIn
      (x.length + 1 + (x.length + 2 + 1)) c0 c4 := by
    simpa [Nat.add_assoc] using
      reachesIn_trans _ hreach_03 hreach_rewind
  refine ⟨c4, x.length + 1 + (x.length + 2 + 1), ?_, ?_, hhalt4,
    ⟨hinput4_cells, hinput4_head, hcounter4, hcell04, hnostart4⟩⟩
  · simp [inputLengthPlusOneCounterTime]
    omega
  · simpa [c0] using hreach_04

/-- One-step preservation of a passive started Boolean work tape distinct from
the active counter tape. -/
private theorem inputLengthPlusOneCounterTM_step_preserves_started_other_work
    (counterIdx passiveIdx : Fin n) (hne : passiveIdx ≠ counterIdx)
    (y : List Bool)
    {c c' : Cfg n (inputLengthPlusOneCounterTM counterIdx).Q}
    (hstep : (inputLengthPlusOneCounterTM counterIdx).step c = some c')
    (hpassive : c.work passiveIdx = (_root_.initTape (y.map Γ.ofBool)).move Dir3.right) :
    c'.work passiveIdx = c.work passiveIdx := by
  have hpassive_read : (c.work passiveIdx).read ≠ Γ.start := by
    rw [hpassive]
    exact started_ofBool_tape_read_ne_start y
  cases c with
  | mk state input work output =>
      change work passiveIdx = (_root_.initTape (y.map Γ.ofBool)).move Dir3.right at hpassive
      cases state with
      | scan =>
          by_cases hstart : input.read = Γ.start
          · simp [TM.step, inputLengthPlusOneCounterTM, hstart] at hstep
            subst hstep
            simpa [counterPreserveWork, counterIdleDirs] using
              Tape.writeAndMove_readBack_idle_of_ne_start (work passiveIdx)
                (by simpa [hpassive] using hpassive_read)
          · by_cases hblank : input.read = Γ.blank
            · simp [TM.step, inputLengthPlusOneCounterTM, hblank] at hstep
              subst hstep
              simpa [counterWriteOneWork, counterAdvanceDirs, hne] using
                Tape.writeAndMove_readBack_idle_of_ne_start (work passiveIdx)
                  (by simpa [hpassive] using hpassive_read)
            · simp [TM.step, inputLengthPlusOneCounterTM, hstart, hblank] at hstep
              subst hstep
              simpa [counterWriteOneWork, counterAdvanceDirs, hne] using
                Tape.writeAndMove_readBack_idle_of_ne_start (work passiveIdx)
                  (by simpa [hpassive] using hpassive_read)
      | rewind =>
          by_cases hcounter : (work counterIdx).read = Γ.start
          · simp [TM.step, inputLengthPlusOneCounterTM, hcounter] at hstep
            subst hstep
            simpa [counterPreserveWork, counterAdvanceDirs, hne] using
              Tape.writeAndMove_readBack_idle_of_ne_start (work passiveIdx)
                (by simpa [hpassive] using hpassive_read)
          · simp [TM.step, inputLengthPlusOneCounterTM, hcounter] at hstep
            subst hstep
            simpa [counterPreserveWork, counterRewindDirs, hne] using
              Tape.writeAndMove_readBack_idle_of_ne_start (work passiveIdx)
                (by simpa [hpassive] using hpassive_read)
      | done =>
          simp [TM.step, inputLengthPlusOneCounterTM] at hstep

/-- Multi-step preservation of a passive started Boolean work tape distinct
from the active counter tape. -/
private theorem inputLengthPlusOneCounterTM_reachesIn_preserves_started_other_work
    (counterIdx passiveIdx : Fin n) (hne : passiveIdx ≠ counterIdx)
    (y : List Bool)
    {t : ℕ} {c c' : Cfg n (inputLengthPlusOneCounterTM counterIdx).Q}
    (hreach : (inputLengthPlusOneCounterTM counterIdx).reachesIn t c c')
    (hpassive : c.work passiveIdx = (_root_.initTape (y.map Γ.ofBool)).move Dir3.right) :
    c'.work passiveIdx = (_root_.initTape (y.map Γ.ofBool)).move Dir3.right := by
  induction hreach with
  | zero =>
      exact hpassive
  | step hstep _ ih =>
      have hmid : _ = _ :=
        inputLengthPlusOneCounterTM_step_preserves_started_other_work
          counterIdx passiveIdx hne y hstep hpassive
      exact ih (by simpa [hmid] using hpassive)

/-- One-step preservation of a started blank output tape. -/
private theorem inputLengthPlusOneCounterTM_step_preserves_started_blank_output
    (counterIdx : Fin n)
    {c c' : Cfg n (inputLengthPlusOneCounterTM counterIdx).Q}
    (hstep : (inputLengthPlusOneCounterTM counterIdx).step c = some c')
    (hout : c.output = (_root_.initTape []).move Dir3.right) :
    c'.output = c.output := by
  have hout_read : c.output.read ≠ Γ.start := by
    rw [hout]
    simp [Tape.read, Tape.move, _root_.initTape]
  cases c with
  | mk state input work output =>
      change output = (_root_.initTape []).move Dir3.right at hout
      cases state with
      | scan =>
          by_cases hstart : input.read = Γ.start
          · simp [TM.step, inputLengthPlusOneCounterTM, hstart] at hstep
            subst hstep
            simpa [hout] using
              Tape.writeAndMove_readBack_idle_of_ne_start output
                (by simpa [hout] using hout_read)
          · by_cases hblank : input.read = Γ.blank
            · simp [TM.step, inputLengthPlusOneCounterTM, hblank] at hstep
              subst hstep
              simpa [hout] using
                Tape.writeAndMove_readBack_idle_of_ne_start output
                  (by simpa [hout] using hout_read)
            · simp [TM.step, inputLengthPlusOneCounterTM, hstart, hblank] at hstep
              subst hstep
              simpa [hout] using
                Tape.writeAndMove_readBack_idle_of_ne_start output
                  (by simpa [hout] using hout_read)
      | rewind =>
          by_cases hcounter : (work counterIdx).read = Γ.start
          · simp [TM.step, inputLengthPlusOneCounterTM, hcounter] at hstep
            subst hstep
            simpa [hout] using
              Tape.writeAndMove_readBack_idle_of_ne_start output
                (by simpa [hout] using hout_read)
          · simp [TM.step, inputLengthPlusOneCounterTM, hcounter] at hstep
            subst hstep
            simpa [hout] using
              Tape.writeAndMove_readBack_idle_of_ne_start output
                (by simpa [hout] using hout_read)
      | done =>
          simp [TM.step, inputLengthPlusOneCounterTM] at hstep

/-- Multi-step preservation of a started blank output tape. -/
private theorem inputLengthPlusOneCounterTM_reachesIn_preserves_started_blank_output
    (counterIdx : Fin n)
    {t : ℕ} {c c' : Cfg n (inputLengthPlusOneCounterTM counterIdx).Q}
    (hreach : (inputLengthPlusOneCounterTM counterIdx).reachesIn t c c')
    (hout : c.output = (_root_.initTape []).move Dir3.right) :
    c'.output = (_root_.initTape []).move Dir3.right := by
  induction hreach with
  | zero =>
      exact hout
  | step hstep _ ih =>
      have hmid : _ = _ :=
        inputLengthPlusOneCounterTM_step_preserves_started_blank_output
          counterIdx hstep hout
      exact ih (by simpa [hmid] using hout)

/-- Started-tape variant of the unary counter builder that also records the
final input position and preserves one passive started Boolean work tape
exactly. -/
theorem inputLengthPlusOneCounterTM_started_tracksInput_preserves_work_hoareTime
    (counterIdx passiveIdx : Fin n) (hne : passiveIdx ≠ counterIdx)
    (x y : List Bool) :
    (inputLengthPlusOneCounterTM counterIdx).HoareTime
      (fun inp work out =>
        inp = (_root_.initTape (x.map Γ.ofBool)).move Dir3.right ∧
        work counterIdx = (_root_.initTape []).move Dir3.right ∧
        work passiveIdx = (_root_.initTape (y.map Γ.ofBool)).move Dir3.right ∧
        out = (_root_.initTape []).move Dir3.right)
      (fun inp work out =>
        inp.cells = (_root_.initTape (x.map Γ.ofBool)).cells ∧
        inp.head = x.length + 1 ∧
        work passiveIdx = (_root_.initTape (y.map Γ.ofBool)).move Dir3.right ∧
        (work counterIdx).hasUnaryCounter (x.length + 1) ∧
        (work counterIdx).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (work counterIdx).cells j ≠ Γ.start) ∧
        out = (_root_.initTape []).move Dir3.right)
      (inputLengthPlusOneCounterTime x.length) := by
  intro inp work out hpre
  rcases hpre with ⟨hinput, hcounter, hpassive, hout⟩
  obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ :=
    inputLengthPlusOneCounterTM_started_tracksInput_hoareTime counterIdx x inp work out
      ⟨hinput, hcounter⟩
  have hpassive' :
      c'.work passiveIdx = (_root_.initTape (y.map Γ.ofBool)).move Dir3.right :=
    inputLengthPlusOneCounterTM_reachesIn_preserves_started_other_work
      counterIdx passiveIdx hne y hreach hpassive
  have hout' :
      c'.output = (_root_.initTape []).move Dir3.right :=
    inputLengthPlusOneCounterTM_reachesIn_preserves_started_blank_output
      counterIdx hreach hout
  exact ⟨c', t, ht, hreach, hhalt, ⟨hpost.1, hpost.2.1, hpassive', hpost.2.2.1,
    hpost.2.2.2.1, hpost.2.2.2.2, hout'⟩⟩

/-- Nondeterministic form of `inputLengthPlusOneCounterTM_hoareTime`, for use
    inside NTM constructions after lifting the deterministic setup machine. -/
theorem inputLengthPlusOneCounterTM_toNTM_hoareTime
    (counterIdx : Fin n) (x : List Bool) :
    ((inputLengthPlusOneCounterTM counterIdx).toNTM).HoareTime
      (fun inp work _ =>
        inp = _root_.initTape (x.map Γ.ofBool) ∧
        work counterIdx = _root_.initTape [])
      (fun _ work _ =>
        (work counterIdx).hasUnaryCounter (x.length + 1))
      (inputLengthPlusOneCounterTime x.length) :=
  (inputLengthPlusOneCounterTM_hoareTime counterIdx x).toNTM

end TM
