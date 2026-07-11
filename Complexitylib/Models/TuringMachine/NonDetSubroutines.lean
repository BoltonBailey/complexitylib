import Complexitylib.Models.TuringMachine.CounterSubroutines

namespace Complexity

/-!
# Nondeterministic TM subroutines

Small NTM building blocks used by NP constructions.

The main definition in this file is `NTM.guessBoundedNTM`: given a witness
tape and a preloaded unary counter tape, nondeterministically write a witness
whose length is at most the number of counter marks. The counter gives the
guess phase a structural all-paths halting bound, which is essential for
`NTIME`.
-/

namespace Γw

/-- Writable encoding of a Boolean bit. -/
@[simp] def ofBool : Bool → Γw
  | false => .zero
  | true => .one

@[simp] theorem ofBool_toΓ (b : Bool) : (ofBool b).toΓ = Γ.ofBool b := by
  cases b <;> rfl

end Γw

namespace Tape

/-- A witness tape while it is being guessed: cells `1..|bits|` contain the
    guessed bits, the head is at the next cell, and the remaining tail is
    blank. -/
def hasBinaryPrefix (t : Tape) (bits : List Bool) : Prop :=
  t.head = bits.length + 1 ∧
  (∀ i, (h : i < bits.length) → t.cells (i + 1) = Γ.ofBool (bits[i]'h)) ∧
  (∀ i, bits.length ≤ i → t.cells (i + 1) = Γ.blank)

/-- A completed witness tape: the guessed bits are present and the head has
    been rewound to cell 1. -/
def hasBinaryString (t : Tape) (bits : List Bool) : Prop :=
  t.head = 1 ∧
  (∀ i, (h : i < bits.length) → t.cells (i + 1) = Γ.ofBool (bits[i]'h)) ∧
  (∀ i, bits.length ≤ i → t.cells (i + 1) = Γ.blank)

/-- A completed witness tape whose encoded string has length at most `B`. -/
def hasBoundedBinaryString (t : Tape) (B : ℕ) : Prop :=
  ∃ bits : List Bool, bits.length ≤ B ∧ t.hasBinaryString bits

theorem hasBinaryString_hasOutput {t : Tape} {bits : List Bool}
    (h : t.hasBinaryString bits) : t.hasOutput bits :=
  ⟨h.2.1, h.2.2 bits.length le_rfl⟩

theorem hasBinaryString_cells_ne_start {t : Tape} {bits : List Bool}
    (h : t.hasBinaryString bits) :
    ∀ j, j ≥ 1 → t.cells j ≠ Γ.start := by
  intro j hj
  let i := j - 1
  have hj_eq : j = i + 1 := by omega
  by_cases hi : i < bits.length
  · rw [hj_eq, h.2.1 i hi]
    cases bits[i]'hi <;> simp [Γ.ofBool]
  · have hge : bits.length ≤ i := by omega
    rw [hj_eq, h.2.2 i hge]
    decide

/-- A completed binary witness tape with the left marker at cell `0` is
    exactly the standard initialized tape for those bits, moved to cell `1`. -/
theorem hasBinaryString_eq_initTape_move_right {t : Tape} {bits : List Bool}
    (h : t.hasBinaryString bits) (h0 : t.cells 0 = Γ.start) :
    t = (_root_.Complexity.initTape (bits.map Γ.ofBool)).move Dir3.right := by
  cases t with
  | mk head cells =>
    simp only [hasBinaryString] at h
    rcases h with ⟨hhead, hbits, htail⟩
    simp only at h0 hbits htail
    subst head
    simp only [Tape.move]
    congr
    funext j
    by_cases hj0 : j = 0
    · subst hj0
      simp [_root_.Complexity.initTape, h0]
    · let i := j - 1
      have hj : j = i + 1 := by omega
      rw [hj]
      by_cases hi : i < bits.length
      · rw [hbits i hi, initTape_ofBool_cells_lt bits i hi]
      · have hge : bits.length ≤ i := by omega
        rw [htail i hge, initTape_ofBool_cells_ge bits i hge]

/-- Bounded completed witness tapes expose exact initialized tape shape for
    some string whose length satisfies the same bound. -/
theorem hasBoundedBinaryString_eq_initTape_move_right {t : Tape} {B : ℕ}
    (h : t.hasBoundedBinaryString B) (h0 : t.cells 0 = Γ.start) :
    ∃ bits : List Bool, bits.length ≤ B ∧
      t = (_root_.Complexity.initTape (bits.map Γ.ofBool)).move Dir3.right := by
  obtain ⟨bits, hlen, hbits⟩ := h
  exact ⟨bits, hlen, hasBinaryString_eq_initTape_move_right hbits h0⟩

theorem initTape_nil_move_right_hasBinaryPrefix_nil :
    ((_root_.Complexity.initTape []).move Dir3.right).hasBinaryPrefix [] := by
  simp [hasBinaryPrefix, _root_.Complexity.initTape, Tape.move]

/-- Writing the next guessed bit extends a binary prefix by one cell. -/
theorem hasBinaryPrefix_write_bit {t : Tape} {bits : List Bool} (bit : Bool)
    (h : t.hasBinaryPrefix bits) :
    (t.writeAndMove (Γ.ofBool bit) Dir3.right).hasBinaryPrefix (bits ++ [bit]) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Tape.writeAndMove, Tape.write, Tape.move, h.1]
  · intro i hi
    unfold Tape.writeAndMove
    simp only [Tape.move]
    unfold Tape.write
    have hhead_ne : ¬t.head = 0 := by rw [h.1]; omega
    simp only [hhead_ne, ↓reduceIte]
    by_cases hidx : i = bits.length
    · have hcellidx : i + 1 = t.head := by rw [h.1, hidx]
      have hget : (bits ++ [bit])[i]'hi = bit := by
        subst hidx
        simp
      rw [hcellidx, Function.update_self, hget]
    · have hi_bits : i < bits.length := by
        rw [List.length_append, List.length_singleton] at hi
        omega
      have hcell := h.2.1 i hi_bits
      have hget : (bits ++ [bit])[i]'hi = bits[i]'hi_bits := by
        exact List.getElem_append_left (as := bits) (bs := [bit]) hi_bits
      have hne : t.head ≠ i + 1 := by rw [h.1]; omega
      rw [Function.update_of_ne (Ne.symm hne), hcell, hget]
  · intro i hi
    unfold Tape.writeAndMove
    simp only [Tape.move]
    unfold Tape.write
    have hhead_ne : ¬t.head = 0 := by rw [h.1]; omega
    simp only [hhead_ne, ↓reduceIte]
    have hne : t.head ≠ i + 1 := by
      rw [List.length_append, List.length_singleton] at hi
      rw [h.1]
      omega
    rw [Function.update_of_ne (Ne.symm hne)]
    exact h.2.2 i (by
      rw [List.length_append, List.length_singleton] at hi
      omega)

/-- Writing the next guessed bit preserves the left-end marker cell. -/
theorem hasBinaryPrefix_write_bit_cell0 {t : Tape} {bits : List Bool} (bit : Bool)
    (h : t.hasBinaryPrefix bits) (h0 : t.cells 0 = Γ.start) :
    (t.writeAndMove (Γ.ofBool bit) Dir3.right).cells 0 = Γ.start := by
  unfold Tape.writeAndMove
  rw [TM.tape_move_cells]
  unfold Tape.write
  have hhead_ne : ¬t.head = 0 := by rw [h.1]; omega
  simp only [hhead_ne, ↓reduceIte]
  have hne : t.head ≠ 0 := by rw [h.1]; omega
  rw [Function.update_of_ne (Ne.symm hne)]
  exact h0

/-- A binary prefix never contains `▷` after the left-end marker. -/
theorem hasBinaryPrefix_cells_ne_start {t : Tape} {bits : List Bool}
    (h : t.hasBinaryPrefix bits) :
    ∀ j, j ≥ 1 → t.cells j ≠ Γ.start := by
  intro j hj
  let i := j - 1
  have hj_eq : j = i + 1 := by omega
  by_cases hi : i < bits.length
  · rw [hj_eq, h.2.1 i hi]
    cases bits[i]'hi <;> simp [Γ.ofBool]
  · have hge : bits.length ≤ i := by omega
    rw [hj_eq, h.2.2 i hge]
    decide

/-- Rewinding a binary prefix to cell 1 yields a completed witness string. -/
theorem hasBinaryPrefix_to_hasBinaryString {t t' : Tape} {bits : List Bool}
    (hprefix : t.hasBinaryPrefix bits)
    (hhead : t'.head = 1)
    (hcells : t'.cells = t.cells) :
    t'.hasBinaryString bits := by
  refine ⟨hhead, ?_, ?_⟩
  · intro i hi
    rw [hcells]
    exact hprefix.2.1 i hi
  · intro i hi
    rw [hcells]
    exact hprefix.2.2 i hi

end Tape

namespace NTM

variable {n : ℕ}

/-- Split a two-step trace into two one-step traces. -/
theorem trace_two_eq (tm : NTM n) (choices : Fin 2 → Bool) (c : Cfg n tm.Q) :
    tm.trace 2 choices c =
      tm.trace 1 (fun _ => choices ⟨1, by omega⟩)
        (tm.trace 1 (fun _ => choices ⟨0, by omega⟩) c) := by
  by_cases hhalt : c.state = tm.qhalt
  · simp [NTM.trace, hhalt]
  · simp [NTM.trace, hhalt]

/-- Split the first step off a nonzero trace. If the machine is already
    halted, both sides reduce to the starting configuration. -/
theorem trace_succ_eq_trace_one (tm : NTM n) (T : ℕ)
    (choices : Fin (T + 1) → Bool) (c : Cfg n tm.Q) :
    tm.trace (T + 1) choices c =
      tm.trace T (fun i => choices ⟨i.val + 1, by omega⟩)
        (tm.trace 1 (fun _ => choices ⟨0, by omega⟩) c) := by
  by_cases hhalt : c.state = tm.qhalt
  · simp [NTM.trace, hhalt]
    exact (tm.trace_halted T (fun i => choices ⟨i.val + 1, by omega⟩) hhalt).symm
  · simp [NTM.trace, hhalt]

/-- Split the first two steps off a trace. -/
theorem trace_add_two_eq (tm : NTM n) (T : ℕ)
    (choices : Fin (T + 2) → Bool) (c : Cfg n tm.Q) :
    tm.trace (T + 2) choices c =
      tm.trace T (fun i => choices ⟨i.val + 2, by omega⟩)
        (tm.trace 2 (fun i => choices ⟨i.val, by omega⟩) c) := by
  change tm.trace ((T + 1) + 1) choices c = _
  rw [trace_succ_eq_trace_one tm (T + 1) choices c]
  rw [trace_succ_eq_trace_one tm T
    (fun i : Fin (T + 1) => choices ⟨i.val + 1, by omega⟩)
    (tm.trace 1 (fun x => choices ⟨0, by omega⟩) c)]
  rw [← trace_two_eq tm (fun i : Fin 2 => choices ⟨i.val, by omega⟩) c]

/-- Reindex a trace along an equality of time bounds. -/
theorem trace_cast (tm : NTM n) {T T' : ℕ} (h : T = T')
    (choices : Fin T → Bool) (c : Cfg n tm.Q) :
    tm.trace T choices c =
      tm.trace T' (fun i => choices (Fin.cast h.symm i)) c := by
  cases h
  rfl

/-- Split the first `T` steps off a trace.

This version uses `Fin.castLE`/`Fin.natAdd` for the prefix and suffix choice
sequences, which keeps later proofs away from ad-hoc dependent index casts. -/
theorem trace_add_eq (tm : NTM n) (T U : ℕ)
    (choices : Fin (T + U) → Bool) (c : Cfg n tm.Q) :
    tm.trace (T + U) choices c =
      tm.trace U (fun i => choices (Fin.natAdd T i))
        (tm.trace T (fun i => choices (Fin.castLE (Nat.le_add_right T U) i)) c) := by
  induction T generalizing U c with
  | zero =>
    have h := trace_cast tm (Nat.zero_add U) choices c
    rw [h]
    congr 1
    funext i
    apply congrArg choices
    exact Fin.ext (by simp [Fin.natAdd])
  | succ T ih =>
    let choicesCast : Fin ((T + U) + 1) → Bool :=
      fun i => choices (Fin.cast (by omega : (T + U) + 1 = (T + 1) + U) i)
    have hcast := trace_cast tm (by omega : (T + 1) + U = (T + U) + 1) choices c
    rw [hcast]
    rw [trace_succ_eq_trace_one tm (T + U) choicesCast c]
    rw [ih U (fun i : Fin (T + U) => choicesCast ⟨i.val + 1, by omega⟩)
      (tm.trace 1 (fun _ => choicesCast ⟨0, by omega⟩) c)]
    let prefixFinal : Fin (T + 1) → Bool :=
      fun i => choices (Fin.castLE (Nat.le_add_right (T + 1) U) i)
    have hprefix :
        tm.trace (T + 1) prefixFinal c =
          tm.trace T
            (fun i : Fin T =>
              choicesCast ⟨(Fin.castLE (Nat.le_add_right T U) i).val + 1, by omega⟩)
            (tm.trace 1 (fun _ => choicesCast ⟨0, by omega⟩) c) := by
      simpa [choicesCast, prefixFinal, Fin.castLE, Fin.cast] using
        trace_succ_eq_trace_one tm T prefixFinal c
    rw [← hprefix]
    congr 1
    funext i
    apply congrArg choices
    exact Fin.ext (by simp [Fin.val_natAdd]; omega)

-- ════════════════════════════════════════════════════════════════════════
-- Bounded witness guessing from a unary counter
-- ════════════════════════════════════════════════════════════════════════

/-- Control states for `guessBoundedNTM`.

- `choose`: decide nondeterministically whether to stop or continue.
- `write`: write the next guessed bit and consume one counter mark.
- `rewind`: rewind the witness tape to cell 1.
- `done`: halt. -/
inductive GuessBoundedPhase where
  | choose
  | write
  | rewind
  | done
  deriving DecidableEq

instance : Fintype GuessBoundedPhase where
  elems := {.choose, .write, .rewind, .done}
  complete := fun x => by cases x <;> simp

/-- Preserve a work tape by writing back the symbol currently under its head
    and using an idle direction. -/
private def preserveWork (wHeads : Fin n → Γ) : Fin n → Γw :=
  fun i => TM.readBackWrite (wHeads i)

/-- Idle directions for all work tapes. -/
private def idleWorkDirs (wHeads : Fin n → Γ) : Fin n → Dir3 :=
  fun i => TM.idleDir (wHeads i)

private theorem idleWorkDirs_right_of_start (wHeads : Fin n → Γ) :
    ∀ i, wHeads i = Γ.start → idleWorkDirs wHeads i = Dir3.right := by
  intro i hi
  exact TM.idleDir_right_of_start hi

/-- Work writes for the bit-writing step. The witness tape receives the
    nondeterministic bit, while the counter tape has its current mark erased.
    The definition is meaningful when `witnessIdx ≠ counterIdx`; later
    correctness lemmas assume that disjointness. -/
private def guessWriteWork (witnessIdx counterIdx : Fin n)
    (choice : Bool) (wHeads : Fin n → Γ) : Fin n → Γw :=
  fun i =>
    if i = witnessIdx then Γw.ofBool choice
    else if i = counterIdx then Γw.blank
    else TM.readBackWrite (wHeads i)

/-- Work directions for the bit-writing step: witness and counter advance
    right, all other tapes idle. -/
private def guessWriteDirs (witnessIdx counterIdx : Fin n)
    (wHeads : Fin n → Γ) : Fin n → Dir3 :=
  fun i =>
    if i = witnessIdx then Dir3.right
    else if i = counterIdx then Dir3.right
    else TM.idleDir (wHeads i)

private theorem guessWriteDirs_right_of_start (witnessIdx counterIdx : Fin n)
    (wHeads : Fin n → Γ) :
    ∀ i, wHeads i = Γ.start →
      guessWriteDirs witnessIdx counterIdx wHeads i = Dir3.right := by
  intro i hi
  by_cases hwi : i = witnessIdx
  · simp [guessWriteDirs, hwi]
  · by_cases hci : i = counterIdx
    · simp [guessWriteDirs, hci]
    · simp [guessWriteDirs, hwi, hci, TM.idleDir_right_of_start hi]

/-- Work directions for rewinding the witness tape to cell 1. -/
private def rewindWitnessDirs (witnessIdx : Fin n)
    (wHeads : Fin n → Γ) : Fin n → Dir3 :=
  fun i =>
    if i = witnessIdx then TM.moveLeftDir (wHeads i)
    else TM.idleDir (wHeads i)

private theorem moveLeftDir_right_of_start {g : Γ} (h : g = Γ.start) :
    TM.moveLeftDir g = Dir3.right := by
  subst h
  rfl

private theorem rewindWitnessDirs_right_of_start (witnessIdx : Fin n)
    (wHeads : Fin n → Γ) :
    ∀ i, wHeads i = Γ.start →
      rewindWitnessDirs witnessIdx wHeads i = Dir3.right := by
  intro i hi
  by_cases hwi : i = witnessIdx
  · subst hwi
    simp [rewindWitnessDirs, moveLeftDir_right_of_start hi]
  · simp [rewindWitnessDirs, hwi, TM.idleDir_right_of_start hi]

private theorem rightOfStart_idle (iHead : Γ) (wHeads : Fin n → Γ) (oHead : Γ) :
    (iHead = Γ.start → TM.idleDir iHead = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → idleWorkDirs wHeads i = Dir3.right) ∧
    (oHead = Γ.start → TM.idleDir oHead = Dir3.right) :=
  ⟨TM.idleDir_right_of_start, idleWorkDirs_right_of_start wHeads,
    TM.idleDir_right_of_start⟩

private theorem rightOfStart_guessWrite (witnessIdx counterIdx : Fin n)
    (iHead : Γ) (wHeads : Fin n → Γ) (oHead : Γ) :
    (iHead = Γ.start → TM.idleDir iHead = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start →
      guessWriteDirs witnessIdx counterIdx wHeads i = Dir3.right) ∧
    (oHead = Γ.start → TM.idleDir oHead = Dir3.right) :=
  ⟨TM.idleDir_right_of_start, guessWriteDirs_right_of_start witnessIdx counterIdx wHeads,
    TM.idleDir_right_of_start⟩

private theorem rightOfStart_rewind (witnessIdx : Fin n)
    (iHead : Γ) (wHeads : Fin n → Γ) (oHead : Γ) :
    (iHead = Γ.start → TM.idleDir iHead = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start →
      rewindWitnessDirs witnessIdx wHeads i = Dir3.right) ∧
    (oHead = Γ.start → TM.idleDir oHead = Dir3.right) :=
  ⟨TM.idleDir_right_of_start, rewindWitnessDirs_right_of_start witnessIdx wHeads,
    TM.idleDir_right_of_start⟩

/-- A bounded nondeterministic witness-guessing subroutine.

The machine uses two work tapes:
- `witnessIdx`: receives the guessed witness bits.
- `counterIdx`: is assumed to contain a unary counter. Each guessed bit
  consumes one counter mark by blanking the current counter cell and moving
  the counter head right.

At each `choose` state, choice `false` stops early; choice `true` continues
if the counter is not blank. When the counter is blank, the machine must stop.
It then rewinds the witness tape to cell 1 and halts. -/
def guessBoundedNTM (witnessIdx counterIdx : Fin n) : NTM n where
  Q := GuessBoundedPhase
  qstart := .choose
  qhalt := .done
  δ := fun choice state iHead wHeads oHead =>
    match state with
    | .choose =>
      if wHeads counterIdx = Γ.blank then
        (.rewind, preserveWork wHeads, TM.readBackWrite oHead,
          TM.idleDir iHead, idleWorkDirs wHeads, TM.idleDir oHead)
      else if choice = false then
        (.rewind, preserveWork wHeads, TM.readBackWrite oHead,
          TM.idleDir iHead, idleWorkDirs wHeads, TM.idleDir oHead)
      else
        (.write, preserveWork wHeads, TM.readBackWrite oHead,
          TM.idleDir iHead, idleWorkDirs wHeads, TM.idleDir oHead)
    | .write =>
      if wHeads counterIdx = Γ.blank then
        (.rewind, preserveWork wHeads, TM.readBackWrite oHead,
          TM.idleDir iHead, idleWorkDirs wHeads, TM.idleDir oHead)
      else
        (.choose, guessWriteWork witnessIdx counterIdx choice wHeads,
          TM.readBackWrite oHead, TM.idleDir iHead,
          guessWriteDirs witnessIdx counterIdx wHeads, TM.idleDir oHead)
    | .rewind =>
      if wHeads witnessIdx = Γ.start then
        (.done, preserveWork wHeads, TM.readBackWrite oHead,
          TM.idleDir iHead, rewindWitnessDirs witnessIdx wHeads, TM.idleDir oHead)
      else
        (.rewind, preserveWork wHeads, TM.readBackWrite oHead,
          TM.idleDir iHead, rewindWitnessDirs witnessIdx wHeads, TM.idleDir oHead)
    | .done =>
      (.done, preserveWork wHeads, TM.readBackWrite oHead,
        TM.idleDir iHead, idleWorkDirs wHeads, TM.idleDir oHead)
  δ_right_of_start := by
    intro choice state iHead wHeads oHead
    cases state
    · by_cases hcounter : wHeads counterIdx = Γ.blank
      · simpa [hcounter] using rightOfStart_idle iHead wHeads oHead
      · by_cases hchoice : choice = false
        · simpa [hcounter, hchoice] using rightOfStart_idle iHead wHeads oHead
        · simpa [hcounter, hchoice] using rightOfStart_idle iHead wHeads oHead
    · by_cases hcounter : wHeads counterIdx = Γ.blank
      · simpa [hcounter] using rightOfStart_idle iHead wHeads oHead
      · simpa [hcounter] using
          rightOfStart_guessWrite witnessIdx counterIdx iHead wHeads oHead
    · by_cases hwit : wHeads witnessIdx = Γ.start
      · simpa [hwit] using rightOfStart_rewind witnessIdx iHead wHeads oHead
      · simpa [hwit] using rightOfStart_rewind witnessIdx iHead wHeads oHead
    · exact rightOfStart_idle iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- Trace preservation for tapes not actively modified by the guess phase
-- ════════════════════════════════════════════════════════════════════════

theorem guessBoundedNTM_trace_one_preserves_input
    (witnessIdx counterIdx : Fin n) (choice : Bool)
    (c : Cfg n (guessBoundedNTM witnessIdx counterIdx).Q)
    (hread : c.input.read ≠ Γ.start) :
    ((guessBoundedNTM witnessIdx counterIdx).trace 1 (fun _ => choice) c).input =
      c.input := by
  by_cases hhalt : c.state = GuessBoundedPhase.done
  · simp [NTM.trace, guessBoundedNTM, hhalt]
  · cases hstate : c.state
    · by_cases hcounter : (c.work counterIdx).read = Γ.blank
      · simp [NTM.trace, guessBoundedNTM, hstate, hcounter, hread, TM.idleDir, Tape.move]
      · by_cases hchoice : choice = false <;>
          simp [NTM.trace, guessBoundedNTM, hstate, hcounter, hchoice, hread,
            TM.idleDir, Tape.move]
    · by_cases hcounter : (c.work counterIdx).read = Γ.blank <;>
        simp [NTM.trace, guessBoundedNTM, hstate, hcounter, hread, TM.idleDir,
          Tape.move]
    · by_cases hwit : (c.work witnessIdx).read = Γ.start <;>
        simp [NTM.trace, guessBoundedNTM, hstate, hwit, hread, TM.idleDir, Tape.move]
    · exact (hhalt hstate).elim

theorem guessBoundedNTM_trace_preserves_input
    (witnessIdx counterIdx : Fin n) (T : ℕ)
    (choices : Fin T → Bool)
    (c : Cfg n (guessBoundedNTM witnessIdx counterIdx).Q)
    (hread : c.input.read ≠ Γ.start) :
    ((guessBoundedNTM witnessIdx counterIdx).trace T choices c).input = c.input := by
  induction T generalizing c with
  | zero => rfl
  | succ T ih =>
    rw [trace_succ_eq_trace_one (guessBoundedNTM witnessIdx counterIdx) T choices c]
    have hfirst := guessBoundedNTM_trace_one_preserves_input witnessIdx counterIdx
      (choices ⟨0, by omega⟩) c hread
    have hread' :
        (((guessBoundedNTM witnessIdx counterIdx).trace 1
          (fun _ => choices ⟨0, by omega⟩) c).input).read ≠ Γ.start := by
      rw [hfirst]
      exact hread
    rw [ih (fun i => choices ⟨i.val + 1, by omega⟩)
      ((guessBoundedNTM witnessIdx counterIdx).trace 1
        (fun _ => choices ⟨0, by omega⟩) c) hread', hfirst]

theorem guessBoundedNTM_trace_one_preserves_output
    (witnessIdx counterIdx : Fin n) (choice : Bool)
    (c : Cfg n (guessBoundedNTM witnessIdx counterIdx).Q)
    (hread : c.output.read ≠ Γ.start) :
    ((guessBoundedNTM witnessIdx counterIdx).trace 1 (fun _ => choice) c).output =
      c.output := by
  have hpres := Tape.writeAndMove_readBack_idle_of_ne_start c.output hread
  by_cases hhalt : c.state = GuessBoundedPhase.done
  · simp [NTM.trace, guessBoundedNTM, hhalt]
  · cases hstate : c.state
    · by_cases hcounter : (c.work counterIdx).read = Γ.blank
      · simpa [NTM.trace, guessBoundedNTM, hstate, hcounter] using hpres
      · by_cases hchoice : choice = false <;>
          simpa [NTM.trace, guessBoundedNTM, hstate, hcounter, hchoice] using hpres
    · by_cases hcounter : (c.work counterIdx).read = Γ.blank <;>
        simpa [NTM.trace, guessBoundedNTM, hstate, hcounter] using hpres
    · by_cases hwit : (c.work witnessIdx).read = Γ.start <;>
        simpa [NTM.trace, guessBoundedNTM, hstate, hwit] using hpres
    · exact (hhalt hstate).elim

theorem guessBoundedNTM_trace_preserves_output
    (witnessIdx counterIdx : Fin n) (T : ℕ)
    (choices : Fin T → Bool)
    (c : Cfg n (guessBoundedNTM witnessIdx counterIdx).Q)
    (hread : c.output.read ≠ Γ.start) :
    ((guessBoundedNTM witnessIdx counterIdx).trace T choices c).output = c.output := by
  induction T generalizing c with
  | zero => rfl
  | succ T ih =>
    rw [trace_succ_eq_trace_one (guessBoundedNTM witnessIdx counterIdx) T choices c]
    have hfirst := guessBoundedNTM_trace_one_preserves_output witnessIdx counterIdx
      (choices ⟨0, by omega⟩) c hread
    have hread' :
        (((guessBoundedNTM witnessIdx counterIdx).trace 1
          (fun _ => choices ⟨0, by omega⟩) c).output).read ≠ Γ.start := by
      rw [hfirst]
      exact hread
    rw [ih (fun i => choices ⟨i.val + 1, by omega⟩)
      ((guessBoundedNTM witnessIdx counterIdx).trace 1
        (fun _ => choices ⟨0, by omega⟩) c) hread', hfirst]

theorem guessBoundedNTM_trace_one_preserves_other_work
    (witnessIdx counterIdx otherIdx : Fin n) (choice : Bool)
    (c : Cfg n (guessBoundedNTM witnessIdx counterIdx).Q)
    (hwitness : otherIdx ≠ witnessIdx)
    (hcounter : otherIdx ≠ counterIdx)
    (hread : (c.work otherIdx).read ≠ Γ.start) :
    (((guessBoundedNTM witnessIdx counterIdx).trace 1 (fun _ => choice) c).work
      otherIdx) = c.work otherIdx := by
  have hpres := Tape.writeAndMove_readBack_idle_of_ne_start (c.work otherIdx) hread
  by_cases hhalt : c.state = GuessBoundedPhase.done
  · simp [NTM.trace, guessBoundedNTM, hhalt]
  · cases hstate : c.state
    · by_cases hc : (c.work counterIdx).read = Γ.blank
      · simpa [NTM.trace, guessBoundedNTM, hstate, hc, preserveWork, idleWorkDirs]
          using hpres
      · by_cases hchoice : choice = false <;>
          simpa [NTM.trace, guessBoundedNTM, hstate, hc, hchoice, preserveWork,
            idleWorkDirs] using hpres
    · by_cases hc : (c.work counterIdx).read = Γ.blank
      · simpa [NTM.trace, guessBoundedNTM, hstate, hc, preserveWork, idleWorkDirs]
          using hpres
      · simpa [NTM.trace, guessBoundedNTM, hstate, hc, guessWriteWork,
          guessWriteDirs, hwitness, hcounter] using hpres
    · by_cases hwit : (c.work witnessIdx).read = Γ.start <;>
        simpa [NTM.trace, guessBoundedNTM, hstate, hwit, preserveWork,
          rewindWitnessDirs, hwitness] using hpres
    · exact (hhalt hstate).elim

theorem guessBoundedNTM_trace_preserves_other_work
    (witnessIdx counterIdx otherIdx : Fin n) (T : ℕ)
    (choices : Fin T → Bool)
    (c : Cfg n (guessBoundedNTM witnessIdx counterIdx).Q)
    (hwitness : otherIdx ≠ witnessIdx)
    (hcounter : otherIdx ≠ counterIdx)
    (hread : (c.work otherIdx).read ≠ Γ.start) :
    (((guessBoundedNTM witnessIdx counterIdx).trace T choices c).work otherIdx) =
      c.work otherIdx := by
  induction T generalizing c with
  | zero => rfl
  | succ T ih =>
    rw [trace_succ_eq_trace_one (guessBoundedNTM witnessIdx counterIdx) T choices c]
    have hfirst := guessBoundedNTM_trace_one_preserves_other_work witnessIdx counterIdx
      otherIdx (choices ⟨0, by omega⟩) c hwitness hcounter hread
    have hread' :
        (((guessBoundedNTM witnessIdx counterIdx).trace 1
          (fun _ => choices ⟨0, by omega⟩) c).work otherIdx).read ≠ Γ.start := by
      rw [hfirst]
      exact hread
    rw [ih (fun i => choices ⟨i.val + 1, by omega⟩)
      ((guessBoundedNTM witnessIdx counterIdx).trace 1
        (fun _ => choices ⟨0, by omega⟩) c) hread', hfirst]

-- ════════════════════════════════════════════════════════════════════════
-- One-step transition API
-- ════════════════════════════════════════════════════════════════════════

theorem guessBoundedNTM_choose_counter_blank_state
    (witnessIdx counterIdx : Fin n) (choice : Bool)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hcounter : (work counterIdx).read = Γ.blank) :
    ((guessBoundedNTM witnessIdx counterIdx).trace 1 (fun _ => choice)
      { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }).state =
      GuessBoundedPhase.rewind := by
  simp [NTM.trace, guessBoundedNTM, hcounter]

theorem guessBoundedNTM_choose_stop_state
    (witnessIdx counterIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hcounter : (work counterIdx).read ≠ Γ.blank) :
    ((guessBoundedNTM witnessIdx counterIdx).trace 1 (fun _ => false)
      { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }).state =
      GuessBoundedPhase.rewind := by
  simp [NTM.trace, guessBoundedNTM, hcounter]

theorem guessBoundedNTM_choose_continue_state
    (witnessIdx counterIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hcounter : (work counterIdx).read ≠ Γ.blank) :
    ((guessBoundedNTM witnessIdx counterIdx).trace 1 (fun _ => true)
      { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }).state =
      GuessBoundedPhase.write := by
  simp [NTM.trace, guessBoundedNTM, hcounter]

/-- A continuing choose-step preserves the counter tape while moving to the
    `write` state. -/
theorem guessBoundedNTM_choose_continue_preserves_counter
    (witnessIdx counterIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    {used total : ℕ}
    (hcounter : (work counterIdx).hasCounterRemainder used total)
    (hlt : used < total) :
    (((guessBoundedNTM witnessIdx counterIdx).trace 1 (fun _ => true)
      { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }).work
      counterIdx).hasCounterRemainder used total := by
  have hread_one := Tape.hasCounterRemainder_read_one_of_remaining hcounter hlt
  have hread : (work counterIdx).read ≠ Γ.blank := by
    rw [hread_one]
    simp
  have hpreserve :
      (work counterIdx).writeAndMove (TM.readBackWrite (work counterIdx).read)
        (TM.idleDir (work counterIdx).read) = work counterIdx := by
    apply Tape.writeAndMove_readBack_idle_of_ne_start
    rw [hread_one]
    simp
  simp [NTM.trace, guessBoundedNTM, hread, idleWorkDirs, preserveWork]
  change (((work counterIdx).writeAndMove
      (TM.readBackWrite (work counterIdx).read).toΓ
      (TM.idleDir (work counterIdx).read)).hasCounterRemainder used total)
  rw [hpreserve]
  exact hcounter

/-- A continuing choose-step preserves the current witness prefix while moving
    to the `write` state. -/
theorem guessBoundedNTM_choose_continue_preserves_witness
    (witnessIdx counterIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    {bits : List Bool} {used total : ℕ}
    (hwitness : (work witnessIdx).hasBinaryPrefix bits)
    (hcounter : (work counterIdx).hasCounterRemainder used total)
    (hlt : used < total) :
    (((guessBoundedNTM witnessIdx counterIdx).trace 1 (fun _ => true)
      { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }).work
      witnessIdx).hasBinaryPrefix bits := by
  have hread_one := Tape.hasCounterRemainder_read_one_of_remaining hcounter hlt
  have hread : (work counterIdx).read ≠ Γ.blank := by
    rw [hread_one]
    simp
  have hwit_read_ne : (work witnessIdx).read ≠ Γ.start := by
    have hnostart := Tape.hasBinaryPrefix_cells_ne_start hwitness
    exact hnostart (work witnessIdx).head (by rw [hwitness.1]; omega)
  have hpreserve :
      (work witnessIdx).writeAndMove (TM.readBackWrite (work witnessIdx).read)
        (TM.idleDir (work witnessIdx).read) = work witnessIdx :=
    Tape.writeAndMove_readBack_idle_of_ne_start (work witnessIdx) hwit_read_ne
  simp [NTM.trace, guessBoundedNTM, hread, idleWorkDirs, preserveWork]
  change (((work witnessIdx).writeAndMove
      (TM.readBackWrite (work witnessIdx).read).toΓ
      (TM.idleDir (work witnessIdx).read)).hasBinaryPrefix bits)
  rw [hpreserve]
  exact hwitness

/-- A continuing choose-step preserves the witness tape's left-end marker. -/
theorem guessBoundedNTM_choose_continue_preserves_witness_cell0
    (witnessIdx counterIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    {bits : List Bool} {used total : ℕ}
    (hwitness : (work witnessIdx).hasBinaryPrefix bits)
    (hcell0 : (work witnessIdx).cells 0 = Γ.start)
    (hcounter : (work counterIdx).hasCounterRemainder used total)
    (hlt : used < total) :
    (((guessBoundedNTM witnessIdx counterIdx).trace 1 (fun _ => true)
      { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }).work
      witnessIdx).cells 0 = Γ.start := by
  have hread_one := Tape.hasCounterRemainder_read_one_of_remaining hcounter hlt
  have hread : (work counterIdx).read ≠ Γ.blank := by
    rw [hread_one]
    simp
  have hwit_read_ne : (work witnessIdx).read ≠ Γ.start := by
    have hnostart := Tape.hasBinaryPrefix_cells_ne_start hwitness
    exact hnostart (work witnessIdx).head (by rw [hwitness.1]; omega)
  have hpreserve :
      (work witnessIdx).writeAndMove (TM.readBackWrite (work witnessIdx).read)
        (TM.idleDir (work witnessIdx).read) = work witnessIdx :=
    Tape.writeAndMove_readBack_idle_of_ne_start (work witnessIdx) hwit_read_ne
  simp [NTM.trace, guessBoundedNTM, hread, idleWorkDirs, preserveWork]
  change ((work witnessIdx).writeAndMove
      (TM.readBackWrite (work witnessIdx).read).toΓ
      (TM.idleDir (work witnessIdx).read)).cells 0 = Γ.start
  rw [hpreserve]
  exact hcell0

/-- If the guess phase stops by choice, the choose-step preserves the witness
    prefix while entering rewind. -/
theorem guessBoundedNTM_choose_stop_preserves_witness
    (witnessIdx counterIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    {bits : List Bool}
    (hwitness : (work witnessIdx).hasBinaryPrefix bits)
    (hcounter : (work counterIdx).read ≠ Γ.blank) :
    (((guessBoundedNTM witnessIdx counterIdx).trace 1 (fun _ => false)
      { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }).work
      witnessIdx).hasBinaryPrefix bits := by
  have hwit_read_ne : (work witnessIdx).read ≠ Γ.start := by
    have hnostart := Tape.hasBinaryPrefix_cells_ne_start hwitness
    exact hnostart (work witnessIdx).head (by rw [hwitness.1]; omega)
  have hpreserve :
      (work witnessIdx).writeAndMove (TM.readBackWrite (work witnessIdx).read)
        (TM.idleDir (work witnessIdx).read) = work witnessIdx :=
    Tape.writeAndMove_readBack_idle_of_ne_start (work witnessIdx) hwit_read_ne
  simp [NTM.trace, guessBoundedNTM, hcounter, idleWorkDirs, preserveWork]
  change (((work witnessIdx).writeAndMove
      (TM.readBackWrite (work witnessIdx).read).toΓ
      (TM.idleDir (work witnessIdx).read)).hasBinaryPrefix bits)
  rw [hpreserve]
  exact hwitness

/-- If the guess phase stops by choice, the choose-step preserves the witness
    tape's left-end marker. -/
theorem guessBoundedNTM_choose_stop_preserves_witness_cell0
    (witnessIdx counterIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    {bits : List Bool}
    (hwitness : (work witnessIdx).hasBinaryPrefix bits)
    (hcell0 : (work witnessIdx).cells 0 = Γ.start)
    (hcounter : (work counterIdx).read ≠ Γ.blank) :
    (((guessBoundedNTM witnessIdx counterIdx).trace 1 (fun _ => false)
      { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }).work
      witnessIdx).cells 0 = Γ.start := by
  have hwit_read_ne : (work witnessIdx).read ≠ Γ.start := by
    have hnostart := Tape.hasBinaryPrefix_cells_ne_start hwitness
    exact hnostart (work witnessIdx).head (by rw [hwitness.1]; omega)
  have hpreserve :
      (work witnessIdx).writeAndMove (TM.readBackWrite (work witnessIdx).read)
        (TM.idleDir (work witnessIdx).read) = work witnessIdx :=
    Tape.writeAndMove_readBack_idle_of_ne_start (work witnessIdx) hwit_read_ne
  simp [NTM.trace, guessBoundedNTM, hcounter, idleWorkDirs, preserveWork]
  change ((work witnessIdx).writeAndMove
      (TM.readBackWrite (work witnessIdx).read).toΓ
      (TM.idleDir (work witnessIdx).read)).cells 0 = Γ.start
  rw [hpreserve]
  exact hcell0

/-- If the counter is empty, the choose-step is forced into rewind and preserves
    the witness prefix. -/
theorem guessBoundedNTM_choose_counter_blank_preserves_witness
    (witnessIdx counterIdx : Fin n) (choice : Bool)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    {bits : List Bool}
    (hwitness : (work witnessIdx).hasBinaryPrefix bits)
    (hcounter : (work counterIdx).read = Γ.blank) :
    (((guessBoundedNTM witnessIdx counterIdx).trace 1 (fun _ => choice)
      { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }).work
      witnessIdx).hasBinaryPrefix bits := by
  have hwit_read_ne : (work witnessIdx).read ≠ Γ.start := by
    have hnostart := Tape.hasBinaryPrefix_cells_ne_start hwitness
    exact hnostart (work witnessIdx).head (by rw [hwitness.1]; omega)
  have hpreserve :
      (work witnessIdx).writeAndMove (TM.readBackWrite (work witnessIdx).read)
        (TM.idleDir (work witnessIdx).read) = work witnessIdx :=
    Tape.writeAndMove_readBack_idle_of_ne_start (work witnessIdx) hwit_read_ne
  simp [NTM.trace, guessBoundedNTM, hcounter, idleWorkDirs, preserveWork]
  change (((work witnessIdx).writeAndMove
      (TM.readBackWrite (work witnessIdx).read).toΓ
      (TM.idleDir (work witnessIdx).read)).hasBinaryPrefix bits)
  rw [hpreserve]
  exact hwitness

/-- If the counter is empty, the choose-step preserves the witness tape's
    left-end marker. -/
theorem guessBoundedNTM_choose_counter_blank_preserves_witness_cell0
    (witnessIdx counterIdx : Fin n) (choice : Bool)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    {bits : List Bool}
    (hwitness : (work witnessIdx).hasBinaryPrefix bits)
    (hcell0 : (work witnessIdx).cells 0 = Γ.start)
    (hcounter : (work counterIdx).read = Γ.blank) :
    (((guessBoundedNTM witnessIdx counterIdx).trace 1 (fun _ => choice)
      { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }).work
      witnessIdx).cells 0 = Γ.start := by
  have hwit_read_ne : (work witnessIdx).read ≠ Γ.start := by
    have hnostart := Tape.hasBinaryPrefix_cells_ne_start hwitness
    exact hnostart (work witnessIdx).head (by rw [hwitness.1]; omega)
  have hpreserve :
      (work witnessIdx).writeAndMove (TM.readBackWrite (work witnessIdx).read)
        (TM.idleDir (work witnessIdx).read) = work witnessIdx :=
    Tape.writeAndMove_readBack_idle_of_ne_start (work witnessIdx) hwit_read_ne
  simp [NTM.trace, guessBoundedNTM, hcounter, idleWorkDirs, preserveWork]
  change ((work witnessIdx).writeAndMove
      (TM.readBackWrite (work witnessIdx).read).toΓ
      (TM.idleDir (work witnessIdx).read)).cells 0 = Γ.start
  rw [hpreserve]
  exact hcell0

theorem guessBoundedNTM_write_counter_blank_state
    (witnessIdx counterIdx : Fin n) (choice : Bool)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hcounter : (work counterIdx).read = Γ.blank) :
    ((guessBoundedNTM witnessIdx counterIdx).trace 1 (fun _ => choice)
      { state := GuessBoundedPhase.write, input := inp, work := work, output := out }).state =
      GuessBoundedPhase.rewind := by
  simp [NTM.trace, guessBoundedNTM, hcounter]

theorem guessBoundedNTM_write_consume_state
    (witnessIdx counterIdx : Fin n) (choice : Bool)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hcounter : (work counterIdx).read ≠ Γ.blank) :
    ((guessBoundedNTM witnessIdx counterIdx).trace 1 (fun _ => choice)
      { state := GuessBoundedPhase.write, input := inp, work := work, output := out }).state =
      GuessBoundedPhase.choose := by
  simp [NTM.trace, guessBoundedNTM, hcounter]

/-- In the writing state, if the counter tape has remaining unary marks, one
    NTM step consumes exactly one mark from the counter. -/
theorem guessBoundedNTM_write_consumes_counter
    (witnessIdx counterIdx : Fin n) (hne : witnessIdx ≠ counterIdx)
    (choice : Bool) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    {used total : ℕ}
    (hcounter : (work counterIdx).hasCounterRemainder used total)
    (hlt : used < total) :
    (((guessBoundedNTM witnessIdx counterIdx).trace 1 (fun _ => choice)
      { state := GuessBoundedPhase.write, input := inp, work := work, output := out }).work
      counterIdx).hasCounterRemainder (used + 1) total := by
  have hread : (work counterIdx).read ≠ Γ.blank := by
    rw [Tape.hasCounterRemainder_read_one_of_remaining hcounter hlt]
    simp
  simp [NTM.trace, guessBoundedNTM, hread, guessWriteWork, guessWriteDirs,
    Ne.symm hne, Tape.hasCounterRemainder_consume hcounter hlt]

/-- In the writing state, the witness tape receives the chosen bit and advances
    to the next blank cell. -/
theorem guessBoundedNTM_write_extends_witness
    (witnessIdx counterIdx : Fin n)
    (choice : Bool) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    {bits : List Bool}
    (hwitness : (work witnessIdx).hasBinaryPrefix bits)
    (hcounter : (work counterIdx).read ≠ Γ.blank) :
    (((guessBoundedNTM witnessIdx counterIdx).trace 1 (fun _ => choice)
      { state := GuessBoundedPhase.write, input := inp, work := work, output := out }).work
      witnessIdx).hasBinaryPrefix (bits ++ [choice]) := by
  simp [NTM.trace, guessBoundedNTM, hcounter, guessWriteWork, guessWriteDirs]
  change ((work witnessIdx).writeAndMove (Γw.ofBool choice).toΓ Dir3.right).hasBinaryPrefix
    (bits ++ [choice])
  rw [Γw.ofBool_toΓ]
  exact Tape.hasBinaryPrefix_write_bit choice hwitness

/-- In the writing state, writing a bit preserves the witness tape's left-end
    marker. -/
theorem guessBoundedNTM_write_preserves_witness_cell0
    (witnessIdx counterIdx : Fin n)
    (choice : Bool) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    {bits : List Bool}
    (hwitness : (work witnessIdx).hasBinaryPrefix bits)
    (hcell0 : (work witnessIdx).cells 0 = Γ.start)
    (hcounter : (work counterIdx).read ≠ Γ.blank) :
    (((guessBoundedNTM witnessIdx counterIdx).trace 1 (fun _ => choice)
      { state := GuessBoundedPhase.write, input := inp, work := work, output := out }).work
      witnessIdx).cells 0 = Γ.start := by
  simp [NTM.trace, guessBoundedNTM, hcounter, guessWriteWork, guessWriteDirs]
  change ((work witnessIdx).writeAndMove (Γw.ofBool choice).toΓ Dir3.right).cells 0 =
    Γ.start
  rw [Γw.ofBool_toΓ]
  exact Tape.hasBinaryPrefix_write_bit_cell0 choice hwitness hcell0

/-- The normal two-step continue/write sequence consumes one counter mark.
    This is the induction step used by bounded guessing proofs. -/
theorem guessBoundedNTM_continue_write_consumes_counter
    (witnessIdx counterIdx : Fin n) (hne : witnessIdx ≠ counterIdx)
    (bit : Bool) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    {used total : ℕ}
    (hcounter : (work counterIdx).hasCounterRemainder used total)
    (hlt : used < total) :
    (((guessBoundedNTM witnessIdx counterIdx).trace 2
      (fun i => if i.val = 0 then true else bit)
      { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }).work
      counterIdx).hasCounterRemainder (used + 1) total := by
  let tm := guessBoundedNTM witnessIdx counterIdx
  let c0 : Cfg n tm.Q :=
    { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }
  let choices : Fin 2 → Bool := fun i => if i.val = 0 then true else bit
  let c1 := tm.trace 1 (fun _ => true) c0
  have hstate1 : c1.state = GuessBoundedPhase.write := by
    dsimp [c1, c0, tm]
    apply guessBoundedNTM_choose_continue_state
    rw [Tape.hasCounterRemainder_read_one_of_remaining hcounter hlt]
    simp
  have hcounter1 : (c1.work counterIdx).hasCounterRemainder used total := by
    dsimp [c1, c0, tm]
    exact guessBoundedNTM_choose_continue_preserves_counter
      witnessIdx counterIdx inp work out hcounter hlt
  change ((tm.trace 2 choices c0).work counterIdx).hasCounterRemainder (used + 1) total
  rw [trace_two_eq tm choices c0]
  change ((tm.trace 1 (fun _ => bit) c1).work counterIdx).hasCounterRemainder (used + 1) total
  cases hcfg : c1 with
  | mk state1 inp1 work1 out1 =>
    rw [hcfg] at hstate1 hcounter1
    change state1 = GuessBoundedPhase.write at hstate1
    change (work1 counterIdx).hasCounterRemainder used total at hcounter1
    subst state1
    exact guessBoundedNTM_write_consumes_counter witnessIdx counterIdx hne bit
      inp1 work1 out1 hcounter1 hlt

/-- The normal two-step continue/write sequence returns to the `choose` state. -/
theorem guessBoundedNTM_continue_write_state
    (witnessIdx counterIdx : Fin n)
    (bit : Bool) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    {used total : ℕ}
    (hcounter : (work counterIdx).hasCounterRemainder used total)
    (hlt : used < total) :
    ((guessBoundedNTM witnessIdx counterIdx).trace 2
      (fun i => if i.val = 0 then true else bit)
      { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }).state =
      GuessBoundedPhase.choose := by
  let tm := guessBoundedNTM witnessIdx counterIdx
  let c0 : Cfg n tm.Q :=
    { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }
  let choices : Fin 2 → Bool := fun i => if i.val = 0 then true else bit
  let c1 := tm.trace 1 (fun _ => true) c0
  have hstate1 : c1.state = GuessBoundedPhase.write := by
    dsimp [c1, c0, tm]
    apply guessBoundedNTM_choose_continue_state
    rw [Tape.hasCounterRemainder_read_one_of_remaining hcounter hlt]
    simp
  have hcounter1 : (c1.work counterIdx).hasCounterRemainder used total := by
    dsimp [c1, c0, tm]
    exact guessBoundedNTM_choose_continue_preserves_counter
      witnessIdx counterIdx inp work out hcounter hlt
  have hcounter1_read : (c1.work counterIdx).read ≠ Γ.blank := by
    rw [Tape.hasCounterRemainder_read_one_of_remaining hcounter1 hlt]
    simp
  change (tm.trace 2 choices c0).state = GuessBoundedPhase.choose
  rw [trace_two_eq tm choices c0]
  change (tm.trace 1 (fun _ => bit) c1).state = GuessBoundedPhase.choose
  cases hcfg : c1 with
  | mk state1 inp1 work1 out1 =>
    rw [hcfg] at hstate1 hcounter1_read
    change state1 = GuessBoundedPhase.write at hstate1
    change (work1 counterIdx).read ≠ Γ.blank at hcounter1_read
    subst state1
    exact guessBoundedNTM_write_consume_state witnessIdx counterIdx bit
      inp1 work1 out1 hcounter1_read

/-- The normal two-step continue/write sequence appends the chosen bit to the
    witness tape. -/
theorem guessBoundedNTM_continue_write_extends_witness
    (witnessIdx counterIdx : Fin n)
    (bit : Bool) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    {bits : List Bool} {used total : ℕ}
    (hwitness : (work witnessIdx).hasBinaryPrefix bits)
    (hcounter : (work counterIdx).hasCounterRemainder used total)
    (hlt : used < total) :
    (((guessBoundedNTM witnessIdx counterIdx).trace 2
      (fun i => if i.val = 0 then true else bit)
      { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }).work
      witnessIdx).hasBinaryPrefix (bits ++ [bit]) := by
  let tm := guessBoundedNTM witnessIdx counterIdx
  let c0 : Cfg n tm.Q :=
    { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }
  let choices : Fin 2 → Bool := fun i => if i.val = 0 then true else bit
  let c1 := tm.trace 1 (fun _ => true) c0
  have hstate1 : c1.state = GuessBoundedPhase.write := by
    dsimp [c1, c0, tm]
    apply guessBoundedNTM_choose_continue_state
    rw [Tape.hasCounterRemainder_read_one_of_remaining hcounter hlt]
    simp
  have hwitness1 : (c1.work witnessIdx).hasBinaryPrefix bits := by
    dsimp [c1, c0, tm]
    exact guessBoundedNTM_choose_continue_preserves_witness
      witnessIdx counterIdx inp work out hwitness hcounter hlt
  have hcounter1_read : (c1.work counterIdx).read ≠ Γ.blank := by
    have hcounter1 : (c1.work counterIdx).hasCounterRemainder used total := by
      dsimp [c1, c0, tm]
      exact guessBoundedNTM_choose_continue_preserves_counter
        witnessIdx counterIdx inp work out hcounter hlt
    rw [Tape.hasCounterRemainder_read_one_of_remaining hcounter1 hlt]
    simp
  change ((tm.trace 2 choices c0).work witnessIdx).hasBinaryPrefix (bits ++ [bit])
  rw [trace_two_eq tm choices c0]
  change ((tm.trace 1 (fun _ => bit) c1).work witnessIdx).hasBinaryPrefix (bits ++ [bit])
  cases hcfg : c1 with
  | mk state1 inp1 work1 out1 =>
    rw [hcfg] at hstate1 hwitness1 hcounter1_read
    change state1 = GuessBoundedPhase.write at hstate1
    change (work1 witnessIdx).hasBinaryPrefix bits at hwitness1
    change (work1 counterIdx).read ≠ Γ.blank at hcounter1_read
    subst state1
    exact guessBoundedNTM_write_extends_witness witnessIdx counterIdx bit
      inp1 work1 out1 hwitness1 hcounter1_read

/-- The normal two-step continue/write sequence preserves the witness tape's
    left-end marker. -/
theorem guessBoundedNTM_continue_write_preserves_witness_cell0
    (witnessIdx counterIdx : Fin n)
    (bit : Bool) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    {bits : List Bool} {used total : ℕ}
    (hwitness : (work witnessIdx).hasBinaryPrefix bits)
    (hcell0 : (work witnessIdx).cells 0 = Γ.start)
    (hcounter : (work counterIdx).hasCounterRemainder used total)
    (hlt : used < total) :
    (((guessBoundedNTM witnessIdx counterIdx).trace 2
      (fun i => if i.val = 0 then true else bit)
      { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }).work
      witnessIdx).cells 0 = Γ.start := by
  let tm := guessBoundedNTM witnessIdx counterIdx
  let c0 : Cfg n tm.Q :=
    { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }
  let choices : Fin 2 → Bool := fun i => if i.val = 0 then true else bit
  let c1 := tm.trace 1 (fun _ => true) c0
  have hstate1 : c1.state = GuessBoundedPhase.write := by
    dsimp [c1, c0, tm]
    apply guessBoundedNTM_choose_continue_state
    rw [Tape.hasCounterRemainder_read_one_of_remaining hcounter hlt]
    simp
  have hwitness1 : (c1.work witnessIdx).hasBinaryPrefix bits := by
    dsimp [c1, c0, tm]
    exact guessBoundedNTM_choose_continue_preserves_witness
      witnessIdx counterIdx inp work out hwitness hcounter hlt
  have hcell01 : (c1.work witnessIdx).cells 0 = Γ.start := by
    dsimp [c1, c0, tm]
    exact guessBoundedNTM_choose_continue_preserves_witness_cell0
      witnessIdx counterIdx inp work out hwitness hcell0 hcounter hlt
  have hcounter1_read : (c1.work counterIdx).read ≠ Γ.blank := by
    have hcounter1 : (c1.work counterIdx).hasCounterRemainder used total := by
      dsimp [c1, c0, tm]
      exact guessBoundedNTM_choose_continue_preserves_counter
        witnessIdx counterIdx inp work out hcounter hlt
    rw [Tape.hasCounterRemainder_read_one_of_remaining hcounter1 hlt]
    simp
  change ((tm.trace 2 choices c0).work witnessIdx).cells 0 = Γ.start
  rw [trace_two_eq tm choices c0]
  change ((tm.trace 1 (fun _ => bit) c1).work witnessIdx).cells 0 = Γ.start
  cases hcfg : c1 with
  | mk state1 inp1 work1 out1 =>
    rw [hcfg] at hstate1 hwitness1 hcell01 hcounter1_read
    change state1 = GuessBoundedPhase.write at hstate1
    change (work1 witnessIdx).hasBinaryPrefix bits at hwitness1
    change (work1 witnessIdx).cells 0 = Γ.start at hcell01
    change (work1 counterIdx).read ≠ Γ.blank at hcounter1_read
    subst state1
    exact guessBoundedNTM_write_preserves_witness_cell0 witnessIdx counterIdx bit
      inp1 work1 out1 hwitness1 hcell01 hcounter1_read

/-- Bundled invariant update for one successful continue/write iteration. -/
theorem guessBoundedNTM_continue_write_invariants
    (witnessIdx counterIdx : Fin n) (hne : witnessIdx ≠ counterIdx)
    (bit : Bool) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    {bits : List Bool} {used total : ℕ}
    (hwitness : (work witnessIdx).hasBinaryPrefix bits)
    (hcell0 : (work witnessIdx).cells 0 = Γ.start)
    (hcounter : (work counterIdx).hasCounterRemainder used total)
    (hlt : used < total) :
    let c' := (guessBoundedNTM witnessIdx counterIdx).trace 2
      (fun i => if i.val = 0 then true else bit)
      { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }
    c'.state = GuessBoundedPhase.choose ∧
    (c'.work counterIdx).hasCounterRemainder (used + 1) total ∧
    (c'.work witnessIdx).hasBinaryPrefix (bits ++ [bit]) ∧
    (c'.work witnessIdx).cells 0 = Γ.start := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact guessBoundedNTM_continue_write_state witnessIdx counterIdx bit
      inp work out hcounter hlt
  · exact guessBoundedNTM_continue_write_consumes_counter witnessIdx counterIdx hne
      bit inp work out hcounter hlt
  · exact guessBoundedNTM_continue_write_extends_witness witnessIdx counterIdx
      bit inp work out hwitness hcounter hlt
  · exact guessBoundedNTM_continue_write_preserves_witness_cell0 witnessIdx counterIdx
      bit inp work out hwitness hcell0 hcounter hlt

theorem guessBoundedNTM_rewind_at_start_state
    (witnessIdx counterIdx : Fin n) (choice : Bool)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hwitness : (work witnessIdx).read = Γ.start) :
    ((guessBoundedNTM witnessIdx counterIdx).trace 1 (fun _ => choice)
      { state := GuessBoundedPhase.rewind, input := inp, work := work, output := out }).state =
      GuessBoundedPhase.done := by
  simp [NTM.trace, guessBoundedNTM, hwitness]

theorem guessBoundedNTM_rewind_left_state
    (witnessIdx counterIdx : Fin n) (choice : Bool)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hwitness : (work witnessIdx).read ≠ Γ.start) :
    ((guessBoundedNTM witnessIdx counterIdx).trace 1 (fun _ => choice)
      { state := GuessBoundedPhase.rewind, input := inp, work := work, output := out }).state =
      GuessBoundedPhase.rewind := by
  simp [NTM.trace, guessBoundedNTM, hwitness]

private theorem guessBoundedNTM_rewind_step_left
    (witnessIdx counterIdx : Fin n) (choice : Bool)
    (c : Cfg n (guessBoundedNTM witnessIdx counterIdx).Q)
    (hstate : c.state = GuessBoundedPhase.rewind)
    (hread : (c.work witnessIdx).read ≠ Γ.start) :
    ∃ c',
      (guessBoundedNTM witnessIdx counterIdx).trace 1 (fun _ => choice) c = c' ∧
      c'.state = GuessBoundedPhase.rewind ∧
      (c'.work witnessIdx).head = (c.work witnessIdx).head - 1 ∧
      (c'.work witnessIdx).cells = (c.work witnessIdx).cells := by
  simp only [NTM.trace, hstate, guessBoundedNTM, hread]
  refine ⟨_, rfl, rfl, ?_, ?_⟩
  · by_cases h0 : (c.work witnessIdx).head = 0
    · simp [preserveWork, rewindWitnessDirs, TM.moveLeftDir, hread,
        Tape.writeAndMove, Tape.move, Tape.write, h0]
    · simp [preserveWork, rewindWitnessDirs, TM.moveLeftDir, hread,
        Tape.writeAndMove, Tape.move, Tape.write, h0]
  · simp [preserveWork, rewindWitnessDirs, TM.moveLeftDir, hread,
      Tape.writeAndMove, TM.tape_move_cells]
    change ((c.work witnessIdx).write
        ((TM.readBackWrite (c.work witnessIdx).read).toΓ)).cells =
      (c.work witnessIdx).cells
    rw [TM.readBackWrite_toΓ_eq hread]
    simp only [Tape.write, Tape.read]
    split
    · rfl
    · exact Function.update_eq_self _ _

private theorem guessBoundedNTM_rewind_step_base
    (witnessIdx counterIdx : Fin n) (choice : Bool)
    (c : Cfg n (guessBoundedNTM witnessIdx counterIdx).Q)
    (hstate : c.state = GuessBoundedPhase.rewind)
    (hread : (c.work witnessIdx).read = Γ.start)
    (hnostart : ∀ j, j ≥ 1 → (c.work witnessIdx).cells j ≠ Γ.start) :
    ∃ c',
      (guessBoundedNTM witnessIdx counterIdx).trace 1 (fun _ => choice) c = c' ∧
      (guessBoundedNTM witnessIdx counterIdx).halted c' ∧
      (c'.work witnessIdx).head = 1 ∧
      (c'.work witnessIdx).cells = (c.work witnessIdx).cells := by
  have hhead : (c.work witnessIdx).head = 0 := by
    by_contra h
    exact hnostart (c.work witnessIdx).head (by omega) (by rwa [Tape.read] at hread)
  simp only [NTM.trace, hstate, guessBoundedNTM, hread]
  refine ⟨_, rfl, rfl, ?_, ?_⟩
  · simp [preserveWork, rewindWitnessDirs, TM.moveLeftDir, hread,
      Tape.writeAndMove, Tape.move, Tape.write, hhead]
  · simp [preserveWork, rewindWitnessDirs, Tape.writeAndMove, TM.tape_move_cells,
      Tape.write, hhead]

private theorem guessBoundedNTM_rewind_loop (witnessIdx counterIdx : Fin n) :
    ∀ (p : ℕ) (c : Cfg n (guessBoundedNTM witnessIdx counterIdx).Q),
      c.state = GuessBoundedPhase.rewind →
      (c.work witnessIdx).cells 0 = Γ.start →
      (∀ j, j ≥ 1 → (c.work witnessIdx).cells j ≠ Γ.start) →
      (c.work witnessIdx).head = p →
      ∀ choices : Fin (p + 1) → Bool,
        let c' := (guessBoundedNTM witnessIdx counterIdx).trace (p + 1) choices c
        (guessBoundedNTM witnessIdx counterIdx).halted c' ∧
        (c'.work witnessIdx).head = 1 ∧
        (c'.work witnessIdx).cells = (c.work witnessIdx).cells := by
  intro p
  induction p with
  | zero =>
    intro c hstate hcell0 hnostart hhead choices
    have hread : (c.work witnessIdx).read = Γ.start := by
      simp [Tape.read, hhead, hcell0]
    obtain ⟨c', hstep, hhalt, hhead', hcells'⟩ :=
      guessBoundedNTM_rewind_step_base witnessIdx counterIdx
        (choices ⟨0, by omega⟩) c hstate hread hnostart
    have hstep_choices :
        (guessBoundedNTM witnessIdx counterIdx).trace 1 choices c = c' := by
      simpa using hstep
    rw [hstep_choices]
    exact ⟨hhalt, hhead', hcells'⟩
  | succ p ih =>
    intro c hstate hcell0 hnostart hhead choices
    have hread : (c.work witnessIdx).read ≠ Γ.start := by
      simp [Tape.read, hhead]
      exact hnostart (p + 1) (by omega)
    obtain ⟨c1, hstep, hstate1, hhead1, hcells1⟩ :=
      guessBoundedNTM_rewind_step_left witnessIdx counterIdx
        (choices ⟨0, by omega⟩) c hstate hread
    have hhead1' : (c1.work witnessIdx).head = p := by
      rw [hhead1, hhead]
      omega
    have hcell01 : (c1.work witnessIdx).cells 0 = Γ.start := by
      rw [hcells1]
      exact hcell0
    have hnostart1 : ∀ j, j ≥ 1 → (c1.work witnessIdx).cells j ≠ Γ.start := by
      intro j hj
      rw [hcells1]
      exact hnostart j hj
    have htail := ih c1 hstate1 hcell01 hnostart1 hhead1'
      (fun i => choices ⟨i.val + 1, by omega⟩)
    rw [trace_succ_eq_trace_one (guessBoundedNTM witnessIdx counterIdx) (p + 1) choices c]
    rw [hstep]
    exact ⟨htail.1, htail.2.1, by rw [htail.2.2, hcells1]⟩

theorem guessBoundedNTM_rewind_completes_witness
    (witnessIdx counterIdx : Fin n)
    (bits : List Bool)
    (c : Cfg n (guessBoundedNTM witnessIdx counterIdx).Q)
    (hstate : c.state = GuessBoundedPhase.rewind)
    (hwitness : (c.work witnessIdx).hasBinaryPrefix bits)
    (hcell0 : (c.work witnessIdx).cells 0 = Γ.start)
    (choices : Fin (bits.length + 2) → Bool) :
    let c' := (guessBoundedNTM witnessIdx counterIdx).trace (bits.length + 2) choices c
    (guessBoundedNTM witnessIdx counterIdx).halted c' ∧
    (c'.work witnessIdx).hasBinaryString bits ∧
    (c'.work witnessIdx).cells 0 = Γ.start := by
  have hnostart : ∀ j, j ≥ 1 → (c.work witnessIdx).cells j ≠ Γ.start :=
    Tape.hasBinaryPrefix_cells_ne_start hwitness
  have hhead : (c.work witnessIdx).head = bits.length + 1 := hwitness.1
  have hloop := guessBoundedNTM_rewind_loop witnessIdx counterIdx (bits.length + 1)
    c hstate hcell0 hnostart hhead choices
  exact ⟨hloop.1, Tape.hasBinaryPrefix_to_hasBinaryString hwitness hloop.2.1 hloop.2.2,
    by rw [hloop.2.2]; exact hcell0⟩

/-- If the counter is already blank in the choose state, the guess phase is
    forced to stop and then rewind the current witness prefix. -/
theorem guessBoundedNTM_choose_counter_blank_completes_witness
    (witnessIdx counterIdx : Fin n)
    (bits : List Bool)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hwitness : (work witnessIdx).hasBinaryPrefix bits)
    (hcell0 : (work witnessIdx).cells 0 = Γ.start)
    (hcounter : (work counterIdx).read = Γ.blank)
    (choices : Fin (bits.length + 3) → Bool) :
    let c' := (guessBoundedNTM witnessIdx counterIdx).trace (bits.length + 3) choices
      { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }
    (guessBoundedNTM witnessIdx counterIdx).halted c' ∧
    (c'.work witnessIdx).hasBinaryString bits ∧
    (c'.work witnessIdx).cells 0 = Γ.start := by
  let tm := guessBoundedNTM witnessIdx counterIdx
  let c0 : Cfg n tm.Q :=
    { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }
  let c1 := tm.trace 1 (fun _ => choices ⟨0, by omega⟩) c0
  have hsplit := trace_succ_eq_trace_one tm (bits.length + 2) choices c0
  have hstate1 : c1.state = GuessBoundedPhase.rewind := by
    dsimp [c1, c0, tm]
    exact guessBoundedNTM_choose_counter_blank_state witnessIdx counterIdx
      (choices ⟨0, by omega⟩) inp work out hcounter
  have hwitness1 : (c1.work witnessIdx).hasBinaryPrefix bits := by
    dsimp [c1, c0, tm]
    exact guessBoundedNTM_choose_counter_blank_preserves_witness witnessIdx counterIdx
      (choices ⟨0, by omega⟩) inp work out hwitness hcounter
  have hcell01 : (c1.work witnessIdx).cells 0 = Γ.start := by
    dsimp [c1, c0, tm]
    exact guessBoundedNTM_choose_counter_blank_preserves_witness_cell0 witnessIdx counterIdx
      (choices ⟨0, by omega⟩) inp work out hwitness hcell0 hcounter
  have hrewind :=
    guessBoundedNTM_rewind_completes_witness witnessIdx counterIdx bits c1
      hstate1 hwitness1 hcell01 (fun i => choices ⟨i.val + 1, by omega⟩)
  change tm.halted (tm.trace (bits.length + 3) choices c0) ∧
    ((tm.trace (bits.length + 3) choices c0).work witnessIdx).hasBinaryString bits ∧
    ((tm.trace (bits.length + 3) choices c0).work witnessIdx).cells 0 = Γ.start
  rw [hsplit]
  exact hrewind

/-- If the first choice from `choose` is `false`, the guess phase stops early
    and rewinds the current witness prefix. -/
theorem guessBoundedNTM_choose_stop_completes_witness
    (witnessIdx counterIdx : Fin n)
    (bits : List Bool)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hwitness : (work witnessIdx).hasBinaryPrefix bits)
    (hcell0 : (work witnessIdx).cells 0 = Γ.start)
    (hcounter : (work counterIdx).read ≠ Γ.blank)
    (choices : Fin (bits.length + 3) → Bool)
    (hchoice : choices ⟨0, by omega⟩ = false) :
    let c' := (guessBoundedNTM witnessIdx counterIdx).trace (bits.length + 3) choices
      { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }
    (guessBoundedNTM witnessIdx counterIdx).halted c' ∧
    (c'.work witnessIdx).hasBinaryString bits ∧
    (c'.work witnessIdx).cells 0 = Γ.start := by
  let tm := guessBoundedNTM witnessIdx counterIdx
  let c0 : Cfg n tm.Q :=
    { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }
  let c1 := tm.trace 1 (fun _ => choices ⟨0, by omega⟩) c0
  have hsplit := trace_succ_eq_trace_one tm (bits.length + 2) choices c0
  have hchoices_false :
      (fun _ : Fin 1 => choices 0) = (fun _ : Fin 1 => false) := by
    funext i
    exact hchoice
  have hstate1 : c1.state = GuessBoundedPhase.rewind := by
    dsimp [c1, c0, tm]
    rw [hchoices_false]
    exact guessBoundedNTM_choose_stop_state witnessIdx counterIdx inp work out hcounter
  have hwitness1 : (c1.work witnessIdx).hasBinaryPrefix bits := by
    dsimp [c1, c0, tm]
    rw [hchoices_false]
    exact guessBoundedNTM_choose_stop_preserves_witness witnessIdx counterIdx
      inp work out hwitness hcounter
  have hcell01 : (c1.work witnessIdx).cells 0 = Γ.start := by
    dsimp [c1, c0, tm]
    rw [hchoices_false]
    exact guessBoundedNTM_choose_stop_preserves_witness_cell0 witnessIdx counterIdx
      inp work out hwitness hcell0 hcounter
  have hrewind :=
    guessBoundedNTM_rewind_completes_witness witnessIdx counterIdx bits c1
      hstate1 hwitness1 hcell01 (fun i => choices ⟨i.val + 1, by omega⟩)
  change tm.halted (tm.trace (bits.length + 3) choices c0) ∧
    ((tm.trace (bits.length + 3) choices c0).work witnessIdx).hasBinaryString bits ∧
    ((tm.trace (bits.length + 3) choices c0).work witnessIdx).cells 0 = Γ.start
  rw [hsplit]
  exact hrewind

/-- A simple all-path bound for the bounded guessing loop.

From a prefix of length `prefixLen` and `remaining` available counter marks,
the worst case guesses every remaining bit, takes two steps per bit, then
rewinds the final witness string. -/
def guessBoundedTime (remaining prefixLen : ℕ) : ℕ :=
  3 * remaining + prefixLen + 3

private theorem guessBoundedNTM_choose_reaches_bounded_witness_aux
    (witnessIdx counterIdx : Fin n) (hne : witnessIdx ≠ counterIdx) :
    ∀ (remaining used total : ℕ) (bits : List Bool)
      (c : Cfg n (guessBoundedNTM witnessIdx counterIdx).Q),
      c.state = GuessBoundedPhase.choose →
      used + remaining = total →
      (c.work witnessIdx).hasBinaryPrefix bits →
      (c.work witnessIdx).cells 0 = Γ.start →
      (c.work counterIdx).hasCounterRemainder used total →
      ∀ choices : Fin (guessBoundedTime remaining bits.length) → Bool,
        ∃ t, ∃ ht : t ≤ guessBoundedTime remaining bits.length,
          let c' := (guessBoundedNTM witnessIdx counterIdx).trace t
            (fun i => choices ⟨i.val, Nat.lt_of_lt_of_le i.isLt ht⟩) c
          (guessBoundedNTM witnessIdx counterIdx).halted c' ∧
                      ∃ finalBits : List Bool,
                        finalBits.length ≤ bits.length + remaining ∧
                        (c'.work witnessIdx).hasBinaryString finalBits ∧
                        (c'.work witnessIdx).cells 0 = Γ.start := by
  intro remaining
  induction remaining with
  | zero =>
    intro used total bits c hstate hremaining hwitness hcell0 hcounter choices
    cases c with
    | mk state inp work out =>
      change state = GuessBoundedPhase.choose at hstate
      subst state
      have hused_total : used = total := by omega
      have hcounter_done : (work counterIdx).hasCounterRemainder total total := by
        simpa [hused_total] using hcounter
      have hcounter_read : (work counterIdx).read = Γ.blank :=
        Tape.hasCounterRemainder_read_blank_of_done hcounter_done
      let choicesShort : Fin (bits.length + 3) → Bool := fun i =>
        choices ⟨i.val, by
          have hi := i.isLt
          unfold guessBoundedTime
          omega⟩
      have hexact :=
        guessBoundedNTM_choose_counter_blank_completes_witness
          witnessIdx counterIdx bits inp work out hwitness hcell0 hcounter_read choicesShort
      refine ⟨bits.length + 3, ?_, ?_⟩
      · unfold guessBoundedTime
        omega
      · simpa [choicesShort] using
          And.intro hexact.1
            (Exists.intro bits (And.intro (by omega) hexact.2))
  | succ remaining ih =>
    intro used total bits c hstate hremaining hwitness hcell0 hcounter choices
    cases c with
    | mk state inp work out =>
      change state = GuessBoundedPhase.choose at hstate
      subst state
      have hlt : used < total := by omega
      have hcounter_read : (work counterIdx).read = Γ.one :=
        Tape.hasCounterRemainder_read_one_of_remaining hcounter hlt
      let idx0 : Fin (guessBoundedTime (remaining + 1) bits.length) :=
        ⟨0, by unfold guessBoundedTime; omega⟩
      by_cases hchoice0 : choices idx0 = false
      · have hcounter_not_blank : (work counterIdx).read ≠ Γ.blank := by
          rw [hcounter_read]
          decide
        let choicesShort : Fin (bits.length + 3) → Bool := fun i =>
          choices ⟨i.val, by
            have hi := i.isLt
            unfold guessBoundedTime
            omega⟩
        have hchoiceShort : choicesShort ⟨0, by omega⟩ = false := by
          simpa [choicesShort, idx0] using hchoice0
        have hexact :=
          guessBoundedNTM_choose_stop_completes_witness
            witnessIdx counterIdx bits inp work out hwitness hcell0 hcounter_not_blank
            choicesShort hchoiceShort
        refine ⟨bits.length + 3, ?_, ?_⟩
        · unfold guessBoundedTime
          omega
        · simpa [choicesShort] using
            And.intro hexact.1
              (Exists.intro bits (And.intro (by omega) hexact.2))
      · have hchoice0_true :
            choices idx0 = true := by
          cases hchoice : choices idx0 <;> simp [hchoice] at hchoice0 ⊢
        let bit : Bool := choices ⟨1, by unfold guessBoundedTime; omega⟩
        let choicesTwo : Fin 2 → Bool := fun i =>
          choices ⟨i.val, by
            have hi := i.isLt
            unfold guessBoundedTime
            omega⟩
        let c2 : Cfg n (guessBoundedNTM witnessIdx counterIdx).Q :=
          (guessBoundedNTM witnessIdx counterIdx).trace 2 choicesTwo
            { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }
        have hchoicesTwo :
            choicesTwo = (fun i : Fin 2 => if i.val = 0 then true else bit) := by
          funext i
          by_cases hi0 : i.val = 0
          · have hi : i = ⟨0, by omega⟩ := Fin.ext hi0
            rw [hi]
            simpa [choicesTwo, bit, idx0] using hchoice0_true
          · have hi1 : i.val = 1 := by omega
            have hi : i = ⟨1, by omega⟩ := Fin.ext hi1
            rw [hi]
            simp [choicesTwo, bit]
        have hinvCanonical :=
          guessBoundedNTM_continue_write_invariants witnessIdx counterIdx hne bit
            inp work out hwitness hcell0 hcounter hlt
        have hinv :
            c2.state = GuessBoundedPhase.choose ∧
            (c2.work counterIdx).hasCounterRemainder (used + 1) total ∧
            (c2.work witnessIdx).hasBinaryPrefix (bits ++ [bit]) ∧
            (c2.work witnessIdx).cells 0 = Γ.start := by
          simpa [c2, choicesTwo, hchoicesTwo] using hinvCanonical
        have hremaining_tail : used + 1 + remaining = total := by omega
        let choicesTail : Fin (guessBoundedTime remaining (bits ++ [bit]).length) → Bool :=
          fun i => choices ⟨i.val + 2, by
            have hi := i.isLt
            unfold guessBoundedTime at hi ⊢
            simp [List.length_append] at hi ⊢
            omega⟩
        obtain ⟨ttail, httail, htail⟩ :=
          ih (used + 1) total (bits ++ [bit]) c2 hinv.1 hremaining_tail
            hinv.2.2.1 hinv.2.2.2 hinv.2.1 choicesTail
        have ht : ttail + 2 ≤ guessBoundedTime (remaining + 1) bits.length := by
          have httail' := httail
          unfold guessBoundedTime at httail' ⊢
          simp [List.length_append] at httail' ⊢
          omega
        let choicesFull : Fin (ttail + 2) → Bool := fun i =>
          choices ⟨i.val, Nat.lt_of_lt_of_le i.isLt ht⟩
        have hsplit :=
          trace_add_two_eq (guessBoundedNTM witnessIdx counterIdx) ttail choicesFull
            { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }
        have hfirst :
            (fun i : Fin 2 => choicesFull ⟨i.val, by omega⟩) = choicesTwo := by
          funext i
          simp [choicesFull, choicesTwo]
        have htailChoices :
            (fun i : Fin ttail => choicesFull ⟨i.val + 2, by omega⟩) =
              (fun i : Fin ttail =>
                choicesTail ⟨i.val, Nat.lt_of_lt_of_le i.isLt httail⟩) := by
          funext i
          simp [choicesFull, choicesTail]
        refine ⟨ttail + 2, ht, ?_⟩
        rw [hsplit, hfirst, htailChoices]
        obtain ⟨hhalt, finalBits, hlen, hwit, hcell0_final⟩ := htail
        refine ⟨hhalt, finalBits, ?_, hwit, hcell0_final⟩
        simp [List.length_append] at hlen
        omega

/-- From any `choose` configuration with a completed unary counter and a
binary prefix on the witness tape, every path halts within `guessBoundedTime`
and leaves a completed witness string no longer than the prefix plus the
counter bound. -/
theorem guessBoundedNTM_choose_halts_with_bounded_witness
    (witnessIdx counterIdx : Fin n) (hne : witnessIdx ≠ counterIdx)
    (B : ℕ) (bits : List Bool)
    (c : Cfg n (guessBoundedNTM witnessIdx counterIdx).Q)
    (hstate : c.state = GuessBoundedPhase.choose)
    (hwitness : (c.work witnessIdx).hasBinaryPrefix bits)
    (hcell0 : (c.work witnessIdx).cells 0 = Γ.start)
    (hcounter : (c.work counterIdx).hasUnaryCounter B)
    (choices : Fin (guessBoundedTime B bits.length) → Bool) :
    let c' := (guessBoundedNTM witnessIdx counterIdx).trace
      (guessBoundedTime B bits.length) choices c
    (guessBoundedNTM witnessIdx counterIdx).halted c' ∧
    ∃ finalBits : List Bool,
      finalBits.length ≤ bits.length + B ∧
      (c'.work witnessIdx).hasBinaryString finalBits ∧
      (c'.work witnessIdx).cells 0 = Γ.start := by
  let tm := guessBoundedNTM witnessIdx counterIdx
  have hcounter_rem : (c.work counterIdx).hasCounterRemainder 0 B := by
    exact Tape.hasUnaryCounter_iff_remainder_zero.mp hcounter
  obtain ⟨t, ht, hshort⟩ :=
    guessBoundedNTM_choose_reaches_bounded_witness_aux witnessIdx counterIdx hne
      B 0 B bits c hstate (by omega) hwitness hcell0 hcounter_rem choices
  let choicesShort : Fin t → Bool := fun i =>
    choices ⟨i.val, Nat.lt_of_lt_of_le i.isLt ht⟩
  have heq := tm.trace_mono ht (choices := choicesShort) (choices' := choices)
    (c := c) (fun i => by simp [choicesShort]) hshort.1
  change tm.halted (tm.trace (guessBoundedTime B bits.length) choices c) ∧
    ∃ finalBits : List Bool,
      finalBits.length ≤ bits.length + B ∧
      ((tm.trace (guessBoundedTime B bits.length) choices c).work witnessIdx).hasBinaryString
        finalBits ∧
      ((tm.trace (guessBoundedTime B bits.length) choices c).work witnessIdx).cells 0 =
        Γ.start
  rw [heq]
  exact hshort

/-- Hoare-style all-path specification for `guessBoundedNTM`, starting from an
empty binary prefix and a unary counter of length `B`. -/
theorem guessBoundedNTM_hoareTime
    (witnessIdx counterIdx : Fin n) (hne : witnessIdx ≠ counterIdx)
    (B : ℕ) :
    (guessBoundedNTM witnessIdx counterIdx).HoareTime
      (fun _ work _ =>
        (work witnessIdx).hasBinaryPrefix [] ∧
        (work witnessIdx).cells 0 = Γ.start ∧
        (work counterIdx).hasUnaryCounter B)
      (fun _ work _ =>
        (work witnessIdx).hasBoundedBinaryString B)
      (guessBoundedTime B 0) := by
  intro inp work out hpre choices
  let tm := guessBoundedNTM witnessIdx counterIdx
  let c0 : Cfg n tm.Q :=
    { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }
  have hguess :=
    guessBoundedNTM_choose_halts_with_bounded_witness
      witnessIdx counterIdx hne B [] c0 rfl hpre.1 hpre.2.1 hpre.2.2 choices
  change tm.halted (tm.trace (guessBoundedTime B 0) choices c0) ∧
    ((tm.trace (guessBoundedTime B 0) choices c0).work witnessIdx).hasBoundedBinaryString B
  refine ⟨hguess.1, ?_⟩
  obtain ⟨finalBits, hlen, hwitness, _hcell0⟩ := hguess.2
  exact ⟨finalBits, by simpa using hlen, hwitness⟩

/-- Stronger Hoare-style specification for `guessBoundedNTM` that retains the
left-end marker fact needed by later tape consumers. -/
theorem guessBoundedNTM_hoareTime_with_cell0
    (witnessIdx counterIdx : Fin n) (hne : witnessIdx ≠ counterIdx)
    (B : ℕ) :
    (guessBoundedNTM witnessIdx counterIdx).HoareTime
      (fun _ work _ =>
        (work witnessIdx).hasBinaryPrefix [] ∧
        (work witnessIdx).cells 0 = Γ.start ∧
        (work counterIdx).hasUnaryCounter B)
      (fun _ work _ =>
        (work witnessIdx).hasBoundedBinaryString B ∧
        (work witnessIdx).cells 0 = Γ.start)
      (guessBoundedTime B 0) := by
  intro inp work out hpre choices
  let tm := guessBoundedNTM witnessIdx counterIdx
  let c0 : Cfg n tm.Q :=
    { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }
  have hguess :=
    guessBoundedNTM_choose_halts_with_bounded_witness
      witnessIdx counterIdx hne B [] c0 rfl hpre.1 hpre.2.1 hpre.2.2 choices
  change tm.halted (tm.trace (guessBoundedTime B 0) choices c0) ∧
    (((tm.trace (guessBoundedTime B 0) choices c0).work witnessIdx).hasBoundedBinaryString B ∧
      ((tm.trace (guessBoundedTime B 0) choices c0).work witnessIdx).cells 0 = Γ.start)
  refine ⟨hguess.1, ?_⟩
  obtain ⟨finalBits, hlen, hwitness, hcell0_final⟩ := hguess.2
  exact ⟨⟨finalBits, by simpa using hlen, hwitness⟩, hcell0_final⟩

/-- Hoare-style all-path specification for `guessBoundedNTM` with the
    completed witness tape in exact initialized-tape form. -/
theorem guessBoundedNTM_hoareTime_initTape_move_right
    (witnessIdx counterIdx : Fin n) (hne : witnessIdx ≠ counterIdx)
    (B : ℕ) :
    (guessBoundedNTM witnessIdx counterIdx).HoareTime
      (fun _ work _ =>
        (work witnessIdx).hasBinaryPrefix [] ∧
        (work witnessIdx).cells 0 = Γ.start ∧
        (work counterIdx).hasUnaryCounter B)
      (fun _ work _ =>
        ∃ bits : List Bool, bits.length ≤ B ∧
          work witnessIdx = (_root_.Complexity.initTape (bits.map Γ.ofBool)).move Dir3.right)
      (guessBoundedTime B 0) := by
  exact (guessBoundedNTM_hoareTime_with_cell0 witnessIdx counterIdx hne B).consequence
    (fun _ _ _ h => h)
    (fun _ work _ hpost =>
      Tape.hasBoundedBinaryString_eq_initTape_move_right hpost.1 hpost.2)

/-- Framed exact-tape Hoare specification for `guessBoundedNTM`: besides
    producing an exact initialized witness tape, the real input, output, and
    every non-witness/non-counter work tape whose head is already past `▷`
    are preserved unchanged. -/
theorem guessBoundedNTM_hoareTime_initTape_move_right_with_frames
    (witnessIdx counterIdx : Fin n) (hne : witnessIdx ≠ counterIdx)
    (B : ℕ) (input0 output0 : Tape) (frame : Fin n → Tape)
    (hinput_read : input0.read ≠ Γ.start)
    (houtput_read : output0.read ≠ Γ.start)
    (hframe_read : ∀ i, i ≠ witnessIdx → i ≠ counterIdx → (frame i).read ≠ Γ.start) :
    (guessBoundedNTM witnessIdx counterIdx).HoareTime
      (fun inp work out =>
        inp = input0 ∧
        out = output0 ∧
        (∀ i, i ≠ witnessIdx → i ≠ counterIdx → work i = frame i) ∧
        (work witnessIdx).hasBinaryPrefix [] ∧
        (work witnessIdx).cells 0 = Γ.start ∧
        (work counterIdx).hasUnaryCounter B)
      (fun inp work out =>
        inp = input0 ∧
        out = output0 ∧
        (∀ i, i ≠ witnessIdx → i ≠ counterIdx → work i = frame i) ∧
        ∃ bits : List Bool, bits.length ≤ B ∧
          work witnessIdx = (_root_.Complexity.initTape (bits.map Γ.ofBool)).move Dir3.right)
      (guessBoundedTime B 0) := by
  intro inp work out hpre choices
  obtain ⟨hinp, hout, hframe, hwitness, hcell0, hcounter⟩ := hpre
  let tm := guessBoundedNTM witnessIdx counterIdx
  let c0 : Cfg n tm.Q := { state := tm.qstart, input := inp, work := work, output := out }
  have hguess :=
    guessBoundedNTM_hoareTime_with_cell0 witnessIdx counterIdx hne B
      inp work out ⟨hwitness, hcell0, hcounter⟩ choices
  have hinput_pres :
      (tm.trace (guessBoundedTime B 0) choices c0).input = inp := by
    exact guessBoundedNTM_trace_preserves_input witnessIdx counterIdx
      (guessBoundedTime B 0) choices c0 (by
        change inp.read ≠ Γ.start
        rw [hinp]
        exact hinput_read)
  have houtput_pres :
      (tm.trace (guessBoundedTime B 0) choices c0).output = out := by
    exact guessBoundedNTM_trace_preserves_output witnessIdx counterIdx
      (guessBoundedTime B 0) choices c0 (by
        change out.read ≠ Γ.start
        rw [hout]
        exact houtput_read)
  constructor
  · exact hguess.1
  · refine ⟨?_, ?_, ?_, ?_⟩
    · change (tm.trace (guessBoundedTime B 0) choices c0).input = input0
      rw [hinput_pres, hinp]
    · change (tm.trace (guessBoundedTime B 0) choices c0).output = output0
      rw [houtput_pres, hout]
    · intro i hiw hic
      have hwork_pres :
          ((tm.trace (guessBoundedTime B 0) choices c0).work i) = c0.work i := by
        exact guessBoundedNTM_trace_preserves_other_work witnessIdx counterIdx i
          (guessBoundedTime B 0) choices c0 hiw hic
          (by
            change (work i).read ≠ Γ.start
            rw [hframe i hiw hic]
            exact hframe_read i hiw hic)
      change ((tm.trace (guessBoundedTime B 0) choices c0).work i) = frame i
      rw [hwork_pres]
      exact hframe i hiw hic
    · exact Tape.hasBoundedBinaryString_eq_initTape_move_right hguess.2.1 hguess.2.2

private theorem guessBoundedNTM_choose_generates_suffix_aux
    (witnessIdx counterIdx : Fin n) (hne : witnessIdx ≠ counterIdx) :
    ∀ (suffix : List Bool) (remaining used total : ℕ) (bits : List Bool)
      (c : Cfg n (guessBoundedNTM witnessIdx counterIdx).Q),
      suffix.length ≤ remaining →
      c.state = GuessBoundedPhase.choose →
      used + remaining = total →
      (c.work witnessIdx).hasBinaryPrefix bits →
      (c.work witnessIdx).cells 0 = Γ.start →
      (c.work counterIdx).hasCounterRemainder used total →
      ∃ t, t ≤ guessBoundedTime remaining bits.length ∧
        ∃ choices : Fin t → Bool,
          let c' := (guessBoundedNTM witnessIdx counterIdx).trace t choices c
          (guessBoundedNTM witnessIdx counterIdx).halted c' ∧
          (c'.work witnessIdx).hasBinaryString (bits ++ suffix) ∧
          (c'.work witnessIdx).cells 0 = Γ.start := by
  intro suffix
  induction suffix with
  | nil =>
    intro remaining used total bits c _ hstate hremaining hwitness hcell0 hcounter
    cases c with
    | mk state inp work out =>
      change state = GuessBoundedPhase.choose at hstate
      subst state
      by_cases hdone : used = total
      · have hcounter_done : (work counterIdx).hasCounterRemainder total total := by
          simpa [hdone] using hcounter
        have hcounter_read : (work counterIdx).read = Γ.blank :=
          Tape.hasCounterRemainder_read_blank_of_done hcounter_done
        let choicesStop : Fin (bits.length + 3) → Bool := fun _ => false
        have hstop :=
          guessBoundedNTM_choose_counter_blank_completes_witness
            witnessIdx counterIdx bits inp work out hwitness hcell0 hcounter_read choicesStop
        refine ⟨bits.length + 3, ?_, choicesStop, ?_⟩
        · unfold guessBoundedTime
          omega
        · simpa using (And.intro hstop.1 hstop.2)
      · have hlt : used < total := by omega
        have hcounter_read : (work counterIdx).read = Γ.one :=
          Tape.hasCounterRemainder_read_one_of_remaining hcounter hlt
        have hcounter_not_blank : (work counterIdx).read ≠ Γ.blank := by
          rw [hcounter_read]
          decide
        let choicesStop : Fin (bits.length + 3) → Bool := fun _ => false
        have hchoiceStop : choicesStop ⟨0, by omega⟩ = false := rfl
        have hstop :=
          guessBoundedNTM_choose_stop_completes_witness
            witnessIdx counterIdx bits inp work out hwitness hcell0 hcounter_not_blank
            choicesStop hchoiceStop
        refine ⟨bits.length + 3, ?_, choicesStop, ?_⟩
        · unfold guessBoundedTime
          omega
        · simpa using (And.intro hstop.1 hstop.2)
  | cons bit rest ih =>
    intro remaining used total bits c hlen hstate hremaining hwitness hcell0 hcounter
    cases remaining with
    | zero =>
      simp at hlen
    | succ remaining =>
      cases c with
      | mk state inp work out =>
        change state = GuessBoundedPhase.choose at hstate
        subst state
        have hlt : used < total := by omega
        let choicesTwo : Fin 2 → Bool := fun i => if i.val = 0 then true else bit
        let c2 : Cfg n (guessBoundedNTM witnessIdx counterIdx).Q :=
          (guessBoundedNTM witnessIdx counterIdx).trace 2 choicesTwo
            { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }
        have hinvCanonical :=
          guessBoundedNTM_continue_write_invariants witnessIdx counterIdx hne bit
            inp work out hwitness hcell0 hcounter hlt
        have hinv :
            c2.state = GuessBoundedPhase.choose ∧
            (c2.work counterIdx).hasCounterRemainder (used + 1) total ∧
            (c2.work witnessIdx).hasBinaryPrefix (bits ++ [bit]) ∧
            (c2.work witnessIdx).cells 0 = Γ.start := by
          simpa [c2, choicesTwo] using hinvCanonical
        have htail_len : rest.length ≤ remaining := by
          simpa using hlen
        have hremaining_tail : used + 1 + remaining = total := by omega
        obtain ⟨ttail, httail, choicesTail, htail⟩ :=
          ih remaining (used + 1) total (bits ++ [bit]) c2 htail_len
            hinv.1 hremaining_tail hinv.2.2.1 hinv.2.2.2 hinv.2.1
        have ht : ttail + 2 ≤ guessBoundedTime (remaining + 1) bits.length := by
          have httail' := httail
          unfold guessBoundedTime at httail' ⊢
          simp [List.length_append] at httail' ⊢
          omega
        let choicesFull : Fin (ttail + 2) → Bool := fun i =>
          if hsmall : i.val < 2 then
            if i.val = 0 then true else bit
          else
            choicesTail ⟨i.val - 2, by omega⟩
        have hsplit :=
          trace_add_two_eq (guessBoundedNTM witnessIdx counterIdx) ttail choicesFull
            { state := GuessBoundedPhase.choose, input := inp, work := work, output := out }
        have hfirst :
            (fun i : Fin 2 => choicesFull ⟨i.val, by omega⟩) = choicesTwo := by
          funext i
          by_cases hi0 : i.val = 0
          · have hi : i = ⟨0, by omega⟩ := Fin.ext hi0
            rw [hi]
            simp [choicesFull, choicesTwo]
          · have hi1 : i.val = 1 := by omega
            have hi : i = ⟨1, by omega⟩ := Fin.ext hi1
            rw [hi]
            simp [choicesFull, choicesTwo]
        have htailChoices :
            (fun i : Fin ttail => choicesFull ⟨i.val + 2, by omega⟩) = choicesTail := by
          funext i
          simp [choicesFull]
        refine ⟨ttail + 2, ht, choicesFull, ?_⟩
        rw [hsplit, hfirst, htailChoices]
        simpa [List.append_assoc] using htail

/-- Completeness of the bounded guess phase: any suffix within the unary
counter bound can be produced by some nondeterministic path. -/
theorem guessBoundedNTM_choose_generates_witness
    (witnessIdx counterIdx : Fin n) (hne : witnessIdx ≠ counterIdx)
    (B : ℕ) (bits suffix : List Bool)
    (c : Cfg n (guessBoundedNTM witnessIdx counterIdx).Q)
    (hlen : suffix.length ≤ B)
    (hstate : c.state = GuessBoundedPhase.choose)
    (hwitness : (c.work witnessIdx).hasBinaryPrefix bits)
    (hcell0 : (c.work witnessIdx).cells 0 = Γ.start)
    (hcounter : (c.work counterIdx).hasUnaryCounter B) :
    ∃ choices : Fin (guessBoundedTime B bits.length) → Bool,
      let c' := (guessBoundedNTM witnessIdx counterIdx).trace
        (guessBoundedTime B bits.length) choices c
      (guessBoundedNTM witnessIdx counterIdx).halted c' ∧
      (c'.work witnessIdx).hasBinaryString (bits ++ suffix) ∧
      (c'.work witnessIdx).cells 0 = Γ.start := by
  let tm := guessBoundedNTM witnessIdx counterIdx
  have hcounter_rem : (c.work counterIdx).hasCounterRemainder 0 B :=
    Tape.hasUnaryCounter_iff_remainder_zero.mp hcounter
  obtain ⟨t, ht, choicesShort, hshort⟩ :=
    guessBoundedNTM_choose_generates_suffix_aux witnessIdx counterIdx hne
      suffix B 0 B bits c hlen hstate (by omega) hwitness hcell0 hcounter_rem
  let choicesFull : Fin (guessBoundedTime B bits.length) → Bool := fun i =>
    if hi : i.val < t then choicesShort ⟨i.val, hi⟩ else false
  have heq := tm.trace_mono ht (choices := choicesShort) (choices' := choicesFull)
    (c := c) (fun i => by simp [choicesFull, i.isLt]) hshort.1
  refine ⟨choicesFull, ?_⟩
  change tm.halted (tm.trace (guessBoundedTime B bits.length) choicesFull c) ∧
    ((tm.trace (guessBoundedTime B bits.length) choicesFull c).work witnessIdx).hasBinaryString
      (bits ++ suffix) ∧
    ((tm.trace (guessBoundedTime B bits.length) choicesFull c).work witnessIdx).cells 0 =
      Γ.start
  rw [heq]
  exact hshort

/-- Exact-tape form of `guessBoundedNTM_choose_generates_witness`, convenient
    for feeding a chosen witness directly into pair construction. -/
theorem guessBoundedNTM_choose_generates_witness_initTape_move_right
    (witnessIdx counterIdx : Fin n) (hne : witnessIdx ≠ counterIdx)
    (B : ℕ) (bits suffix : List Bool)
    (c : Cfg n (guessBoundedNTM witnessIdx counterIdx).Q)
    (hlen : suffix.length ≤ B)
    (hstate : c.state = GuessBoundedPhase.choose)
    (hwitness : (c.work witnessIdx).hasBinaryPrefix bits)
    (hcell0 : (c.work witnessIdx).cells 0 = Γ.start)
    (hcounter : (c.work counterIdx).hasUnaryCounter B) :
    ∃ choices : Fin (guessBoundedTime B bits.length) → Bool,
      let c' := (guessBoundedNTM witnessIdx counterIdx).trace
        (guessBoundedTime B bits.length) choices c
      (guessBoundedNTM witnessIdx counterIdx).halted c' ∧
      c'.work witnessIdx =
        (_root_.Complexity.initTape ((bits ++ suffix).map Γ.ofBool)).move Dir3.right := by
  obtain ⟨choices, hchoices⟩ :=
    guessBoundedNTM_choose_generates_witness witnessIdx counterIdx hne B bits suffix c
      hlen hstate hwitness hcell0 hcounter
  refine ⟨choices, ?_⟩
  dsimp
  exact ⟨hchoices.1,
    Tape.hasBinaryString_eq_initTape_move_right hchoices.2.1 hchoices.2.2⟩

end NTM

end Complexity
