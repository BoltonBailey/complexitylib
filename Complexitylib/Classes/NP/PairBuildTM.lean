import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
import Complexitylib.Models.TuringMachine.Hoare.Defs
import Complexitylib.Classes.Pairing

/-!
# `pairBuildTM`: construct `pair x y` on a work tape

The DTM `pairBuildTM k yIdx pIdx` assumes:
- `x` lives on the **input tape** (standard layout: head 0 on ▷, `x` in
  cells 1..|x|, blanks beyond),
- `y` lives on **work tape `yIdx`** (same layout: head 0 on ▷, `y` in
  cells 1..|y|, blanks beyond),
- **work tape `pIdx`** is the empty `initTape []`.

After running, work tape `pIdx` carries `pair x y` — the doubled-bits
encoding of `x` followed by the `[false, true]` separator followed by
`y` verbatim — with head positioned at cell `1`, matching the convention
used by the other `rewindWorkTM`-based subroutines.

## Phase structure

```
init        advance every ▷-reading tape past ▷ (one step)
copyX1      if input blank → writeSep1; else write bit to pIdx, advance pIdx
copyX2      write the same bit to pIdx, advance input *and* pIdx
writeSep1   write `false` to pIdx, advance pIdx
writeSep2   write `true`  to pIdx, advance pIdx
copyY       if y blank → rewindP1; else write y-bit to pIdx, advance y+pIdx
rewindP1    if pIdx reads ▷ → rewindP2; else move pIdx left
rewindP2    one extra right step, transition to done (leaves pIdx head=1)
done        halt
```

Total running time: linear in `|x| + |y|` (see `pairBuildTM_hoareTime`).

## Status

This file contains the **skeleton**: the machine's transition function and
the `δ_right_of_start` proof are fully worked out, while the correctness
theorem `pairBuildTM_hoareTime` is stated but sorry-gated. Discharging
that sorry is the remaining piece of A1.
-/

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- State type
-- ════════════════════════════════════════════════════════════════════════

inductive PairBuildPhase where
  | init
  | copyX1 | copyX2
  | writeSep1 | writeSep2
  | copyY
  | rewindP1 | rewindP2
  | done
  deriving DecidableEq

instance : Fintype PairBuildPhase where
  elems := {.init, .copyX1, .copyX2, .writeSep1, .writeSep2,
            .copyY, .rewindP1, .rewindP2, .done}
  complete := fun x => by cases x <;> simp

-- ════════════════════════════════════════════════════════════════════════
-- Definition
-- ════════════════════════════════════════════════════════════════════════

variable {k : ℕ}

/-- Build `pair x y` on work tape `pIdx`, reading `x` from the input tape
    and `y` from work tape `yIdx`. Requires `yIdx ≠ pIdx` for the
    construction to make sense; the definition itself is valid for any
    indices. -/
def pairBuildTM (yIdx pIdx : Fin k) : TM k where
  Q := PairBuildPhase
  qstart := .init
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    -- Step 0: advance every tape currently reading ▷ past it.
    -- Input, pIdx, yIdx, and output all start at ▷; `idleDir` sends them right.
    | .init =>
      (.copyX1,
       fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead,
       fun i => idleDir (wHeads i),
       idleDir oHead)
    -- copyX1: "new iteration" state. Decides continue-vs-switch based on input.
    | .copyX1 =>
      if iHead = Γ.blank then
        -- End of x: transition to separator writing.
        (.writeSep1,
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => idleDir (wHeads i),
         idleDir oHead)
      else
        -- Write the current input bit to pIdx, advance pIdx only.
        (.copyX2,
         fun i => if i = pIdx then readBackWrite iHead
                  else readBackWrite (wHeads i),
         readBackWrite oHead,
         idleDir iHead,
         fun i => if i = pIdx then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
    -- copyX2: write the *second* copy of the current bit to pIdx; advance input+pIdx.
    | .copyX2 =>
      (.copyX1,
       fun i => if i = pIdx then readBackWrite iHead
                else readBackWrite (wHeads i),
       readBackWrite oHead,
       Dir3.right,                                           -- input advances
       fun i => if i = pIdx then Dir3.right
                else idleDir (wHeads i),
       idleDir oHead)
    -- writeSep1: write the `false` (= Γw.zero) bit of the separator.
    | .writeSep1 =>
      (.writeSep2,
       fun i => if i = pIdx then Γw.zero else readBackWrite (wHeads i),
       readBackWrite oHead,
       idleDir iHead,
       fun i => if i = pIdx then Dir3.right else idleDir (wHeads i),
       idleDir oHead)
    -- writeSep2: write the `true` (= Γw.one) bit of the separator.
    | .writeSep2 =>
      (.copyY,
       fun i => if i = pIdx then Γw.one else readBackWrite (wHeads i),
       readBackWrite oHead,
       idleDir iHead,
       fun i => if i = pIdx then Dir3.right else idleDir (wHeads i),
       idleDir oHead)
    -- copyY: copy y-bits from work[yIdx] to pIdx until blank.
    | .copyY =>
      if wHeads yIdx = Γ.blank then
        (.rewindP1,
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => idleDir (wHeads i),
         idleDir oHead)
      else
        (.copyY,
         fun i => if i = pIdx then readBackWrite (wHeads yIdx)
                  else readBackWrite (wHeads i),
         readBackWrite oHead,
         idleDir iHead,
         fun i => if i = pIdx then Dir3.right
                  else if i = yIdx then Dir3.right
                  else idleDir (wHeads i),
         idleDir oHead)
    -- rewindP1: move pIdx left until reading ▷.
    | .rewindP1 =>
      if wHeads pIdx = Γ.start then
        (.rewindP2,
         fun i => readBackWrite (wHeads i),
         readBackWrite oHead,
         idleDir iHead,
         fun i => if i = pIdx then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.rewindP1,
         fun i => readBackWrite (wHeads i),
         readBackWrite oHead,
         idleDir iHead,
         fun i => if i = pIdx then Dir3.left else idleDir (wHeads i),
         idleDir oHead)
    -- rewindP2: one more step, go to done. Leaves pIdx head at 1.
    -- (Uses readBackWrite so non-pIdx tapes are preserved even if mid-tape.)
    | .rewindP2 =>
      (.done,
       fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead,
       fun i => idleDir (wHeads i),
       idleDir oHead)
    -- done: halt. δ never actually fires; we just need δ_right_of_start to hold.
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .init =>
      refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
      intro i hwi; exact idleDir_right_of_start hwi
    | .copyX1 =>
      dsimp only []; split
      · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rfl
        · exact idleDir_right_of_start hwi
    | .copyX2 =>
      refine ⟨fun _ => rfl, ?_, idleDir_right_of_start⟩
      intro i hwi; simp only []; split
      · rfl
      · exact idleDir_right_of_start hwi
    | .writeSep1 =>
      refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
      intro i hwi; simp only []; split
      · rfl
      · exact idleDir_right_of_start hwi
    | .writeSep2 =>
      refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
      intro i hwi; simp only []; split
      · rfl
      · exact idleDir_right_of_start hwi
    | .copyY =>
      dsimp only []; split
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; exact idleDir_right_of_start hwi
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []
        split
        · rfl
        · split
          · rfl
          · exact idleDir_right_of_start hwi
    | .rewindP1 =>
      dsimp only []; split
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rfl
        · exact idleDir_right_of_start hwi
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rename_i heq; subst heq; contradiction
        · exact idleDir_right_of_start hwi
    | .rewindP2 =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
             idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- Phase lemmas (building blocks for the main correctness theorem)
-- ════════════════════════════════════════════════════════════════════════

/-- **init step.** From the `.init` state with input, `yIdx`, and `pIdx`
    all at head 0 on ▷, one step transitions to `.copyX1` with all three
    heads at cell 1 and cells unchanged. -/
private theorem pairBuild_init_step {k : ℕ} (yIdx pIdx : Fin k)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hst : c.state = .init)
    (hi0 : c.input.head = 0) (hic0 : c.input.cells 0 = Γ.start)
    (hyi0 : (c.work yIdx).head = 0) (hyic0 : (c.work yIdx).cells 0 = Γ.start)
    (hpi0 : (c.work pIdx).head = 0) (hpic0 : (c.work pIdx).cells 0 = Γ.start) :
    ∃ c', (pairBuildTM yIdx pIdx).step c = some c' ∧
      c'.state = .copyX1 ∧
      c'.input.head = 1 ∧ c'.input.cells = c.input.cells ∧
      (c'.work yIdx).head = 1 ∧ (c'.work yIdx).cells = (c.work yIdx).cells ∧
      (c'.work pIdx).head = 1 ∧ (c'.work pIdx).cells = (c.work pIdx).cells := by
  have hiread : c.input.read = Γ.start := by simp [Tape.read, hi0, hic0]
  have hyread : (c.work yIdx).read = Γ.start := by simp [Tape.read, hyi0, hyic0]
  have hpread : (c.work pIdx).read = Γ.start := by simp [Tape.read, hpi0, hpic0]
  simp only [TM.step, hst, pairBuildTM]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- input.head = 1
    show (c.input.move (idleDir c.input.read)).head = 1
    simp [idleDir, hiread, Tape.move, hi0]
  · -- input.cells unchanged
    exact tape_move_cells _ _
  · -- (work yIdx).head = 1
    show ((c.work yIdx).writeAndMove (readBackWrite (c.work yIdx).read)
          (idleDir (c.work yIdx).read)).head = 1
    simp [idleDir, hyread, Tape.writeAndMove, Tape.write, Tape.move, hyi0]
  · -- (work yIdx).cells unchanged
    show ((c.work yIdx).writeAndMove (readBackWrite (c.work yIdx).read)
          (idleDir (c.work yIdx).read)).cells = (c.work yIdx).cells
    simp [Tape.writeAndMove, tape_move_cells, Tape.write, hyi0]
  · -- (work pIdx).head = 1
    show ((c.work pIdx).writeAndMove (readBackWrite (c.work pIdx).read)
          (idleDir (c.work pIdx).read)).head = 1
    simp [idleDir, hpread, Tape.writeAndMove, Tape.write, Tape.move, hpi0]
  · -- (work pIdx).cells unchanged
    show ((c.work pIdx).writeAndMove (readBackWrite (c.work pIdx).read)
          (idleDir (c.work pIdx).read)).cells = (c.work pIdx).cells
    simp [Tape.writeAndMove, tape_move_cells, Tape.write, hpi0]

/-- **copyX1 halt step.** In `.copyX1` reading blank on input, transition
    to `.writeSep1`. All three tracked tapes unchanged (they're past ▷ so
    `tape_writeAndMove_stable` applies). -/
private theorem pairBuild_copyX1_halt_step {k : ℕ} (yIdx pIdx : Fin k)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hst : c.state = .copyX1) (hread : c.input.read = Γ.blank)
    (hih : c.input.head ≥ 1) (hyh : (c.work yIdx).head ≥ 1)
    (hph : (c.work pIdx).head ≥ 1)
    (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start)
    (hpns : ∀ j, j ≥ 1 → (c.work pIdx).cells j ≠ Γ.start) :
    ∃ c', (pairBuildTM yIdx pIdx).step c = some c' ∧
      c'.state = .writeSep1 ∧
      c'.input = c.input ∧
      c'.work yIdx = c.work yIdx ∧
      c'.work pIdx = c.work pIdx := by
  simp only [TM.step, hst, pairBuildTM, if_pos hread]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · exact tape_move_idleDir_stable c.input hih hins
  · exact tape_writeAndMove_stable (c.work yIdx) hyh hyns
  · exact tape_writeAndMove_stable (c.work pIdx) hph hpns

/-- **copyX1 continue step.** In `.copyX1` reading a data bit on input,
    transition to `.copyX2`, writing that bit to `pIdx`, advancing `pIdx`.
    Input head unchanged; yIdx unchanged. -/
private theorem pairBuild_copyX1_cont_step {k : ℕ} (yIdx pIdx : Fin k)
    (hne : yIdx ≠ pIdx)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hst : c.state = .copyX1) (hread_nb : c.input.read ≠ Γ.blank)
    (hread_ns : c.input.read ≠ Γ.start)
    (hih : c.input.head ≥ 1) (hyh : (c.work yIdx).head ≥ 1)
    (hph : (c.work pIdx).head ≥ 1)
    (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start)
    (_hpns : ∀ j, j ≥ 1 → (c.work pIdx).cells j ≠ Γ.start) :
    ∃ c', (pairBuildTM yIdx pIdx).step c = some c' ∧
      c'.state = .copyX2 ∧
      c'.input = c.input ∧
      c'.work yIdx = c.work yIdx ∧
      (c'.work pIdx).head = (c.work pIdx).head + 1 ∧
      (c'.work pIdx).cells =
        Function.update (c.work pIdx).cells (c.work pIdx).head c.input.read := by
  simp only [TM.step, hst, pairBuildTM, if_neg hread_nb]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact tape_move_idleDir_stable c.input hih hins
  · simp only [if_neg hne]
    exact tape_writeAndMove_stable (c.work yIdx) hyh hyns
  · simp only [↓reduceIte]
    simp [Tape.writeAndMove, Tape.write, Tape.move,
          show (c.work pIdx).head ≠ 0 from by omega]
  · simp only [↓reduceIte]
    rw [readBackWrite_toΓ_eq hread_ns]
    simp [Tape.writeAndMove, tape_move_cells, Tape.write,
          show (c.work pIdx).head ≠ 0 from by omega, Tape.read]

/-- **copyX2 step.** In `.copyX2` (reading the same data bit), transition
    back to `.copyX1`, writing that bit to `pIdx` (second copy), advancing
    both input and `pIdx`. yIdx unchanged. -/
private theorem pairBuild_copyX2_step {k : ℕ} (yIdx pIdx : Fin k)
    (hne : yIdx ≠ pIdx)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hst : c.state = .copyX2)
    (hread_ns : c.input.read ≠ Γ.start)
    (_hih : c.input.head ≥ 1) (hyh : (c.work yIdx).head ≥ 1)
    (hph : (c.work pIdx).head ≥ 1)
    (hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start) :
    ∃ c', (pairBuildTM yIdx pIdx).step c = some c' ∧
      c'.state = .copyX1 ∧
      c'.input.head = c.input.head + 1 ∧
      c'.input.cells = c.input.cells ∧
      c'.work yIdx = c.work yIdx ∧
      (c'.work pIdx).head = (c.work pIdx).head + 1 ∧
      (c'.work pIdx).cells =
        Function.update (c.work pIdx).cells (c.work pIdx).head c.input.read := by
  simp only [TM.step, hst, pairBuildTM]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · show (c.input.move .right).head = c.input.head + 1
    simp [Tape.move]
  · exact tape_move_cells _ _
  · simp only [if_neg hne]
    exact tape_writeAndMove_stable (c.work yIdx) hyh hyns
  · simp only [↓reduceIte]
    simp [Tape.writeAndMove, Tape.write, Tape.move,
          show (c.work pIdx).head ≠ 0 from by omega]
  · simp only [↓reduceIte]
    rw [readBackWrite_toΓ_eq hread_ns]
    simp [Tape.writeAndMove, tape_move_cells, Tape.write,
          show (c.work pIdx).head ≠ 0 from by omega, Tape.read]

/-- **writeSep1 step.** Write `0` (the `false` bit of the separator) to
    pIdx, advancing pIdx. Input and yIdx stable. -/
private theorem pairBuild_writeSep1_step {k : ℕ} (yIdx pIdx : Fin k)
    (hne : yIdx ≠ pIdx)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hst : c.state = .writeSep1)
    (hih : c.input.head ≥ 1) (hyh : (c.work yIdx).head ≥ 1)
    (hph : (c.work pIdx).head ≥ 1)
    (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start) :
    ∃ c', (pairBuildTM yIdx pIdx).step c = some c' ∧
      c'.state = .writeSep2 ∧
      c'.input = c.input ∧
      c'.work yIdx = c.work yIdx ∧
      (c'.work pIdx).head = (c.work pIdx).head + 1 ∧
      (c'.work pIdx).cells =
        Function.update (c.work pIdx).cells (c.work pIdx).head Γ.zero := by
  simp only [TM.step, hst, pairBuildTM]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact tape_move_idleDir_stable c.input hih hins
  · simp only [if_neg hne]
    exact tape_writeAndMove_stable (c.work yIdx) hyh hyns
  · simp only [↓reduceIte]
    simp [Tape.writeAndMove, Tape.write, Tape.move,
          show (c.work pIdx).head ≠ 0 from by omega]
  · simp only [↓reduceIte]
    simp [Tape.writeAndMove, tape_move_cells, Tape.write,
          show (c.work pIdx).head ≠ 0 from by omega]

/-- **writeSep2 step.** Write `1` (the `true` bit of the separator) to
    pIdx, advancing pIdx. Transition to `.copyY`. -/
private theorem pairBuild_writeSep2_step {k : ℕ} (yIdx pIdx : Fin k)
    (hne : yIdx ≠ pIdx)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hst : c.state = .writeSep2)
    (hih : c.input.head ≥ 1) (hyh : (c.work yIdx).head ≥ 1)
    (hph : (c.work pIdx).head ≥ 1)
    (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start) :
    ∃ c', (pairBuildTM yIdx pIdx).step c = some c' ∧
      c'.state = .copyY ∧
      c'.input = c.input ∧
      c'.work yIdx = c.work yIdx ∧
      (c'.work pIdx).head = (c.work pIdx).head + 1 ∧
      (c'.work pIdx).cells =
        Function.update (c.work pIdx).cells (c.work pIdx).head Γ.one := by
  simp only [TM.step, hst, pairBuildTM]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact tape_move_idleDir_stable c.input hih hins
  · simp only [if_neg hne]
    exact tape_writeAndMove_stable (c.work yIdx) hyh hyns
  · simp only [↓reduceIte]
    simp [Tape.writeAndMove, Tape.write, Tape.move,
          show (c.work pIdx).head ≠ 0 from by omega]
  · simp only [↓reduceIte]
    simp [Tape.writeAndMove, tape_move_cells, Tape.write,
          show (c.work pIdx).head ≠ 0 from by omega]

/-- **copyY halt step.** In `.copyY` with work tape `yIdx` reading blank,
    transition to `.rewindP1`. All tapes stable. -/
private theorem pairBuild_copyY_halt_step {k : ℕ} (yIdx pIdx : Fin k)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hst : c.state = .copyY) (hyread : (c.work yIdx).read = Γ.blank)
    (hih : c.input.head ≥ 1) (hyh : (c.work yIdx).head ≥ 1)
    (hph : (c.work pIdx).head ≥ 1)
    (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start)
    (hpns : ∀ j, j ≥ 1 → (c.work pIdx).cells j ≠ Γ.start) :
    ∃ c', (pairBuildTM yIdx pIdx).step c = some c' ∧
      c'.state = .rewindP1 ∧
      c'.input = c.input ∧
      c'.work yIdx = c.work yIdx ∧
      c'.work pIdx = c.work pIdx := by
  simp only [TM.step, hst, pairBuildTM, if_pos hyread]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · exact tape_move_idleDir_stable c.input hih hins
  · exact tape_writeAndMove_stable (c.work yIdx) hyh hyns
  · exact tape_writeAndMove_stable (c.work pIdx) hph hpns

/-- **copyY continue step.** In `.copyY` with `yIdx` reading a data bit,
    copy that bit to pIdx, advancing both yIdx and pIdx. Input stable. -/
private theorem pairBuild_copyY_cont_step {k : ℕ} (yIdx pIdx : Fin k)
    (hne : yIdx ≠ pIdx)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hst : c.state = .copyY) (hyread_nb : (c.work yIdx).read ≠ Γ.blank)
    (hyread_ns : (c.work yIdx).read ≠ Γ.start)
    (hih : c.input.head ≥ 1) (hyh : (c.work yIdx).head ≥ 1)
    (hph : (c.work pIdx).head ≥ 1)
    (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (_hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start) :
    ∃ c', (pairBuildTM yIdx pIdx).step c = some c' ∧
      c'.state = .copyY ∧
      c'.input = c.input ∧
      (c'.work yIdx).head = (c.work yIdx).head + 1 ∧
      (c'.work yIdx).cells = (c.work yIdx).cells ∧
      (c'.work pIdx).head = (c.work pIdx).head + 1 ∧
      (c'.work pIdx).cells =
        Function.update (c.work pIdx).cells (c.work pIdx).head (c.work yIdx).read := by
  simp only [TM.step, hst, pairBuildTM, if_neg hyread_nb]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact tape_move_idleDir_stable c.input hih hins
  · -- yIdx head advances (yIdx ≠ pIdx, condition picks the else branch, which is Dir3.right)
    simp only [if_neg hne]
    show ((c.work yIdx).writeAndMove (readBackWrite (c.work yIdx).read).toΓ Dir3.right).head
         = (c.work yIdx).head + 1
    simp [Tape.writeAndMove, Tape.write, Tape.move,
          show (c.work yIdx).head ≠ 0 from by omega]
  · -- yIdx cells unchanged (readBackWrite preserves non-▷ symbols)
    simp only [if_neg hne]
    show ((c.work yIdx).writeAndMove (readBackWrite (c.work yIdx).read).toΓ Dir3.right).cells
         = (c.work yIdx).cells
    rw [readBackWrite_toΓ_eq hyread_ns]
    simp [Tape.writeAndMove, tape_move_cells, Tape.write,
          show (c.work yIdx).head ≠ 0 from by omega, Tape.read]
  · -- pIdx head advances
    simp only [↓reduceIte]
    simp [Tape.writeAndMove, Tape.write, Tape.move,
          show (c.work pIdx).head ≠ 0 from by omega]
  · -- pIdx cells updated with yIdx.read
    simp only [↓reduceIte]
    rw [readBackWrite_toΓ_eq hyread_ns]
    simp [Tape.writeAndMove, tape_move_cells, Tape.write,
          show (c.work pIdx).head ≠ 0 from by omega, Tape.read]

/-- **rewindP1 continue step.** pIdx reads non-▷; move pIdx left one cell;
    stay in `.rewindP1`. Input, yIdx, pIdx-cells unchanged. -/
private theorem pairBuild_rewindP1_step_cont {k : ℕ} (yIdx pIdx : Fin k)
    (hne : yIdx ≠ pIdx)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hst : c.state = .rewindP1) (hpread_ns : (c.work pIdx).read ≠ Γ.start)
    (hih : c.input.head ≥ 1) (hyh : (c.work yIdx).head ≥ 1)
    (hph : (c.work pIdx).head ≥ 1)
    (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start) :
    ∃ c', (pairBuildTM yIdx pIdx).step c = some c' ∧
      c'.state = .rewindP1 ∧
      c'.input = c.input ∧
      c'.work yIdx = c.work yIdx ∧
      (c'.work pIdx).head = (c.work pIdx).head - 1 ∧
      (c'.work pIdx).cells = (c.work pIdx).cells := by
  simp only [TM.step, hst, pairBuildTM, if_neg hpread_ns]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact tape_move_idleDir_stable c.input hih hins
  · -- yIdx stable (yIdx ≠ pIdx picks else branch; readBackWrite + idle)
    simp only [if_neg hne]
    exact tape_writeAndMove_stable (c.work yIdx) hyh hyns
  · -- pIdx head = head - 1
    simp only [↓reduceIte]
    simp [Tape.writeAndMove, Tape.write, Tape.move,
          show (c.work pIdx).head ≠ 0 from by omega]
  · -- pIdx cells unchanged (readBackWrite preserves at non-start read)
    simp only [↓reduceIte]
    rw [readBackWrite_toΓ_eq hpread_ns]
    simp [Tape.writeAndMove, tape_move_cells, Tape.write,
          show (c.work pIdx).head ≠ 0 from by omega, Tape.read]

/-- **rewindP1 base step.** pIdx reads ▷ (head=0); transition to
    `.rewindP2` with pIdx advancing to head=1. All other tapes stable. -/
private theorem pairBuild_rewindP1_step_base {k : ℕ} (yIdx pIdx : Fin k)
    (hne : yIdx ≠ pIdx)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hst : c.state = .rewindP1) (hpread : (c.work pIdx).read = Γ.start)
    (hph0 : (c.work pIdx).head = 0)
    (hih : c.input.head ≥ 1) (hyh : (c.work yIdx).head ≥ 1)
    (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start) :
    ∃ c', (pairBuildTM yIdx pIdx).step c = some c' ∧
      c'.state = .rewindP2 ∧
      c'.input = c.input ∧
      c'.work yIdx = c.work yIdx ∧
      (c'.work pIdx).head = 1 ∧
      (c'.work pIdx).cells = (c.work pIdx).cells := by
  simp only [TM.step, hst, pairBuildTM, if_pos hpread]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact tape_move_idleDir_stable c.input hih hins
  · -- yIdx stable (yIdx ≠ pIdx picks else branch)
    simp only [if_neg hne]
    exact tape_writeAndMove_stable (c.work yIdx) hyh hyns
  · -- pIdx head = 1
    simp only [↓reduceIte]
    simp [Tape.writeAndMove, Tape.write, Tape.move, hph0]
  · -- pIdx cells unchanged (write at head=0 is no-op)
    simp only [↓reduceIte]
    simp [Tape.writeAndMove, tape_move_cells, Tape.write, hph0]

/-- **rewindP2 step.** Transition to `.done`; all tapes stable
    (head ≥ 1 and cells ≥ 1 ≠ start). -/
private theorem pairBuild_rewindP2_step {k : ℕ} (yIdx pIdx : Fin k)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hst : c.state = .rewindP2)
    (hih : c.input.head ≥ 1) (hyh : (c.work yIdx).head ≥ 1)
    (hph : (c.work pIdx).head ≥ 1)
    (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start)
    (hpns : ∀ j, j ≥ 1 → (c.work pIdx).cells j ≠ Γ.start) :
    ∃ c', (pairBuildTM yIdx pIdx).step c = some c' ∧
      c'.state = .done ∧
      c'.input = c.input ∧
      c'.work yIdx = c.work yIdx ∧
      c'.work pIdx = c.work pIdx := by
  simp only [TM.step, hst, pairBuildTM]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · exact tape_move_idleDir_stable c.input hih hins
  · exact tape_writeAndMove_stable (c.work yIdx) hyh hyns
  · exact tape_writeAndMove_stable (c.work pIdx) hph hpns

/-- **rewindP1 loop.** From `.rewindP1` with pIdx at head=`p`, in `p+1`
    steps reach `.rewindP2` with pIdx at head=1 and all pIdx/input/yIdx
    cells preserved. -/
private theorem pairBuild_rewindP1_loop {k : ℕ} (yIdx pIdx : Fin k)
    (hne : yIdx ≠ pIdx) :
    ∀ (p : ℕ) (c : Cfg k (pairBuildTM yIdx pIdx).Q),
      c.state = .rewindP1 →
      (c.work pIdx).head = p →
      (c.work pIdx).cells 0 = Γ.start →
      (∀ j, j ≥ 1 → (c.work pIdx).cells j ≠ Γ.start) →
      c.input.head ≥ 1 → (∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) →
      (c.work yIdx).head ≥ 1 →
      (∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start) →
      ∃ c',
        (pairBuildTM yIdx pIdx).reachesIn (p + 1) c c' ∧
        c'.state = .rewindP2 ∧
        c'.input = c.input ∧
        c'.work yIdx = c.work yIdx ∧
        (c'.work pIdx).head = 1 ∧
        (c'.work pIdx).cells = (c.work pIdx).cells := by
  intro p
  induction p with
  | zero =>
    intro c hst hhead hcell0 _ hih hins hyh hyns
    have hpread : (c.work pIdx).read = Γ.start := by
      simp [Tape.read, hhead, hcell0]
    obtain ⟨c', hstep, hst', hinp, hyw, hph, hpcells⟩ :=
      pairBuild_rewindP1_step_base yIdx pIdx hne c hst hpread hhead hih hyh hins hyns
    exact ⟨c', .step hstep .zero, hst', hinp, hyw, hph, hpcells⟩
  | succ p ih =>
    intro c hst hhead hcell0 hnostart hih hins hyh hyns
    have hph_ge : (c.work pIdx).head ≥ 1 := by omega
    have hpread_ns : (c.work pIdx).read ≠ Γ.start := by
      simp only [Tape.read, hhead]; exact hnostart (p + 1) (by omega)
    obtain ⟨c₁, hstep, hst₁, hinp₁, hyw₁, hph₁, hpcells₁⟩ :=
      pairBuild_rewindP1_step_cont yIdx pIdx hne c hst hpread_ns hih hyh hph_ge hins hyns
    have hhead₁ : (c₁.work pIdx).head = p := by rw [hph₁, hhead]; omega
    have hcell0₁ : (c₁.work pIdx).cells 0 = Γ.start := by rw [hpcells₁]; exact hcell0
    have hnostart₁ : ∀ j, j ≥ 1 → (c₁.work pIdx).cells j ≠ Γ.start := by
      intro j hj; rw [hpcells₁]; exact hnostart j hj
    have hih₁ : c₁.input.head ≥ 1 := hinp₁ ▸ hih
    have hins₁ : ∀ j, j ≥ 1 → c₁.input.cells j ≠ Γ.start := by
      intro j hj; rw [hinp₁]; exact hins j hj
    have hyh₁ : (c₁.work yIdx).head ≥ 1 := by rw [hyw₁]; exact hyh
    have hyns₁ : ∀ j, j ≥ 1 → (c₁.work yIdx).cells j ≠ Γ.start := by
      intro j hj; rw [hyw₁]; exact hyns j hj
    obtain ⟨c', hreach, hst', hinp', hyw', hph', hpcells'⟩ :=
      ih c₁ hst₁ hhead₁ hcell0₁ hnostart₁ hih₁ hins₁ hyh₁ hyns₁
    exact ⟨c', .step hstep hreach, hst',
      hinp'.trans hinp₁, hyw'.trans hyw₁, hph',
      by rw [hpcells', hpcells₁]⟩

-- ════════════════════════════════════════════════════════════════════════
-- Correctness specification (proof deferred)

-- ════════════════════════════════════════════════════════════════════════
-- Correctness specification (proof deferred)
-- ════════════════════════════════════════════════════════════════════════

/-- Running-time bound: `pairBuildTM` finishes in `4·|x| + |y| + 8` steps.

    Breakdown:
    - `init`: 1 step.
    - `copyX1`+`copyX2`: 2·|x| + 1 steps (one final `copyX1` detects blank).
    - `writeSep1`+`writeSep2`: 2 steps.
    - `copyY`: |y| + 1 steps.
    - `rewindP1`: one step per cell left from `2|x|+2+|y|+1` to `0`,
      so `2|x|+|y|+3` steps; plus the `rewindP2` step; plus the
      `done` transition step. -/
def pairBuildTime (xLen yLen : ℕ) : ℕ :=
  4 * xLen + 2 * yLen + 10

/-- **`pairBuildTM` correctness.** Given `x` on the input tape and `y` on
    work tape `yIdx` (with `yIdx ≠ pIdx`), `pairBuildTM yIdx pIdx` halts
    leaving work tape `pIdx` carrying `pair x y` (in the cells indexed
    `1..|pair x y|`) with head at cell `1`, within `pairBuildTime` steps.

    This statement is in HoareTime form so it composes with the rest of
    the NTM assembly in A3.

    **Status**: sorry-gated. Discharging this sorry is the remaining
    mechanical proof obligation for A1. -/
theorem pairBuildTM_hoareTime
    {k : ℕ} (yIdx pIdx : Fin k) (_hne : yIdx ≠ pIdx)
    (x y : List Bool) :
    (pairBuildTM yIdx pIdx).HoareTime
      (fun inp work _ =>
        inp = _root_.initTape (x.map Γ.ofBool) ∧
        work yIdx = _root_.initTape (y.map Γ.ofBool) ∧
        work pIdx = _root_.initTape [])
      (fun _ work _ =>
        (work pIdx).head = 1 ∧
        (work pIdx).cells 0 = Γ.start ∧
        (∀ i : ℕ, (h : i < (pair x y).length) →
          (work pIdx).cells (i + 1) = Γ.ofBool ((pair x y)[i]'h)) ∧
        (work pIdx).cells ((pair x y).length + 1) = Γ.blank)
      (pairBuildTime x.length y.length) := by
  sorry

end TM
