import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.UTM.Defs

/-!
# UTM Helper Machines

Small concrete Turing machines used as building blocks for the Universal TM.

## Main definitions

- `TM.writeTM` — write a symbol to output cell 1
- `TM.rewindWorkTM` — rewind a work tape head to cell 1
- `TM.scanRightTM` — scan a work tape right until blank
- `TM.copyInputToWorkTM` — copy input tape contents to a work tape
- `TM.compareWorkTapesTM` — compare two work tapes cell by cell
-/

namespace TM

variable {n : ℕ}

/-- Proof that all-idle directions satisfy `δ_right_of_start`. -/
private theorem ros_allIdle (iHead : Γ) (wHeads : Fin k → Γ) (oHead : Γ) :
    (iHead = Γ.start → idleDir iHead = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → idleDir (wHeads i) = Dir3.right) ∧
    (oHead = Γ.start → idleDir oHead = Dir3.right) :=
  ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩

-- ════════════════════════════════════════════════════════════════════════
-- writeTM: write a symbol to output cell 1 and halt
-- ════════════════════════════════════════════════════════════════════════

inductive WritePhase where
  | rewind | goRight | write | done
  deriving DecidableEq

instance : Fintype WritePhase where
  elems := {.rewind, .goRight, .write, .done}
  complete := fun x => by cases x <;> simp

/-- Write `sym` to output cell 1 and halt.
    Phases: rewind output to ▷ → move right to cell 1 → write → halt. -/
def writeTM (sym : Γw) : TM n where
  Q := WritePhase
  qstart := .rewind
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .rewind =>
      if oHead = Γ.start then
        (.goRight, fun _ => .blank, .blank,
         idleDir iHead, fun i => idleDir (wHeads i), Dir3.right)
      else
        (.rewind, fun _ => .blank, readBackWrite oHead,
         idleDir iHead, fun i => idleDir (wHeads i), Dir3.left)
    | .goRight =>
      (.write, fun _ => .blank, .blank,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .write =>
      (.done, fun _ => .blank, sym,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .rewind =>
      dsimp only []; split
      · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, fun _ => rfl⟩
      · refine ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, ?_⟩
        intro h; next hn => exact absurd h hn
    | .goRight =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
             idleDir_right_of_start⟩
    | .write =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
             idleDir_right_of_start⟩
    | .done => exact ros_allIdle iHead wHeads oHead

abbrev writeOneTM : TM n := writeTM .one
abbrev writeZeroTM : TM n := writeTM .zero

-- ════════════════════════════════════════════════════════════════════════
-- rewindWorkTM: rewind a work tape to cell 1
-- ════════════════════════════════════════════════════════════════════════

inductive RewindPhase where
  | moveLeft | moveRight | done
  deriving DecidableEq

instance : Fintype RewindPhase where
  elems := {.moveLeft, .moveRight, .done}
  complete := fun x => by cases x <;> simp

/-- Rewind work tape `idx` to cell 1 (first data cell after ▷). -/
def rewindWorkTM (idx : Fin n) : TM n where
  Q := RewindPhase
  qstart := .moveLeft
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .moveLeft =>
      if wHeads idx = Γ.start then
        (.moveRight, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = idx then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.moveLeft,
         fun i => readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => if i = idx then Dir3.left else idleDir (wHeads i),
         idleDir oHead)
    | .moveRight =>
        (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .moveLeft =>
      dsimp only []; split
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rfl
        · exact idleDir_right_of_start hwi
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rename_i heq; subst heq; contradiction
        · exact idleDir_right_of_start hwi
    | .moveRight =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
             idleDir_right_of_start⟩
    | .done => exact ros_allIdle iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- scanRightTM: scan a work tape right until blank
-- ════════════════════════════════════════════════════════════════════════

inductive ScanPhase where
  | scanning | done
  deriving DecidableEq

instance : Fintype ScanPhase where
  elems := {.scanning, .done}
  complete := fun x => by cases x <;> simp

/-- Scan work tape `idx` right until finding `Γ.blank`. Preserves tape contents. -/
def scanRightTM (idx : Fin n) : TM n where
  Q := ScanPhase
  qstart := .scanning
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .scanning =>
      if wHeads idx = Γ.blank then
        allIdle .done iHead wHeads oHead
      else
        (.scanning,
         fun i => if i = idx then readBackWrite (wHeads idx) else .blank,
         .blank, idleDir iHead,
         fun i => if i = idx then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .scanning =>
      dsimp only []; split
      · exact ros_allIdle iHead wHeads oHead
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rfl
        · exact idleDir_right_of_start hwi
    | .done => exact ros_allIdle iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- copyInputToWorkTM: copy input tape to a work tape
-- ════════════════════════════════════════════════════════════════════════

inductive CopyPhase where
  | copying | done
  deriving DecidableEq

instance : Fintype CopyPhase where
  elems := {.copying, .done}
  complete := fun x => by cases x <;> simp

/-- Copy input tape data to work tape `idx`. Reads input right, writes to work tape.
    Stops when input reads `Γ.blank`. Skips ▷ at cell 0. -/
def copyInputToWorkTM (idx : Fin n) : TM n where
  Q := CopyPhase
  qstart := .copying
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .copying =>
      if iHead = Γ.blank then
        allIdle .done iHead wHeads oHead
      else
        let w : Γw := match iHead with
          | .zero => .zero | .one => .one | .blank => .blank | .start => .blank
        (.copying,
         fun i => if i = idx then w else .blank,
         .blank, Dir3.right,
         fun i => if i = idx then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .copying =>
      dsimp only []; split
      · exact ros_allIdle iHead wHeads oHead
      · refine ⟨fun _ => rfl, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rfl
        · exact idleDir_right_of_start hwi
    | .done => exact ros_allIdle iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- compareWorkTapesTM: compare two work tapes cell by cell
-- ════════════════════════════════════════════════════════════════════════

inductive ComparePhase where
  | comparing | mismatch | matchDone | done
  deriving DecidableEq

instance : Fintype ComparePhase where
  elems := {.comparing, .mismatch, .matchDone, .done}
  complete := fun x => by cases x <;> simp

/-- Compare work tapes `idx₁` and `idx₂` cell by cell.
    Both advance right together. Stops when both read `Γ.blank`.
    Writes `Γ.one` to output if match, `Γ.zero` if mismatch.
    Assumes output head is at cell 1. -/
def compareWorkTapesTM (idx₁ idx₂ : Fin n) : TM n where
  Q := ComparePhase
  qstart := .comparing
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .comparing =>
      if wHeads idx₁ = Γ.blank ∧ wHeads idx₂ = Γ.blank then
        (.matchDone, fun _ => .blank, .one,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else if wHeads idx₁ = wHeads idx₂ then
        (.comparing,
         fun i => if i = idx₁ then readBackWrite (wHeads idx₁)
                  else if i = idx₂ then readBackWrite (wHeads idx₂)
                  else .blank,
         .blank, idleDir iHead,
         fun i => if i = idx₁ then Dir3.right
                  else if i = idx₂ then Dir3.right
                  else idleDir (wHeads i),
         idleDir oHead)
      else
        (.mismatch, fun _ => .blank, .zero,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .mismatch => allIdle .done iHead wHeads oHead
    | .matchDone => allIdle .done iHead wHeads oHead
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .comparing =>
      dsimp only []; split
      · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
      · split
        · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
          intro i hwi; simp only []; split
          · rfl
          · split
            · rfl
            · exact idleDir_right_of_start hwi
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
                 idleDir_right_of_start⟩
    | .mismatch => exact ros_allIdle iHead wHeads oHead
    | .matchDone => exact ros_allIdle iHead wHeads oHead
    | .done => exact ros_allIdle iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- setupStateTM: parse desc header, copy qstart to state tape, n to scratch
-- ════════════════════════════════════════════════════════════════════════

/-- States for the setup-state machine. Scans the description header on
    work tape 0, copies the qstart one-hot to work tape 1, and writes
    n ones to work tape 3 (scratch).

    Phases:
    1. **skipK**: Scan desc right past k ones, copying each one to state tape 1.
       When desc reads non-one (separator), advance desc past separator, go to copyN.
       After: state tape has k ones at cells 1..k, head at k+1.
    2. **copyN**: Scan desc right past n ones, copying each one to scratch tape 3.
       When desc reads non-one (separator), advance desc past separator, go to skipQhalt.
       After: scratch has n ones at cells 1..n, head at n+1.
    3. **skipQhalt**: Advance desc right while moving state tape left (k-counter).
       When state reads ▷ (cell 0), stop. The forced right-move on ▷ brings
       state to cell 1. This skips k qhalt bits + 1 separator = k+1 cells.
       After: desc at first qstart bit, state at cell 1.
    4. **copyQstart**: Copy desc bits to state tape, advancing both right.
       Stop when state reads Γ.blank (at cell k+1, the sentinel beyond the
       k ones written in Phase 1). This overwrites the k ones with qstart
       one-hot bits.
       After: state tape has qstart one-hot at cells 1..k, blank sentinel at k+1. -/
inductive SetupStatePhase where
  | skipK      -- skip k ones on desc (tape 0), copy to state (tape 1)
  | copyN      -- skip n ones on desc (tape 0), copy to scratch (tape 3)
  | skipQhalt  -- skip qhalt+sep using state tape as k-counter
  | copyQstart -- copy qstart from desc to state, stop at blank sentinel
  | done
  deriving DecidableEq

instance : Fintype SetupStatePhase where
  elems := {.skipK, .copyN, .skipQhalt, .copyQstart, .done}
  complete := fun x => by cases x <;> simp

/-- Parse the desc header on work tape 0, copy qstart one-hot to state tape 1,
    and write n ones to scratch tape 3.

    **Pre**: Desc tape at cell 1 (start of header), state tape at cell 1,
    scratch tape at cell 1.
    **Post**: State tape has qstart one-hot at cells 1..k with blank sentinel
    at k+1. Scratch tape has n ones at cells 1..n. Desc tape head somewhere
    past qstart section. -/
def setupStateTM : TM 4 where
  Q := SetupStatePhase
  qstart := .skipK
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .skipK =>
      if wHeads 0 = Γ.one then
        -- Desc reads one: copy to state tape, advance both desc(0) and state(1) right
        (.skipK,
         fun i => if i.val = 0 then readBackWrite (wHeads 0)
                  else if i.val = 1 then .one
                  else .blank,
         .blank, idleDir iHead,
         fun i => if i.val = 0 then Dir3.right
                  else if i.val = 1 then Dir3.right
                  else idleDir (wHeads i),
         idleDir oHead)
      else
        -- Desc reads separator: advance desc past it, transition to copyN
        (.copyN,
         fun i => if i.val = 0 then readBackWrite (wHeads 0) else .blank,
         .blank, idleDir iHead,
         fun i => if i.val = 0 then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
    | .copyN =>
      if wHeads 0 = Γ.one then
        -- Desc reads one: copy to scratch tape (3), advance both right
        (.copyN,
         fun i => if i.val = 0 then readBackWrite (wHeads 0)
                  else if i.val = 3 then .one
                  else .blank,
         .blank, idleDir iHead,
         fun i => if i.val = 0 then Dir3.right
                  else if i.val = 3 then Dir3.right
                  else idleDir (wHeads i),
         idleDir oHead)
      else
        -- Desc reads separator: advance desc past it, transition to skipQhalt
        (.skipQhalt,
         fun i => if i.val = 0 then readBackWrite (wHeads 0) else .blank,
         .blank, idleDir iHead,
         fun i => if i.val = 0 then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
    | .skipQhalt =>
      if wHeads 1 = Γ.start then
        -- State tape reads ▷ (cell 0): counter exhausted.
        -- Forced to move state right (to cell 1) by δ_right_of_start.
        -- Desc stays (already past qhalt + separator).
        (.copyQstart,
         fun i => if i.val = 0 then readBackWrite (wHeads 0) else .blank,
         .blank, idleDir iHead,
         fun i => if i.val = 1 then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        -- Counter not exhausted: advance desc right, move state left
        (.skipQhalt,
         fun i => if i.val = 0 then readBackWrite (wHeads 0)
                  else if i.val = 1 then readBackWrite (wHeads 1)
                  else .blank,
         .blank, idleDir iHead,
         fun i => if i.val = 0 then Dir3.right
                  else if i.val = 1 then Dir3.left
                  else idleDir (wHeads i),
         idleDir oHead)
    | .copyQstart =>
      if wHeads 1 = Γ.blank then
        -- State tape reads blank sentinel: copy complete
        (.done,
         fun i => if i.val = 0 then readBackWrite (wHeads 0) else .blank,
         .blank, idleDir iHead,
         fun i => idleDir (wHeads i),
         idleDir oHead)
      else
        -- Copy desc bit to state tape, advance both right
        (.copyQstart,
         fun i => if i.val = 0 then readBackWrite (wHeads 0)
                  else if i.val = 1 then readBackWrite (wHeads 0)
                  else .blank,
         .blank, idleDir iHead,
         fun i => if i.val = 0 then Dir3.right
                  else if i.val = 1 then Dir3.right
                  else idleDir (wHeads i),
         idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .skipK =>
      dsimp only []; split
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rfl
        · split
          · rfl
          · exact idleDir_right_of_start hwi
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rfl
        · exact idleDir_right_of_start hwi
    | .copyN =>
      dsimp only []; split
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rfl
        · split
          · rfl
          · exact idleDir_right_of_start hwi
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rfl
        · exact idleDir_right_of_start hwi
    | .skipQhalt =>
      dsimp only []; split
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rfl
        · exact idleDir_right_of_start hwi
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rfl
        · split
          · next hn heq =>
            have : i = (1 : Fin 4) := by ext; exact heq
            subst this; contradiction
          · exact idleDir_right_of_start hwi
    | .copyQstart =>
      dsimp only []; split
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; exact idleDir_right_of_start hwi
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rfl
        · split
          · rfl
          · exact idleDir_right_of_start hwi
    | .done => exact ros_allIdle iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- setupSimTM: write position-0 super-cells and copy x to sim tape
-- ════════════════════════════════════════════════════════════════════════

/-- States for the setup-sim machine. Sets up the simulation tape (work tape 2)
    with position-0 super-cells and copies x with super-cell stride spacing.

    The machine uses scratch tape (work tape 3) which has n ones at cells 1..n
    (written by `setupStateTM`) as a counter for both the position-0 loop and
    the stride loop.

    ## Phase 1: Position-0 super-cells

    All simulated heads start at position 0, and cell 0 of every simulated tape
    is `Γ.start`. So `symToCellPair(.start) = (.one, .one)` and head marker =
    `Γ.one`. Each of the n+2 tapes needs 3 ones (head + hi + lo).

    The machine writes 3 ones per scratch-one (for n work tapes), then 6 extra
    ones (for the 2 fixed tapes: input + output). Total: 3n + 6 = 3*(n+2).

    ## Phase 2: Advance input past separator

    Input head is at the `Γ.blank` separator between desc and x. Advance right
    by 1 to reach x[0] (or blank if x is empty).

    ## Phase 3: Copy x with stride

    For each x bit:
    1. Skip head marker cell on sim (already Γ.blank = head-absent). 1 step.
    2. Write sym_hi = Γ.zero (same for both 0 and 1). 1 step.
    3. Write sym_lo = Γ.ofBool(x[i]). 1 step. Advance input right.
    4. Stride 3*n + 3 cells on sim: rewind scratch, then 3 per scratch-one
       (3*n cells) + 3 extra cells. This skips past all other tapes' slots
       in the current super-cell to reach the next super-cell's input slot. -/
inductive SetupSimPhase where
  -- Phase 1: Position-0 super-cell writing
  | pos0Write1     -- check scratch; if one, write Γ.one to sim; if blank, go to extras
  | pos0Write2     -- write 2nd Γ.one to sim
  | pos0Write3     -- write 3rd Γ.one to sim, advance scratch, loop
  | pos0Extra1     -- write extra one 1 of 6 (for input + output tapes)
  | pos0Extra2
  | pos0Extra3
  | pos0Extra4
  | pos0Extra5
  | pos0Extra6
  -- Phase 2: Advance input
  | advanceInput   -- move input right by 1 (past separator)
  -- Phase 3: Copy x loop
  | checkInput     -- if input = blank → done; else skip head marker on sim
  | writeSymHi     -- write Γ.zero to sim (sym_hi)
  | writeSymLo     -- write sym_lo based on input bit, advance input
  -- Stride sub-machine
  | rewindScratch  -- move scratch left until ▷
  | bounceScratch  -- move scratch right to cell 1, enter stride loop
  | stride1        -- check scratch; if one, advance sim; if blank, go to extras
  | stride2        -- advance sim right
  | stride3        -- advance sim right, advance scratch, loop to stride1
  | strideExtra1   -- extra advance 1 of 3
  | strideExtra2   -- extra advance 2 of 3
  | strideExtra3   -- extra advance 3 of 3, go to checkInput
  -- Done
  | done
  deriving DecidableEq

instance : Fintype SetupSimPhase where
  elems := {.pos0Write1, .pos0Write2, .pos0Write3,
            .pos0Extra1, .pos0Extra2, .pos0Extra3,
            .pos0Extra4, .pos0Extra5, .pos0Extra6,
            .advanceInput, .checkInput, .writeSymHi, .writeSymLo,
            .rewindScratch, .bounceScratch,
            .stride1, .stride2, .stride3,
            .strideExtra1, .strideExtra2, .strideExtra3,
            .done}
  complete := fun x => by cases x <;> simp

-- Helper: idle transition that preserves all cell contents via readBackWrite
def setupIdle (next : SetupSimPhase)
    (iHead : Γ) (wHeads : Fin 4 → Γ) (oHead : Γ) :
    SetupSimPhase × (Fin 4 → Γw) × Γw × Dir3 × (Fin 4 → Dir3) × Dir3 :=
  (next,
   fun i => readBackWrite (wHeads i),
   readBackWrite oHead, idleDir iHead,
   fun i => idleDir (wHeads i),
   idleDir oHead)

private theorem ros_setupIdle (iHead : Γ) (wHeads : Fin 4 → Γ) (oHead : Γ) :
    (iHead = Γ.start → idleDir iHead = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → idleDir (wHeads i) = Dir3.right) ∧
    (oHead = Γ.start → idleDir oHead = Dir3.right) :=
  ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩

-- Helper: advance only sim tape (work 2) right, writing `w` to it.
-- Non-sim tapes use readBackWrite to preserve cell contents.
def simWriteRight (next : SetupSimPhase) (w : Γw)
    (iHead : Γ) (wHeads : Fin 4 → Γ) (oHead : Γ) :
    SetupSimPhase × (Fin 4 → Γw) × Γw × Dir3 × (Fin 4 → Dir3) × Dir3 :=
  (next,
   fun i => if i.val = 2 then w else readBackWrite (wHeads i),
   readBackWrite oHead, idleDir iHead,
   fun i => if i.val = 2 then Dir3.right else idleDir (wHeads i),
   idleDir oHead)

-- Helper: advance sim tape right preserving cell contents
def simAdvanceRight (next : SetupSimPhase)
    (iHead : Γ) (wHeads : Fin 4 → Γ) (oHead : Γ) :
    SetupSimPhase × (Fin 4 → Γw) × Γw × Dir3 × (Fin 4 → Dir3) × Dir3 :=
  simWriteRight next (readBackWrite (wHeads 2)) iHead wHeads oHead

/-- Set up the simulation tape (work tape 2) with position-0 super-cells
    and the input x encoded at the correct super-cell offsets.

    **Pre**: Sim tape at cell 1, scratch tape at cell 1 with n ones,
    input at desc separator (Γ.blank).
    **Post**: Sim tape encodes `superCellsCorrect (initCfg x)`.
    Sim/scratch/input heads at various positions (final rewinds handle cleanup). -/
def setupSimTM : TM 4 where
  Q := SetupSimPhase
  qstart := .pos0Write1
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    -- ══════════════════════════════════════════════════════════════════
    -- Phase 1: Write position-0 super-cells
    -- ══════════════════════════════════════════════════════════════════
    | .pos0Write1 =>
      if wHeads 3 = Γ.one then
        -- Scratch has a one: write first of 3 ones to sim
        simWriteRight .pos0Write2 .one iHead wHeads oHead
      else
        -- Scratch exhausted (n work tapes done): write 6 extras
        setupIdle .pos0Extra1 iHead wHeads oHead
    | .pos0Write2 => simWriteRight .pos0Write3 .one iHead wHeads oHead
    | .pos0Write3 =>
      -- Write 3rd one, advance scratch right, loop back
      (.pos0Write1,
       fun i => if i.val = 2 then Γw.one
                else if i.val = 3 then readBackWrite (wHeads 3)
                else readBackWrite (wHeads i),
       readBackWrite oHead, idleDir iHead,
       fun i => if i.val = 2 then Dir3.right
                else if i.val = 3 then Dir3.right
                else idleDir (wHeads i),
       idleDir oHead)
    -- Extra ones for input tape (3) + output tape (3) at position 0
    | .pos0Extra1 => simWriteRight .pos0Extra2 .one iHead wHeads oHead
    | .pos0Extra2 => simWriteRight .pos0Extra3 .one iHead wHeads oHead
    | .pos0Extra3 => simWriteRight .pos0Extra4 .one iHead wHeads oHead
    | .pos0Extra4 => simWriteRight .pos0Extra5 .one iHead wHeads oHead
    | .pos0Extra5 => simWriteRight .pos0Extra6 .one iHead wHeads oHead
    | .pos0Extra6 => simWriteRight .advanceInput .one iHead wHeads oHead
    -- ══════════════════════════════════════════════════════════════════
    -- Phase 2: Advance input past separator
    -- ══════════════════════════════════════════════════════════════════
    | .advanceInput =>
      (.checkInput,
       fun i => readBackWrite (wHeads i), readBackWrite oHead,
       Dir3.right, -- advance input past Γ.blank separator
       fun i => idleDir (wHeads i),
       idleDir oHead)
    -- ══════════════════════════════════════════════════════════════════
    -- Phase 3: Copy x with stride
    -- ══════════════════════════════════════════════════════════════════
    | .checkInput =>
      if iHead = Γ.blank then
        -- End of x: done
        setupIdle .done iHead wHeads oHead
      else
        -- x bit present: skip head marker on sim (advance sim right)
        simAdvanceRight .writeSymHi iHead wHeads oHead
    | .writeSymHi =>
      -- Write Γ.zero to sim (sym_hi is .zero for both Γ.zero and Γ.one)
      simWriteRight .writeSymLo .zero iHead wHeads oHead
    | .writeSymLo =>
      -- Write sym_lo based on input bit, advance both sim and input
      let w : Γw := if iHead = Γ.one then .one else .zero
      (.rewindScratch,
       fun i => if i.val = 2 then w else readBackWrite (wHeads i),
       readBackWrite oHead, Dir3.right, -- advance input
       fun i => if i.val = 2 then Dir3.right else idleDir (wHeads i),
       idleDir oHead)
    -- ══════════════════════════════════════════════════════════════════
    -- Stride: rewind scratch + advance sim 3*(n+1) cells
    -- ══════════════════════════════════════════════════════════════════
    | .rewindScratch =>
      if wHeads 3 = Γ.start then
        -- Scratch at ▷ (cell 0): bounce right to cell 1
        (.bounceScratch,
         fun i => readBackWrite (wHeads i), readBackWrite oHead, idleDir iHead,
         fun i => if i.val = 3 then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        -- Keep moving scratch left, preserving cells
        (.rewindScratch,
         fun i => if i.val = 3 then readBackWrite (wHeads 3)
                  else readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => if i.val = 3 then Dir3.left else idleDir (wHeads i),
         idleDir oHead)
    | .bounceScratch =>
      -- Scratch at cell 1: enter stride loop (no tape movement this step)
      setupIdle .stride1 iHead wHeads oHead
    | .stride1 =>
      if wHeads 3 = Γ.one then
        -- Scratch one: advance sim right (1st of 3)
        simAdvanceRight .stride2 iHead wHeads oHead
      else
        -- Scratch exhausted: 3 extra advances
        simAdvanceRight .strideExtra2 iHead wHeads oHead
    | .stride2 => simAdvanceRight .stride3 iHead wHeads oHead
    | .stride3 =>
      -- Advance sim right (3rd of 3), advance scratch right, loop
      (.stride1,
       fun i => if i.val = 2 then readBackWrite (wHeads 2)
                else if i.val = 3 then readBackWrite (wHeads 3)
                else readBackWrite (wHeads i),
       readBackWrite oHead, idleDir iHead,
       fun i => if i.val = 2 then Dir3.right
                else if i.val = 3 then Dir3.right
                else idleDir (wHeads i),
       idleDir oHead)
    | .strideExtra1 => simAdvanceRight .strideExtra2 iHead wHeads oHead
    | .strideExtra2 => simAdvanceRight .strideExtra3 iHead wHeads oHead
    | .strideExtra3 => simAdvanceRight .checkInput iHead wHeads oHead
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    -- States using simWriteRight or simAdvanceRight (sim right, rest idle)
    | .pos0Write2 | .pos0Extra1 | .pos0Extra2 | .pos0Extra3
    | .pos0Extra4 | .pos0Extra5 | .pos0Extra6
    | .writeSymHi
    | .stride2 | .strideExtra1 | .strideExtra2 | .strideExtra3 =>
      dsimp only [simWriteRight, simAdvanceRight]
      refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
      intro i hwi; split
      · rfl
      · exact idleDir_right_of_start hwi
    -- checkInput (two branches)
    | .checkInput =>
      dsimp only [setupIdle, simAdvanceRight, simWriteRight]; split
      · exact ros_setupIdle iHead wHeads oHead
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rfl
        · exact idleDir_right_of_start hwi
    -- stride1 (two branches, both advance sim)
    | .stride1 =>
      dsimp only [simAdvanceRight, simWriteRight]; split
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rfl
        · exact idleDir_right_of_start hwi
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rfl
        · exact idleDir_right_of_start hwi
    -- pos0Write1 (split on scratch)
    | .pos0Write1 =>
      dsimp only [setupIdle, simWriteRight]; split
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rfl
        · exact idleDir_right_of_start hwi
      · exact ros_setupIdle iHead wHeads oHead
    -- pos0Write3 (advance sim + scratch)
    | .pos0Write3 =>
      refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
      intro i hwi; simp only []; split
      · rfl
      · split
        · rfl
        · exact idleDir_right_of_start hwi
    -- stride3 (advance sim + scratch)
    | .stride3 =>
      refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
      intro i hwi; simp only []; split
      · rfl
      · split
        · rfl
        · exact idleDir_right_of_start hwi
    -- writeSymLo (advance sim + input)
    | .writeSymLo =>
      refine ⟨fun _ => rfl, ?_, idleDir_right_of_start⟩
      intro i hwi; simp only []; split
      · rfl
      · exact idleDir_right_of_start hwi
    -- advanceInput (advance input, rest idle)
    | .advanceInput =>
      exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩
    -- rewindScratch (scratch left or right depending on ▷)
    | .rewindScratch =>
      dsimp only []; split
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rfl
        · exact idleDir_right_of_start hwi
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · next hn heq =>
          have : i = (3 : Fin 4) := by ext; exact heq
          subst this; contradiction
        · exact idleDir_right_of_start hwi
    -- bounceScratch (setupIdle)
    | .bounceScratch =>
      dsimp only [setupIdle]
      exact ros_setupIdle iHead wHeads oHead
    -- done (allIdle — never reached since state = qhalt)
    | .done => exact ros_allIdle iHead wHeads oHead

end TM
