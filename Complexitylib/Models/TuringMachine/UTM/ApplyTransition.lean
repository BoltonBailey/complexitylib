import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.UTM.Defs
import Complexitylib.Models.TuringMachine.UTM.Helpers
import Complexitylib.Models.TuringMachine.UTM.SimConfig.Defs
import Complexitylib.Models.TuringMachine.Hoare.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

/-!
# UTM Apply Transition

Applies the decoded transition to the simulated state and tapes:
1. Read the transition output from the scratch tape
2. Update the state tape (write new one-hot encoding)
3. Update the simulation tape (write new symbols, move head markers)

## Architecture

The machine operates in several phases:

1. **Clear old state**: Scan state tape right, clearing all k cells to zero.
2. **Write new state**: Read new state one-hot from scratch, write to state tape.
3. **Update sim tape**: For each simulated tape (n+2 total), read the write
   symbol and direction from scratch, find the tape's head marker on the sim
   tape, write the new symbol, and move the head marker in the specified direction.
4. **Clear scratch**: Reset scratch tape cells to blank.
5. **Rewind all**: Return all work tape heads to cell 1.

## Main results

- `applyTransitionTM` — the machine definition (parametric in `k`)
- `applyTransitionTM_hoareTime` — HoareTime spec: advances SimInvariant by one step
-/

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- State type
-- ════════════════════════════════════════════════════════════════════════

/-- States for the apply transition machine. -/
inductive ApplyTransQ (n k : ℕ) where
  /-- Clear old state tape: write zeros to cells 1..k. -/
  | clearState (rem : Fin (k + 1))
  /-- Write new state: read one-hot from scratch, write to state tape. -/
  | writeState (rem : Fin (k + 1))
  /-- Rewind state and scratch tapes after state update. -/
  | rewindAfterState
  /-- For simulated tape `tapeIdx`, read write-symbol and direction from scratch.
      `scratchPos` tracks position in the output. -/
  | readTransData (tapeIdx : Fin (n + 2)) (scratchPos : Fin (TMEncoding.outputWidth k n + 1))
  /-- Scan sim tape right to find head marker for `tapeIdx`. -/
  | findHead (tapeIdx : Fin (n + 2)) (writeHi writeLo : Γ) (dir : Dir3)
  /-- Found head marker. Write new symbol and move marker. -/
  | applyWrite (tapeIdx : Fin (n + 2)) (writeHi writeLo : Γ) (dir : Dir3)
  /-- Rewind sim tape after update. -/
  | rewindSim
  /-- Sim tape at ▷, move right. -/
  | rewindSimR
  /-- Clear scratch tape. -/
  | clearScratch
  /-- Rewind all work tapes. -/
  | rewindAll
  /-- Rewind phase: left on a specific tape. -/
  | rewindTape (tapeIdx : Fin 4)
  /-- Tape hit ▷, move right. -/
  | rewindTapeR (tapeIdx : Fin 4)
  /-- Done. -/
  | done
  deriving DecidableEq

private instance : Fintype (ApplyTransQ n k) where
  elems :=
    {.rewindAfterState, .rewindSim, .rewindSimR, .clearScratch, .rewindAll, .done} ∪
    (Finset.univ.image fun (r : Fin (k + 1)) =>
      ApplyTransQ.clearState r) ∪
    (Finset.univ.image fun (r : Fin (k + 1)) =>
      ApplyTransQ.writeState r) ∪
    (Finset.univ.image fun (p : Fin (n + 2) × Fin (TMEncoding.outputWidth k n + 1)) =>
      ApplyTransQ.readTransData p.1 p.2) ∪
    (Finset.univ.image fun (p : Fin (n + 2) × Γ × Γ × Dir3) =>
      ApplyTransQ.findHead p.1 p.2.1 p.2.2.1 p.2.2.2) ∪
    (Finset.univ.image fun (p : Fin (n + 2) × Γ × Γ × Dir3) =>
      ApplyTransQ.applyWrite p.1 p.2.1 p.2.2.1 p.2.2.2) ∪
    (Finset.univ.image fun (t : Fin 4) => ApplyTransQ.rewindTape t) ∪
    (Finset.univ.image fun (t : Fin 4) => ApplyTransQ.rewindTapeR t)
  complete x := by
    cases x with
    | clearState r =>
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      left; left; left; left; left; left; right; exact ⟨r, rfl⟩
    | writeState r =>
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      left; left; left; left; left; right; exact ⟨r, rfl⟩
    | readTransData t s =>
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]
      left; left; left; left; right; exact ⟨t, s, rfl⟩
    | findHead t whi wlo d =>
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]
      left; left; left; right; exact ⟨t, whi, wlo, d, rfl⟩
    | applyWrite t whi wlo d =>
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]
      left; left; right; exact ⟨t, whi, wlo, d, rfl⟩
    | rewindTape t =>
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      left; right; exact ⟨t, rfl⟩
    | rewindTapeR t =>
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      right; exact ⟨t, rfl⟩
    | rewindAfterState => simp [Finset.mem_union, Finset.mem_insert]
    | rewindSim => simp [Finset.mem_union, Finset.mem_insert]
    | rewindSimR => simp [Finset.mem_union, Finset.mem_insert]
    | clearScratch => simp [Finset.mem_union, Finset.mem_insert]
    | rewindAll => simp [Finset.mem_union, Finset.mem_insert]
    | done => simp [Finset.mem_union, Finset.mem_insert]

-- ════════════════════════════════════════════════════════════════════════
-- Machine definition
-- ════════════════════════════════════════════════════════════════════════

/-- Apply the decoded transition to the UTM's work tapes.
    Reads transition output from scratch. Updates state tape (new one-hot)
    and sim tape (new symbols + moved head markers).

    Parametric in `k` (number of states of the simulated TM). -/
noncomputable def applyTransitionTM (k : ℕ) : TM 4 where
  Q := ApplyTransQ n k
  qstart := .clearState ⟨k, by omega⟩
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .clearState rem =>
      if rem.val = 0 then
        -- Done clearing. Rewind state tape, start reading new state from scratch.
        allIdle (.writeState ⟨k, by omega⟩) iHead wHeads oHead
      else
        -- Write zero to current state tape cell, advance right.
        (.clearState ⟨rem.val - 1, by omega⟩,
         fun i => if i = utmStateTape then .zero else .blank,
         .blank, idleDir iHead,
         fun i => if i = utmStateTape then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
    | .writeState rem =>
      if rem.val = 0 then
        -- Done writing new state. Proceed to read transition data.
        allIdle (.rewindAfterState) iHead wHeads oHead
      else
        -- Copy scratch bit to state tape, advance both right.
        let w : Γw := match wHeads utmScratchTape with
          | .zero => .zero | .one => .one | .blank => .blank | .start => .blank
        (.writeState ⟨rem.val - 1, by omega⟩,
         fun i => if i = utmStateTape then w
                  else if i = utmScratchTape then readBackWrite (wHeads utmScratchTape)
                  else .blank,
         .blank, idleDir iHead,
         fun i => if i = utmStateTape then Dir3.right
                  else if i = utmScratchTape then Dir3.right
                  else idleDir (wHeads i),
         idleDir oHead)
    | .rewindAfterState =>
      -- Rewind both state and scratch tapes to cell 1 (simplified: just idle)
      allIdle (.readTransData ⟨0, by omega⟩ ⟨0, by omega⟩) iHead wHeads oHead
    -- The remaining states handle per-tape updates on the sim tape.
    -- This is complex and involves scanning the sim tape for each tape's
    -- head marker, writing the new symbol, and moving the marker.
    -- For now, these transition to done.
    | .readTransData _ _ => allIdle .done iHead wHeads oHead
    | .findHead _ _ _ _ => allIdle .done iHead wHeads oHead
    | .applyWrite _ _ _ _ => allIdle .done iHead wHeads oHead
    | .rewindSim => allIdle .done iHead wHeads oHead
    | .rewindSimR => allIdle .done iHead wHeads oHead
    | .clearScratch => allIdle .done iHead wHeads oHead
    | .rewindAll => allIdle .done iHead wHeads oHead
    | .rewindTape _ => allIdle .done iHead wHeads oHead
    | .rewindTapeR _ => allIdle .done iHead wHeads oHead
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    have hros := fun (h : iHead = Γ.start) => idleDir_right_of_start h
    have hrosO := fun (h : oHead = Γ.start) => idleDir_right_of_start h
    match state with
    | .clearState rem =>
      dsimp only []; split
      · exact ⟨hros, fun _ hi => idleDir_right_of_start hi, hrosO⟩
      · refine ⟨hros, ?_, hrosO⟩
        intro i hi; dsimp only []; split <;> [rfl; exact idleDir_right_of_start hi]
    | .writeState rem =>
      dsimp only []; split
      · exact ⟨hros, fun _ hi => idleDir_right_of_start hi, hrosO⟩
      · refine ⟨hros, ?_, hrosO⟩
        intro i hi; dsimp only []; split <;> [rfl; split <;> [rfl; exact idleDir_right_of_start hi]]
    | .rewindAfterState
    | .readTransData _ _
    | .findHead _ _ _ _
    | .applyWrite _ _ _ _
    | .rewindSim | .rewindSimR | .clearScratch | .rewindAll
    | .rewindTape _ | .rewindTapeR _
    | .done =>
      exact ⟨hros, fun _ hi => idleDir_right_of_start hi, hrosO⟩

-- ════════════════════════════════════════════════════════════════════════
-- HoareTime specification
-- ════════════════════════════════════════════════════════════════════════

/-- HoareTime specification for `applyTransitionTM`. -/
theorem applyTransitionTM_hoareTime (tm : TM n) (k : ℕ)
    (hk : k = @Fintype.card tm.Q tm.finQ) (desc : List Bool)
    (simCfg : Cfg n tm.Q) (hNotHalted : simCfg.state ≠ tm.qhalt) :
    let e := tm.stateEquivK hk
    let iHead := simCfg.input.read
    let wHeads := fun i => (simCfg.work i).read
    let oHead := simCfg.output.read
    let (q', wW, oW, iD, wD, oD) := tm.δ simCfg.state iHead wHeads oHead
    ∃ B, (applyTransitionTM (n := n) k).HoareTime
      (fun _inp work _out =>
        stateOnTapeAt k (e simCfg.state) (work utmStateTape) ∧
        superCellsCorrect simCfg (work utmSimTape) ∧
        scratchHasTransOutput k n (e q') wW oW iD wD oD (work utmScratchTape) ∧
        descOnTape desc (work utmDescTape) ∧
        WorkTapesWF work)
      (fun _inp work _out =>
        let simCfg' : Cfg n tm.Q :=
          ⟨q', simCfg.input.move iD,
           fun i => (simCfg.work i).writeAndMove (wW i).toΓ (wD i),
           simCfg.output.writeAndMove oW.toΓ oD⟩
        stateOnTapeAt k (e q') (work utmStateTape) ∧
        superCellsCorrect simCfg' (work utmSimTape) ∧
        descOnTape desc (work utmDescTape) ∧
        (work utmDescTape).head = 1 ∧
        (work utmStateTape).head = 1 ∧
        (work utmSimTape).head = 1 ∧
        WorkTapesWF work)
      B := by
  sorry

end TM
