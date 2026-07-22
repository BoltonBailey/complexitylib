/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputCursor
import Complexitylib.Models.TuringMachine.Subroutines.BinaryPred.Defs

/-!
# Random-access probes for append-only transducer output -- definitions

`TM.outputProbeTM` simulates a source transducer without materializing its
output. One additional work tape holds a canonical positive binary cell
position. Every right move of the simulated output head runs the verified
binary predecessor controller on that tape. Once the counter is zero, leaving
the selected logical cell captures its final written bit; halting on that cell
captures the cursor's current bit.

The machine-level correctness and resource theorems live in the internal and
surface modules. This file contains only the finite controller and transition
construction.
-/

namespace Complexity

namespace TM

/-- Finite control of the output-position probe. -/
inductive OutputProbeQ (State : Type) where
  /-- Simulate one source transition with a finite output cursor. -/
  | source (state : State) (cursor : OutputCursor)
  /-- Run binary predecessor while the source configuration is frozen. -/
  | pred (state : State) (cursor : OutputCursor)
      (phase : BinaryPredPhase)
  /-- Emit a captured Boolean result on the physical output tape. -/
  | capture (bit : Bool)
  /-- The requested position did not contain a Boolean symbol. -/
  | missing
  /-- Unique normalized halt state. -/
  | done
  deriving DecidableEq

/-- The probe controller is finite whenever the source controller is finite. -/
instance [Fintype State] [DecidableEq State] : Fintype (OutputProbeQ State) where
  elems :=
    (Finset.univ.image fun pair : State × OutputCursor =>
      OutputProbeQ.source pair.1 pair.2) ∪
    (Finset.univ.image fun data : State × OutputCursor × BinaryPredPhase =>
      OutputProbeQ.pred data.1 data.2.1 data.2.2) ∪
    {.capture false, .capture true, .missing, .done}
  complete := by
    intro state
    cases state <;> simp

/-- The final work tape is the probe's canonical binary countdown. -/
def outputProbeCounterIdx (n : ℕ) : Fin (n + 1) :=
  Fin.last n

/-- Canonical rewound binary countdown supplied to the probe. -/
def outputProbeCounterTape (value : ℕ) : Tape :=
  (Tape.init (value.bits.map Γ.ofBool)).move Dir3.right

/-- Read the source machine's work heads from the prefix of the probe layout. -/
def outputProbeSourceHeads {n : ℕ} (workHeads : Fin (n + 1) → Γ) :
    Fin n → Γ :=
  fun i => workHeads (Fin.castAdd 1 i)

/-- Apply source work writes to the prefix and preserve the countdown tape. -/
def outputProbeSourceWrites {n : ℕ} (sourceWrites : Fin n → Γw)
    (workHeads : Fin (n + 1) → Γ) : Fin (n + 1) → Γw :=
  fun i =>
    if h : i.val < n then sourceWrites ⟨i.val, h⟩
    else readBackWrite (workHeads i)

/-- Apply source work directions to the prefix and park the countdown tape. -/
def outputProbeSourceDirs {n : ℕ} (sourceDirs : Fin n → Dir3)
    (workHeads : Fin (n + 1) → Γ) : Fin (n + 1) → Dir3 :=
  fun i =>
    if h : i.val < n then sourceDirs ⟨i.val, h⟩
    else idleDir (workHeads i)

/-- A source-simulation action with suppressed physical output. -/
def outputProbeSourceAction {n : ℕ} {State : Type}
    (nextState : OutputProbeQ State) (sourceWrites : Fin n → Γw)
    (inputDir : Dir3) (sourceDirs : Fin n → Dir3)
    (workHeads : Fin (n + 1) → Γ) (outputHead : Γ) :
    OutputProbeQ State × (Fin (n + 1) → Γw) × Γw × Dir3 ×
      (Fin (n + 1) → Dir3) × Dir3 :=
  (nextState, outputProbeSourceWrites sourceWrites workHeads,
    readBackWrite outputHead, inputDir,
    outputProbeSourceDirs sourceDirs workHeads, idleDir outputHead)

/-- Choose the result state for a symbol finalized by a right move. -/
def outputProbeCaptureWrite {State : Type} : Γw → OutputProbeQ State
  | .zero => .capture false
  | .one => .capture true
  | .blank => .missing

/-- Choose the result state for the symbol under a halted source cursor. -/
def outputProbeCaptureCursor {State : Type} : OutputCursor → OutputProbeQ State
  | .cell .zero => .capture false
  | .cell .one => .capture true
  | .start | .cell .blank | .cell .start => .missing

/-- Select the probe phase after one nonhalting source transition. -/
def outputProbeAfterSourceTransition {State : Type} (nextState : State)
    (cursor nextCursor : OutputCursor) (outputWrite : Γw)
    (outputDir : Dir3) (counterHead : Γ) : OutputProbeQ State :=
  if outputDir = Dir3.right then
    match cursor with
    | .start => .pred nextState nextCursor .borrow
    | .cell _ =>
        if counterHead = Γ.blank then outputProbeCaptureWrite outputWrite
        else .pred nextState nextCursor .borrow
  else .source nextState nextCursor

/-- Wrap the next predecessor phase, returning to source simulation as soon as
the canonical countdown has been rewound to cell one. -/
def outputProbeAfterPred {State : Type} (sourceState : State)
    (cursor : OutputCursor) (phase : BinaryPredPhase) : OutputProbeQ State :=
  if phase = .done then .source sourceState cursor
  else .pred sourceState cursor phase

private theorem outputProbeSourceAction_right_of_start
    {n : ℕ}
    {sourceOutputSafe : Prop}
    {inputDir : Dir3}
    {sourceDirs : Fin n → Dir3} {inputHead outputHead : Γ}
    {workHeads : Fin (n + 1) → Γ}
    (hsource :
      (inputHead = Γ.start → inputDir = Dir3.right) ∧
      (∀ i, outputProbeSourceHeads workHeads i = Γ.start →
        sourceDirs i = Dir3.right) ∧ sourceOutputSafe) :
    (inputHead = Γ.start → inputDir = Dir3.right) ∧
      (∀ i, workHeads i = Γ.start →
        outputProbeSourceDirs sourceDirs workHeads i = Dir3.right) ∧
      (outputHead = Γ.start →
        idleDir outputHead = Dir3.right) := by
  refine ⟨hsource.1, fun i hi => ?_, idleDir_right_of_start⟩
  unfold outputProbeSourceDirs
  split
  · next hlt =>
    apply hsource.2.1 ⟨i.val, hlt⟩
    simpa [outputProbeSourceHeads] using hi
  · exact idleDir_right_of_start hi

/-- Simulate a source transducer while probing one output cell.

The first `n` work tapes are the source tapes. Work tape `n` is a canonical
binary countdown initialized by the caller. The physical output tape is not
used by the source simulation; it receives exactly the captured result bit.
Correctness is specified for positive requested cell positions and canonical
countdown tapes. -/
def outputProbeTM (tm : TM n) : TM (n + 1) :=
  haveI : Fintype tm.Q := tm.finQ
  haveI : DecidableEq tm.Q := tm.decEq
  haveI : Fintype (OutputProbeQ tm.Q) := inferInstance
  haveI : DecidableEq (OutputProbeQ tm.Q) := inferInstance
  { Q := OutputProbeQ tm.Q
    qstart := .source tm.qstart .start
    qhalt := .done
    δ := fun phase inputHead workHeads outputHead =>
      match phase with
      | .source sourceState cursor =>
          if sourceState = tm.qhalt then
            if workHeads (outputProbeCounterIdx n) = Γ.blank then
              allReadBack (outputProbeCaptureCursor cursor)
                inputHead workHeads outputHead
            else
              allReadBack OutputProbeQ.missing inputHead workHeads outputHead
          else
            let (nextState, sourceWrites, outputWrite, inputDir,
              sourceDirs, outputDir) :=
                tm.δ sourceState inputHead
                  (outputProbeSourceHeads workHeads) cursor.read
            let nextCursor := cursor.next outputWrite outputDir
            let nextPhase := outputProbeAfterSourceTransition nextState
              cursor nextCursor outputWrite outputDir
              (workHeads (outputProbeCounterIdx n))
            outputProbeSourceAction nextPhase sourceWrites inputDir
              sourceDirs workHeads outputHead
      | .pred sourceState cursor predPhase =>
          let transition :=
            (binaryPredTM (outputProbeCounterIdx n)).δ predPhase inputHead
              workHeads outputHead
          (outputProbeAfterPred sourceState cursor transition.1,
            transition.2.1, transition.2.2.1, transition.2.2.2.1,
            transition.2.2.2.2.1, transition.2.2.2.2.2)
      | .capture bit =>
          if outputHead = Γ.start then
            allReadBack (.capture bit) inputHead workHeads outputHead
          else
            (.done, fun i => readBackWrite (workHeads i),
              if bit then .one else .zero, idleDir inputHead,
              fun i => idleDir (workHeads i), .right)
      | .missing =>
          allReadBack .done inputHead workHeads outputHead
      | .done =>
          allIdle .done inputHead workHeads outputHead
    δ_right_of_start := by
      intro phase inputHead workHeads outputHead
      match phase with
      | .source sourceState cursor =>
          dsimp only
          split
          · split
            · exact rightOfStart_allReadBack inputHead workHeads outputHead
            · exact rightOfStart_allReadBack inputHead workHeads outputHead
          · generalize htransition :
                tm.δ sourceState inputHead
                  (outputProbeSourceHeads workHeads) cursor.read = transition
            obtain ⟨nextState, sourceWrites, outputWrite, inputDir,
              sourceDirs, outputDir⟩ := transition
            have hsource := tm.δ_right_of_start sourceState inputHead
              (outputProbeSourceHeads workHeads) cursor.read
            rw [htransition] at hsource
            simp only [htransition]
            change
              (inputHead = Γ.start → inputDir = Dir3.right) ∧
                (∀ i, workHeads i = Γ.start →
                  outputProbeSourceDirs sourceDirs workHeads i =
                    Dir3.right) ∧
                (outputHead = Γ.start →
                  idleDir outputHead = Dir3.right)
            exact outputProbeSourceAction_right_of_start hsource
      | .pred sourceState cursor predPhase =>
          dsimp only
          generalize htransition :
            (binaryPredTM (outputProbeCounterIdx n)).δ predPhase inputHead
              workHeads outputHead = transition
          obtain ⟨nextPhase, workWrites, outputWrite, inputDir,
            workDirs, outputDir⟩ := transition
          have hpred :=
            (binaryPredTM (outputProbeCounterIdx n)).δ_right_of_start
              predPhase inputHead workHeads outputHead
          rw [htransition] at hpred
          exact hpred
      | .capture bit =>
          dsimp only
          split
          · exact rightOfStart_allReadBack inputHead workHeads outputHead
          · next houtput =>
            exact ⟨idleDir_right_of_start, fun i hi =>
              idleDir_right_of_start hi, fun _ => rfl⟩
      | .missing =>
          exact rightOfStart_allReadBack inputHead workHeads outputHead
      | .done =>
          exact rightOfStart_allIdle inputHead workHeads outputHead }

/-- Embed a source cursor configuration, a physical binary countdown, and an
independent real output tape into the source-simulation phase of the probe. -/
def outputProbeCfg (tm : TM n) (cfg : CursorCfg n tm.Q)
    (counter output : Tape) : Cfg (n + 1) (outputProbeTM tm).Q where
  state := .source cfg.state cfg.output
  input := cfg.input
  work := fun i =>
    if h : i.val < n then cfg.work ⟨i.val, h⟩ else counter
  output := output

/-- Configuration immediately after one simulated source step, before any
requested predecessor phase has run. -/
def outputProbeSourceResultCfg (tm : TM n)
    (before after : CursorCfg n tm.Q) (counter output : Tape) :
    Cfg (n + 1) (outputProbeTM tm).Q where
  state := outputProbeAfterSourceTransition after.state before.output
    after.output (tm.cursorOutputWrite before)
    (tm.cursorOutputDirection before) counter.read
  input := after.input
  work := fun i =>
    if h : i.val < n then after.work ⟨i.val, h⟩ else counter
  output := output

/-- View a predecessor-machine configuration inside the probe controller. The
predecessor's halt phase is collapsed directly back to source simulation. -/
def outputProbePredCfg (tm : TM n) (sourceState : tm.Q)
    (cursor : OutputCursor)
    (cfg : Cfg (n + 1) (binaryPredTM (outputProbeCounterIdx n)).Q) :
    Cfg (n + 1) (outputProbeTM tm).Q where
  state := outputProbeAfterPred sourceState cursor cfg.state
  input := cfg.input
  work := cfg.work
  output := cfg.output

/-- Configuration that is ready to emit a successfully captured bit. -/
def outputProbeCaptureCfg (tm : TM n) (bit : Bool)
    (input : Tape) (work : Fin (n + 1) → Tape) (output : Tape) :
    Cfg (n + 1) (outputProbeTM tm).Q where
  state := .capture bit
  input := input
  work := work
  output := output

/-- Halted configuration after emitting a captured bit from an off-marker
physical output head. -/
def outputProbeDoneCfg (tm : TM n) (bit : Bool)
    (input : Tape) (work : Fin (n + 1) → Tape) (output : Tape) :
    Cfg (n + 1) (outputProbeTM tm).Q where
  state := .done
  input := input.move (idleDir input.read)
  work := fun i =>
    (work i).writeAndMove (readBackWrite (work i).read)
      (idleDir (work i).read)
  output := output.writeAndMove (if bit then Γw.one else Γw.zero)
    Dir3.right

end TM

end Complexity
