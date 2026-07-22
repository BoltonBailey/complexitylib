/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputCursor.Defs
import Complexitylib.Models.TuringMachine.OutputCursor.Internal

/-!
# Finite cursors for append-only output tapes

`TM.OutputCursor` replaces an append-only output prefix by the finite data that
can affect the next transition: whether the head is still on the left marker
and the current symbol. The blank-frontier invariant proves that a right move
always enters a fresh blank cell. This is the finite-control basis for
log-space output probing and recomputation without materializing a polynomial
output string on work tape.

## Main results

- `TM.OutputCursor.read_outputCursor` -- the cursor supplies the real symbol.
- `Tape.outputCursor_writeAndMove` -- exact cursor update for a non-left move.
- `TM.IsTransducer.cursorStep_commute` -- cursor stepping commutes with a
  concrete transducer step.
- `TM.IsTransducer.cursorStepObserved_commute` -- the same step exposes its
  zero-or-one output-frontier advance.
- `TM.IsTransducer.cursorTrace_commute` -- the quotient simulates a complete
  exact-step run.
- `TM.IsTransducer.cursorTraceObserved_initCfg` -- from an initial
  configuration, accumulated advances equal the final output-head position.
- `TM.IsTransducer.cursorTrace_initCfg` -- initial runs need no manual frontier
  hypotheses.
- `TM.suppressOutputTM_isTransducer` -- the concrete realization remains an
  append-only transducer.
- `TM.suppressOutputTM_step` -- one concrete step implements one cursor step.
- `TM.IsTransducer.suppressOutputTM_reachesIn` -- complete source runs lift to
  the concrete output-suppressing machine.
- `TM.IsTransducer.suppressOutputTM_reachesIn_halt` -- source halting runs lift
  through the final normalization seam.
- `TM.IsTransducer.suppressOutputTM_computesNil` -- suppressing a function
  transducer gives a genuine machine computing the empty string.
-/

namespace Complexity

namespace TM.OutputCursor

/-- A cursor built from a well-formed tape supplies exactly the symbol read by
that tape. -/
theorem read_outputCursor {tape : Tape} (hstart : tape.StartInvariant) :
    tape.outputCursor.read = tape.read :=
  read_outputCursor_internal hstart

@[simp] theorem next_start_right (write : Γw) :
    OutputCursor.next .start write .right = .cell Γ.blank :=
  next_start_right_internal write

@[simp] theorem next_cell_right (symbol : Γ) (write : Γw) :
    OutputCursor.next (.cell symbol) write .right = .cell Γ.blank :=
  next_cell_right_internal symbol write

@[simp] theorem next_cell_stay (symbol : Γ) (write : Γw) :
    OutputCursor.next (.cell symbol) write .stay = .cell write.toΓ :=
  next_cell_stay_internal symbol write

end TM.OutputCursor

namespace Tape

/-- A write followed by a non-left move updates the finite output cursor
exactly. The proof uses `BlankAfterHead` in the right-moving case to show that
the newly visited cell is blank. -/
theorem outputCursor_writeAndMove {tape : Tape}
    (hblank : tape.BlankAfterHead) (write : Γw) (direction : Dir3)
    (hnoleft : direction ≠ Dir3.left) :
    (tape.writeAndMove write.toΓ direction).outputCursor =
      tape.outputCursor.next write direction :=
  outputCursor_writeAndMove_internal hblank write direction hnoleft

end Tape

namespace TM

/-- Quotienting the output tape to a finite cursor commutes with every concrete
step of a transducer whose output has the standard start-marker and blank-tail
invariants. No already-written output cell appears in the cursor
configuration. -/
theorem IsTransducer.cursorStep_commute {tm : TM n}
    (htrans : tm.IsTransducer) {cfg cfg' : Cfg n tm.Q}
    (hstart : cfg.output.StartInvariant)
    (hblank : cfg.output.BlankAfterHead)
    (hstep : tm.step cfg = some cfg') :
    tm.cursorStep (.ofCfg cfg) = some (.ofCfg cfg') :=
  htrans.cursorStep_commute_internal hstart hblank hstep

/-- The observed cursor step commutes with a concrete transducer step. Its
numeric event is the selected output direction's zero-or-one frontier
contribution. -/
theorem IsTransducer.cursorStepObserved_commute {tm : TM n}
    (htrans : tm.IsTransducer) {cfg cfg' : Cfg n tm.Q}
    (hstart : cfg.output.StartInvariant)
    (hblank : cfg.output.BlankAfterHead)
    (hstep : tm.step cfg = some cfg') :
    tm.cursorStepObserved (.ofCfg cfg) =
      some (.ofCfg cfg', tm.cursorOutputEvent (.ofCfg cfg)) :=
  htrans.cursorStepObserved_commute_internal hstart hblank hstep

/-- Quotienting the output tape commutes with an entire exact-step transducer
run. The cursor trace retains the source state, input, and work tapes exactly
while replacing the potentially polynomial output prefix by one finite cursor.
-/
theorem IsTransducer.cursorTrace_commute {tm : TM n}
    (htrans : tm.IsTransducer) {steps : ℕ} {cfg cfg' : Cfg n tm.Q}
    (hreach : tm.reachesIn steps cfg cfg')
    (hstart : cfg.output.StartInvariant)
    (hblank : cfg.output.BlankAfterHead) :
    tm.cursorTrace steps (.ofCfg cfg) = some (.ofCfg cfg') :=
  htrans.cursorTrace_commute_internal hreach hstart hblank

/-- An observed exact cursor run counts precisely how far the physical output
head advanced. The statement is relative to the starting head, so it also
applies to subruns. -/
theorem IsTransducer.cursorTraceObserved_commute {tm : TM n}
    (htrans : tm.IsTransducer) {steps : ℕ} {cfg cfg' : Cfg n tm.Q}
    (hreach : tm.reachesIn steps cfg cfg')
    (hstart : cfg.output.StartInvariant)
    (hblank : cfg.output.BlankAfterHead) :
    ∃ advances,
      tm.cursorTraceObserved steps (.ofCfg cfg) =
        some (.ofCfg cfg', advances) ∧
      cfg'.output.head = cfg.output.head + advances :=
  htrans.cursorTraceObserved_commute_internal hreach hstart hblank

/-- From the canonical initial configuration, the observed cursor count is
exactly the final physical output-head position. This is the accounting fact
used by binary output-position probes. -/
theorem IsTransducer.cursorTraceObserved_initCfg {tm : TM n}
    (htrans : tm.IsTransducer) {input : List Bool} {steps : ℕ}
    {cfg : Cfg n tm.Q}
    (hreach : tm.reachesIn steps (tm.initCfg input) cfg) :
    tm.cursorTraceObserved steps (.ofCfg (tm.initCfg input)) =
      some (.ofCfg cfg, cfg.output.head) :=
  htrans.cursorTraceObserved_initCfg_internal hreach

/-- Specialized complete-run simulation from an ordinary initial
configuration. The start-marker and blank-frontier obligations are discharged
by the canonical blank output tape. -/
theorem IsTransducer.cursorTrace_initCfg {tm : TM n}
    (htrans : tm.IsTransducer) {input : List Bool} {steps : ℕ}
    {cfg : Cfg n tm.Q}
    (hreach : tm.reachesIn steps (tm.initCfg input) cfg) :
    tm.cursorTrace steps (.ofCfg (tm.initCfg input)) =
      some (.ofCfg cfg) :=
  htrans.cursorTrace_initCfg_internal hreach

/-- The concrete output-suppressing realization never moves its real output
head left. -/
theorem suppressOutputTM_isTransducer (tm : TM n) :
    (suppressOutputTM tm).IsTransducer :=
  suppressOutputTM_isTransducer_internal tm

/-- One step of the concrete output-suppressing machine implements one pure
cursor step exactly, including the source input/work actions. -/
theorem suppressOutputTM_step (tm : TM n)
    {cfg cfg' : CursorCfg n tm.Q} (realOutput : Tape)
    (hcursor : tm.cursorStep cfg = some cfg') :
    (suppressOutputTM tm).step (suppressOutputCfg tm cfg realOutput) =
      some (suppressOutputCfg tm cfg'
        (suppressOutputTapeStep realOutput)) :=
  suppressOutputTM_step_internal tm realOutput hcursor

/-- A complete source-transducer run lifts to the concrete output-suppressing
machine with exactly the same number of simulated steps. The final input and
work tapes are the source final tapes; only the real output follows the idle
blank-tape evolution. -/
theorem IsTransducer.suppressOutputTM_reachesIn {tm : TM n}
    (htrans : tm.IsTransducer) {steps : ℕ} {cfg cfg' : Cfg n tm.Q}
    (hreach : tm.reachesIn steps cfg cfg')
    (hstart : cfg.output.StartInvariant)
    (hblank : cfg.output.BlankAfterHead) (realOutput : Tape) :
    (suppressOutputTM tm).reachesIn steps
      (suppressOutputCfg tm (.ofCfg cfg) realOutput)
      (suppressOutputCfg tm (.ofCfg cfg')
        (suppressOutputTapeTrace steps realOutput)) :=
  htrans.suppressOutputTM_reachesIn_internal hreach hstart hblank realOutput

/-- A halted source-transducer run lifts through the one-step normalization
seam to the genuine halt state of `suppressOutputTM`. -/
theorem IsTransducer.suppressOutputTM_reachesIn_halt {tm : TM n}
    (htrans : tm.IsTransducer) {steps : ℕ} {cfg cfg' : Cfg n tm.Q}
    (hreach : tm.reachesIn steps cfg cfg')
    (hstart : cfg.output.StartInvariant)
    (hblank : cfg.output.BlankAfterHead) (hhalt : tm.halted cfg')
    (realOutput : Tape) :
    (suppressOutputTM tm).reachesIn (steps + 1)
      (suppressOutputCfg tm (.ofCfg cfg) realOutput)
      (suppressOutputDoneCfg tm (.ofCfg cfg')
        (suppressOutputTapeTrace steps realOutput)) :=
  htrans.suppressOutputTM_reachesIn_halt_internal hreach hstart hblank
    hhalt realOutput

/-- Idling the real blank output while simulating any fixed number of source
steps still represents the empty output string. -/
theorem suppressOutputTapeTrace_init_hasOutput_nil (steps : ℕ) :
    (suppressOutputTapeTrace steps (Tape.init [])).HasOutput [] :=
  suppressOutputTapeTrace_init_hasOutput_nil_internal steps

/-- Suppressing the output of a bounded-time function transducer yields a
genuine machine computation of the empty string. The simulator retains the
source input and work-tape behavior, replaces the growing output prefix by a
finite cursor in control state, and spends one final step entering its own
halt state. -/
theorem IsTransducer.suppressOutputTM_computesNil {tm : TM n}
    {f : List Bool → List Bool} {T : ℕ → ℕ}
    (htrans : tm.IsTransducer) (hcomp : tm.ComputesInTime f T) :
    (suppressOutputTM tm).ComputesInTime (fun _ => [])
      (fun inputLength => T inputLength + 1) :=
  htrans.suppressOutputTM_computesNil_internal hcomp

end TM

end Complexity
