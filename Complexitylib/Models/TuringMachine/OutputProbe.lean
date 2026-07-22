/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbe.Defs
import Complexitylib.Models.TuringMachine.OutputProbe.Internal

/-!
# Random-access probes for append-only transducer output

`TM.outputProbeTM` adds one canonical binary countdown tape to a source
transducer. The source output is represented only by `TM.OutputCursor`. A
right output move decrements the countdown with the verified binary
predecessor machine; once it reaches zero, leaving the selected ordinary cell
captures the finalized bit. A source halt on that cell captures the cursor's
current bit. The physical output tape receives only the one-bit answer.

This is the executable recomputation kernel needed for log-space composition:
the potentially polynomial source output is never copied to work tape, while
the requested position occupies only its binary width.

## Main results

- `TM.outputProbeTM_isTransducer` -- the probe retains append-only output.
- `TM.outputProbeTM_step_source` -- exact simulation of one source step.
- `TM.outputProbeTM_reachesIn_source_not_right` -- a non-right source step
  preserves the countdown.
- `TM.outputProbeTM_reachesIn_source_positive` -- a right source step followed
  by verified binary predecessor decrements a positive countdown.
- `TM.outputProbeTM_source_positive_prefix_withinAuxSpace` -- every prefix of
  that countdown invocation uses only the represented binary width.
- `TM.outputProbeTM_reachesIn_cursorTraceObserved` -- an entire observed
  source run consumes exactly its counted output advances.
- `TM.outputProbeTM_reachesIn_cursorTraceObserved_withinAuxSpace` -- the
  entire replay has an all-prefix source-space-plus-binary-width bound.
- `TM.outputProbeTM_step_halt_capture` -- zero countdown at a halted Boolean
  cursor selects that bit for physical output.
- `TM.outputProbeTM_reachesIn_cursorTraceObserved_capture` -- end-to-end
  replay and one-bit output when the selected frontier cell is final.
- `TM.outputProbeTM_reachesIn_cursorTraceObserved_finalize_capture` -- the
  corresponding end-to-end theorem for a cell finalized before source halt.
- `TM.outputProbeSourceResultCfg_capture` -- a right move with a zero
  countdown selects the finalized bit for capture.
- `TM.outputProbeTM_capture_hasOutput` -- capture reaches the unique halt state
  with exactly the selected one-bit output.
-/

namespace Complexity

namespace TM

/-- The output-position probe never moves its physical output head left. -/
theorem outputProbeTM_isTransducer (tm : TM n) :
    (outputProbeTM tm).IsTransducer :=
  outputProbeTM_isTransducer_internal tm

/-- One probe source-phase step implements one finite-cursor source step. The
source input/work actions are exact, the countdown is preserved during this
transition, and the independent physical output performs its idle action. -/
theorem outputProbeTM_step_source (tm : TM n)
    {cfg cfg' : CursorCfg n tm.Q} (counter output : Tape)
    (hcounter : counter.read ≠ Γ.start)
    (hcursor : tm.cursorStep cfg = some cfg') :
    (outputProbeTM tm).step (outputProbeCfg tm cfg counter output) =
      some (outputProbeSourceResultCfg tm cfg cfg' counter
        (suppressOutputTapeStep output)) :=
  outputProbeTM_step_source_internal tm counter output hcounter hcursor

/-- A source step whose logical output head does not move right takes one
probe transition and preserves the binary countdown exactly. -/
theorem outputProbeTM_reachesIn_source_not_right (tm : TM n)
    {before after : CursorCfg n tm.Q} (counter output : Tape)
    (hcursor : tm.cursorStep before = some after)
    (hdir : tm.cursorOutputDirection before ≠ Dir3.right)
    (hcounter : counter.read ≠ Γ.start) :
    (outputProbeTM tm).reachesIn 1
      (outputProbeCfg tm before counter output)
      (outputProbeCfg tm after counter
        (suppressOutputTapeStep output)) :=
  outputProbeTM_reachesIn_source_not_right_internal tm counter output
    hcursor hdir hcounter

/-- A right-moving source step followed by marker normalization, the verified
binary predecessor, and exact marker restoration changes a canonical positive
countdown `value + 1` to canonical `value`. The source configuration after its
one step is retained exactly, even when its input or work heads rest on `▷`. -/
theorem outputProbeTM_reachesIn_source_positive (tm : TM n)
    {before after : CursorCfg n tm.Q} {value : ℕ}
    (counter output : Tape)
    (hcursor : tm.cursorStep before = some after)
    (hdir : tm.cursorOutputDirection before = Dir3.right)
    (hcounter : counter.HasBinaryNat (value + 1))
    (hinput : after.input.StartInvariant)
    (hwork : ∀ i, (after.work i).StartInvariant)
    (houtput : (suppressOutputTapeStep output).read ≠ Γ.start) :
    (outputProbeTM tm).reachesIn (binaryPredTime value + 3)
      (outputProbeCfg tm before counter output)
      (outputProbeCfg tm after (outputProbeCounterTape value)
        (suppressOutputTapeStep output)) :=
  outputProbeTM_reachesIn_source_positive_internal tm counter output
    hcursor hdir hcounter hinput hwork houtput

/-- Every prefix of one positive-countdown source invocation stays inside the
initial auxiliary-space budget plus the represented counter's binary width
and a constant seam allowance. -/
theorem outputProbeTM_source_positive_prefix_withinAuxSpace
    (tm : TM n) {value inputLength initialSpace elapsed : ℕ}
    {before : CursorCfg n tm.Q} (counter output : Tape)
    {cfg : Cfg (n + 1) (outputProbeTM tm).Q}
    (hinitial :
      (outputProbeCfg tm before counter output).WithinAuxSpace
        inputLength initialSpace)
    (hprefix : elapsed ≤ binaryPredTime value + 3)
    (hreach : (outputProbeTM tm).reachesIn elapsed
      (outputProbeCfg tm before counter output) cfg) :
    cfg.WithinAuxSpace inputLength
      (outputProbePositiveSpace initialSpace value) :=
  outputProbeTM_source_positive_prefix_withinAuxSpace_internal tm
    counter output hinitial hprefix hreach

/-- When the countdown is canonical zero, leaving an ordinary source-output
cell to the right selects the just-written Boolean symbol for capture. -/
theorem outputProbeSourceResultCfg_capture (tm : TM n)
    (before after : CursorCfg n tm.Q) (counter output : Tape)
    (bit : Bool) (symbol : Γ)
    (hcursor : before.output = .cell symbol)
    (hdir : tm.cursorOutputDirection before = Dir3.right)
    (hwrite : tm.cursorOutputWrite before =
      if bit then Γw.one else Γw.zero)
    (hcounter : counter.HasBinaryNat 0) :
    outputProbeSourceResultCfg tm before after counter output =
      outputProbeCaptureCfg tm bit after.input
        (fun i =>
          if h : i.val < n then after.work ⟨i.val, h⟩ else counter)
        output :=
  outputProbeSourceResultCfg_capture_internal tm before after counter output
    bit symbol hcursor hdir hwrite hcounter

/-- An entire finite-cursor source run can be replayed by the concrete probe
without materializing its output. If the initial counter is `remaining` plus
the run's observed frontier advances, the final counter is canonical
`remaining`; the source input/work configuration is retained exactly. -/
theorem outputProbeTM_reachesIn_cursorTraceObserved (tm : TM n)
    {steps advances remaining : ℕ}
    {before after : CursorCfg n tm.Q} (counter output : Tape)
    (htrace : tm.cursorTraceObserved steps before = some (after, advances))
    (hinput : before.input.StartInvariant)
    (hwork : ∀ i, (before.work i).StartInvariant)
    (hcounter : counter.HasBinaryNat (remaining + advances))
    (houtput : output.StartInvariant) :
    ∃ probeSteps,
      (outputProbeTM tm).reachesIn probeSteps
        (outputProbeCfg tm before counter output)
        (outputProbeCfg tm after (outputProbeCounterTape remaining)
          (suppressOutputTapeTrace steps output)) :=
  outputProbeTM_reachesIn_cursorTraceObserved_internal tm counter output
    htrace hinput hwork hcounter houtput

/-- Replay an observed source run with an all-prefix auxiliary-space bound.
`Inv` may be any source invariant preserved by cursor steps whose input and
work heads stay inside `sourceSpace`. The probe adds only the binary width of
the initial countdown, independently of the number of predecessor calls. -/
theorem outputProbeTM_reachesIn_cursorTraceObserved_withinAuxSpace
    (tm : TM n) (Inv : CursorCfg n tm.Q → Prop)
    {steps advances remaining inputLength sourceSpace : ℕ}
    {before after : CursorCfg n tm.Q} (counter output : Tape)
    (htrace : tm.cursorTraceObserved steps before = some (after, advances))
    (hinv : Inv before)
    (hinvStep : ∀ {cfg next}, Inv cfg →
      tm.cursorStep cfg = some next → Inv next)
    (hinvSpace : ∀ cfg, Inv cfg →
      (∀ i, (cfg.work i).head ≤ sourceSpace) ∧
      cfg.input.head ≤ inputLength + sourceSpace + 1)
    (hsourceSpace : 1 ≤ sourceSpace)
    (hinput : before.input.StartInvariant)
    (hwork : ∀ i, (before.work i).StartInvariant)
    (hcounter : counter.HasBinaryNat (remaining + advances))
    (houtput : output.StartInvariant) :
    ∃ probeSteps,
      (outputProbeTM tm).reachesIn probeSteps
        (outputProbeCfg tm before counter output)
        (outputProbeCfg tm after (outputProbeCounterTape remaining)
          (suppressOutputTapeTrace steps output)) ∧
      ∀ elapsed cfg, elapsed ≤ probeSteps →
        (outputProbeTM tm).reachesIn elapsed
          (outputProbeCfg tm before counter output) cfg →
        cfg.WithinAuxSpace inputLength
          (outputProbeReplaySpace sourceSpace (remaining + advances)) :=
  outputProbeTM_reachesIn_cursorTraceObserved_withinAuxSpace_internal tm
    Inv counter output htrace hinv hinvStep hinvSpace hsourceSpace hinput
    hwork hcounter houtput le_rfl

/-- At a halted source state, a canonical zero countdown and Boolean cursor
select that cursor bit for capture. The normalization action is explicit so
the theorem applies even when source heads are parked on `▷`. -/
theorem outputProbeTM_step_halt_capture (tm : TM n)
    (cfg : CursorCfg n tm.Q) (counter output : Tape) (bit : Bool)
    (hhalt : cfg.state = tm.qhalt)
    (hcursor : cfg.output = .cell (Γ.ofBool bit))
    (hcounter : counter.HasBinaryNat 0) :
    (outputProbeTM tm).step (outputProbeCfg tm cfg counter output) =
      some (outputProbeCaptureCfg tm bit
        (outputProbeNormalizeInput cfg.input)
        (outputProbeNormalizeWork fun i =>
          if h : i.val < n then cfg.work ⟨i.val, h⟩ else counter)
        (outputProbeNormalizeTape output)) :=
  outputProbeTM_step_halt_capture_internal tm cfg counter output bit
    hhalt hcursor hcounter

/-- From a blank physical output parked at cell one, the capture phase takes
one transition to the unique probe halt state and exposes exactly `[bit]` as
its output string. -/
theorem outputProbeTM_capture_hasOutput (tm : TM n) (bit : Bool)
    (input : Tape) (work : Fin (n + 1) → Tape) (output : Tape)
    (hhead : output.head = 1)
    (hcells : output.cells = (Tape.init []).cells) :
    (outputProbeTM tm).reachesIn 1
      (outputProbeCaptureCfg tm bit input work output)
      (outputProbeDoneCfg tm bit input work output) ∧
    (outputProbeTM tm).halted
      (outputProbeDoneCfg tm bit input work output) ∧
    (outputProbeDoneCfg tm bit input work output).output.HasOutput [bit] :=
  outputProbeTM_capture_hasOutput_internal tm bit input work output
    hhead hcells

/-- Replay an entire observed source run and emit its selected final frontier
bit. The initial countdown equals the run's exact number of output advances;
the source must halt with the Boolean bit under its cursor. The two physical
output hypotheses state that suppressed execution left the blank output parked
at cell one, as it does for every positive-length run from `Tape.init []`. -/
theorem outputProbeTM_reachesIn_cursorTraceObserved_capture (tm : TM n)
    {steps advances : ℕ}
    {before after : CursorCfg n tm.Q} (counter output : Tape) (bit : Bool)
    (htrace : tm.cursorTraceObserved steps before = some (after, advances))
    (hinput : before.input.StartInvariant)
    (hwork : ∀ i, (before.work i).StartInvariant)
    (hcounter : counter.HasBinaryNat advances)
    (houtput : output.StartInvariant)
    (hhalt : after.state = tm.qhalt)
    (hcursor : after.output = .cell (Γ.ofBool bit))
    (hphysicalHead : (suppressOutputTapeTrace steps output).head = 1)
    (hphysicalCells : (suppressOutputTapeTrace steps output).cells =
      (Tape.init []).cells) :
    ∃ probeSteps done,
      (outputProbeTM tm).reachesIn probeSteps
        (outputProbeCfg tm before counter output) done ∧
      (outputProbeTM tm).halted done ∧ done.output.HasOutput [bit] :=
  outputProbeTM_reachesIn_cursorTraceObserved_capture_internal tm counter
    output bit htrace hinput hwork hcounter houtput hhalt hcursor
    hphysicalHead hphysicalCells

/-- Replay an observed source prefix and emit the bit finalized by its next
right output move. This is the earlier-cell counterpart of
`outputProbeTM_reachesIn_cursorTraceObserved_capture`: together the two
theorems cover capture either when a cell is left or when the source halts on
the selected frontier cell. -/
theorem outputProbeTM_reachesIn_cursorTraceObserved_finalize_capture
    (tm : TM n) {steps advances : ℕ}
    {before selected next : CursorCfg n tm.Q}
    (counter output : Tape) (bit : Bool) (symbol : Γ)
    (htrace : tm.cursorTraceObserved steps before =
      some (selected, advances))
    (hinput : before.input.StartInvariant)
    (hwork : ∀ i, (before.work i).StartInvariant)
    (hcounter : counter.HasBinaryNat advances)
    (houtput : output.StartInvariant)
    (hnext : tm.cursorStep selected = some next)
    (hcursor : selected.output = .cell symbol)
    (hdir : tm.cursorOutputDirection selected = Dir3.right)
    (hwrite : tm.cursorOutputWrite selected =
      if bit then Γw.one else Γw.zero)
    (hphysicalHead : (suppressOutputTapeTrace steps output).head = 1)
    (hphysicalCells : (suppressOutputTapeTrace steps output).cells =
      (Tape.init []).cells) :
    ∃ probeSteps done,
      (outputProbeTM tm).reachesIn probeSteps
        (outputProbeCfg tm before counter output) done ∧
      (outputProbeTM tm).halted done ∧ done.output.HasOutput [bit] :=
  outputProbeTM_reachesIn_cursorTraceObserved_finalize_capture_internal tm
    counter output bit symbol htrace hinput hwork hcounter houtput hnext
    hcursor hdir hwrite hphysicalHead hphysicalCells

end TM

end Complexity
