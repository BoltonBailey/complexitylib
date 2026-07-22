/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbe.Defs
import Complexitylib.Models.TuringMachine.Combinators.WorkBranch
import Complexitylib.Models.TuringMachine.Subroutines.BinaryPred

/-!
# Random-access probes for append-only transducer output -- proof internals
-/

namespace Complexity

namespace TM

private theorem hasBinaryNat_positive_read_ne_blank_internal
    {tape : Tape} {value : ℕ} (hvalue : tape.HasBinaryNat value)
    (hpositive : 0 < value) : tape.read ≠ Γ.blank := by
  intro hblank
  have := hvalue.read_eq_blank_iff.mp hblank
  omega

theorem outputProbeCfg_sourceHeads_internal (tm : TM n)
    (cfg : CursorCfg n tm.Q) (counter output : Tape) :
    outputProbeSourceHeads
      (fun i => ((outputProbeCfg tm cfg counter output).work i).read) =
      fun i => (cfg.work i).read := by
  funext i
  simp [outputProbeSourceHeads, outputProbeCfg]

@[simp] theorem outputProbeCfg_counter_internal (tm : TM n)
    (cfg : CursorCfg n tm.Q) (counter output : Tape) :
    (outputProbeCfg tm cfg counter output).work
      (outputProbeCounterIdx n) = counter := by
  simp [outputProbeCfg, outputProbeCounterIdx]

theorem outputProbeTM_isTransducer_internal (tm : TM n) :
    (outputProbeTM tm).IsTransducer := by
  intro phase inputHead workHeads outputHead
  cases phase with
  | source sourceState cursor =>
      simp only [outputProbeTM]
      split
      · split <;> cases outputHead <;> simp [allReadBack, idleDir]
      · generalize htransition :
          tm.δ sourceState inputHead
            (outputProbeSourceHeads workHeads) cursor.read = transition
        obtain ⟨nextState, sourceWrites, outputWrite, inputDir,
          sourceDirs, outputDir⟩ := transition
        cases outputHead <;>
          simp [htransition, outputProbeSourceAction, idleDir]
  | pred sourceState cursor predPhase =>
      simp only [outputProbeTM]
      generalize htransition :
        (binaryPredTM (outputProbeCounterIdx n)).δ predPhase inputHead
          workHeads outputHead = transition
      obtain ⟨nextPhase, workWrites, outputWrite, inputDir,
        workDirs, outputDir⟩ := transition
      have htrans := binaryPredTM_isTransducer
        (outputProbeCounterIdx n) predPhase inputHead workHeads outputHead
      rw [htransition] at htrans
      exact htrans
  | capture bit =>
      simp only [outputProbeTM]
      split
      · cases outputHead <;> simp [allReadBack, idleDir]
      · cases bit <;> simp
  | missing =>
      cases outputHead <;> simp [outputProbeTM, allReadBack, idleDir]
  | done =>
      cases outputHead <;> simp [outputProbeTM, allIdle, idleDir]

theorem outputProbeTM_step_source_internal (tm : TM n)
    {cfg cfg' : CursorCfg n tm.Q} (counter output : Tape)
    (hcounter : counter.read ≠ Γ.start)
    (hcursor : tm.cursorStep cfg = some cfg') :
    (outputProbeTM tm).step (outputProbeCfg tm cfg counter output) =
      some (outputProbeSourceResultCfg tm cfg cfg' counter
        (suppressOutputTapeStep output)) := by
  by_cases hhalt : cfg.state = tm.qhalt
  · simp [cursorStep, hhalt] at hcursor
  · generalize htransition :
      tm.δ cfg.state cfg.input.read (fun i => (cfg.work i).read)
        cfg.output.read = transition
    obtain ⟨state, workWrites, outputWrite, inputDir, workDirs,
      outputDir⟩ := transition
    simp only [cursorStep, hhalt, if_false, htransition,
      Option.some.injEq] at hcursor
    subst cfg'
    have hheads :
        outputProbeSourceHeads
          (fun i =>
            ((if h : i.val < n then cfg.work ⟨i.val, h⟩
              else counter) : Tape).read) =
          fun i => (cfg.work i).read := by
      funext i
      simp [outputProbeSourceHeads]
    have hcounterIdle :
        counter.writeAndMove (readBackWrite counter.read)
          (idleDir counter.read) = counter := by
      rw [writeAndMove_readBack counter hcounter]
      simp [idleDir, hcounter, Tape.move]
    simp [TM.step, outputProbeTM, outputProbeCfg,
      outputProbeSourceResultCfg,
      outputProbeSourceWrites, outputProbeSourceDirs,
      outputProbeSourceAction, cursorOutputWrite, cursorOutputDirection,
      suppressOutputTapeStep, outputProbeCounterIdx, hhalt, hheads,
      htransition]
    funext i
    split
    · rfl
    · exact hcounterIdle

theorem outputProbeTM_step_pred_internal (tm : TM n)
    (sourceState : tm.Q) (cursor : OutputCursor)
    {cfg cfg' : Cfg (n + 1)
      (binaryPredTM (outputProbeCounterIdx n)).Q}
    (hstep : (binaryPredTM (outputProbeCounterIdx n)).step cfg =
      some cfg') :
    (outputProbeTM tm).step
      (outputProbePredCfg tm sourceState cursor cfg) =
      some (outputProbePredCfg tm sourceState cursor cfg') := by
  have hstate : cfg.state ≠ BinaryPredPhase.done := by
    exact state_ne_qhalt_of_step hstep
  have hhalt :
      cfg.state ≠ (binaryPredTM (outputProbeCounterIdx n)).qhalt :=
    hstate
  generalize htransition :
    (binaryPredTM (outputProbeCounterIdx n)).δ cfg.state cfg.input.read
      (fun i => (cfg.work i).read) cfg.output.read = transition
  obtain ⟨nextPhase, workWrites, outputWrite, inputDir, workDirs,
    outputDir⟩ := transition
  rw [TM.step, if_neg hhalt, htransition] at hstep
  simp only [Option.some.injEq] at hstep
  subst cfg'
  have hcurrent : outputProbeAfterPred sourceState cursor cfg.state =
      .pred sourceState cursor cfg.state := by
    unfold outputProbeAfterPred
    exact if_neg hstate
  have hprobeNotHalt :
      (OutputProbeQ.pred sourceState cursor cfg.state : OutputProbeQ tm.Q) ≠
        .done := by
    simp
  have hwrappedNotHalt :
      outputProbeAfterPred sourceState cursor cfg.state ≠
        (outputProbeTM tm).qhalt := by
    rw [hcurrent]
    exact hprobeNotHalt
  rw [TM.step]
  simp only [outputProbePredCfg, hcurrent]
  split
  · next heq => exact (hwrappedNotHalt heq).elim
  · simp only [outputProbeTM, htransition]

theorem outputProbeTM_reachesIn_pred_internal (tm : TM n)
    (sourceState : tm.Q) (cursor : OutputCursor)
    {steps : ℕ}
    {cfg cfg' : Cfg (n + 1)
      (binaryPredTM (outputProbeCounterIdx n)).Q}
    (hreach : (binaryPredTM (outputProbeCounterIdx n)).reachesIn
      steps cfg cfg') :
    (outputProbeTM tm).reachesIn steps
      (outputProbePredCfg tm sourceState cursor cfg)
      (outputProbePredCfg tm sourceState cursor cfg') := by
  induction hreach with
  | zero => exact .zero
  | step hstep _ ih =>
      exact .step
        (outputProbeTM_step_pred_internal tm sourceState cursor hstep) ih

theorem outputProbeSourceResultCfg_positive_internal (tm : TM n)
    (before after : CursorCfg n tm.Q) (counter output : Tape)
    (hdir : tm.cursorOutputDirection before = Dir3.right)
    {value : ℕ} (hcounter : counter.HasBinaryNat (value + 1)) :
    outputProbeSourceResultCfg tm before after counter output =
      outputProbePredCfg tm after.state after.output
        { state := BinaryPredPhase.borrow
          input := after.input
          work := fun i =>
            if h : i.val < n then after.work ⟨i.val, h⟩ else counter
          output := output } := by
  apply Cfg.ext
  · cases houtput : before.output with
    | start =>
        simp [outputProbeSourceResultCfg, outputProbePredCfg,
          outputProbeAfterSourceTransition, outputProbeAfterPred, hdir,
          houtput]
    | cell symbol =>
        have hnotblank : counter.read ≠ Γ.blank :=
          hasBinaryNat_positive_read_ne_blank_internal hcounter (by omega)
        simp [outputProbeSourceResultCfg, outputProbePredCfg,
          outputProbeAfterSourceTransition, outputProbeAfterPred, hdir,
          houtput, hnotblank]
  · rfl
  · rfl
  · rfl

theorem outputProbeSourceResultCfg_not_right_internal (tm : TM n)
    (before after : CursorCfg n tm.Q) (counter output : Tape)
    (hdir : tm.cursorOutputDirection before ≠ Dir3.right) :
    outputProbeSourceResultCfg tm before after counter output =
      outputProbeCfg tm after counter output := by
  apply Cfg.ext
  · simp [outputProbeSourceResultCfg, outputProbeCfg,
      outputProbeAfterSourceTransition, hdir]
  · rfl
  · rfl
  · rfl

theorem outputProbeSourceResultCfg_capture_internal (tm : TM n)
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
        output := by
  have hblank : counter.read = Γ.blank :=
    hcounter.read_eq_blank_iff.mpr rfl
  apply Cfg.ext
  · cases bit <;>
      simp [outputProbeSourceResultCfg, outputProbeCaptureCfg,
        outputProbeAfterSourceTransition, outputProbeCaptureWrite,
        hcursor, hdir, hwrite, hblank]
  · rfl
  · rfl
  · rfl

theorem outputProbeTM_reachesIn_source_not_right_internal (tm : TM n)
    {before after : CursorCfg n tm.Q} (counter output : Tape)
    (hcursor : tm.cursorStep before = some after)
    (hdir : tm.cursorOutputDirection before ≠ Dir3.right)
    (hcounter : counter.read ≠ Γ.start) :
    (outputProbeTM tm).reachesIn 1
      (outputProbeCfg tm before counter output)
      (outputProbeCfg tm after counter
        (suppressOutputTapeStep output)) := by
  have hstep := outputProbeTM_step_source_internal tm counter output
    hcounter hcursor
  rw [outputProbeSourceResultCfg_not_right_internal tm before after
    counter (suppressOutputTapeStep output) hdir] at hstep
  exact .step hstep .zero

theorem outputProbeTM_reachesIn_source_positive_internal (tm : TM n)
    {before after : CursorCfg n tm.Q} {value : ℕ}
    (counter output : Tape)
    (hcursor : tm.cursorStep before = some after)
    (hdir : tm.cursorOutputDirection before = Dir3.right)
    (hcounter : counter.HasBinaryNat (value + 1))
    (hinput : after.input.read ≠ Γ.start)
    (hwork : ∀ i, (after.work i).read ≠ Γ.start)
    (houtput : (suppressOutputTapeStep output).read ≠ Γ.start) :
    (outputProbeTM tm).reachesIn (binaryPredTime value + 1)
      (outputProbeCfg tm before counter output)
      (outputProbeCfg tm after (outputProbeCounterTape value)
        (suppressOutputTapeStep output)) := by
  let nextOutput := suppressOutputTapeStep output
  let predStart : Cfg (n + 1)
      (binaryPredTM (outputProbeCounterIdx n)).Q :=
    { state := BinaryPredPhase.borrow
      input := after.input
      work := fun i =>
        if h : i.val < n then after.work ⟨i.val, h⟩ else counter
      output := nextOutput }
  have hcounterAt :
      (predStart.work (outputProbeCounterIdx n)).HasBinaryNat
        (value + 1) := by
    simpa [predStart, outputProbeCounterIdx] using hcounter
  have hother : ∀ i, i ≠ outputProbeCounterIdx n →
      (predStart.work i).read ≠ Γ.start := by
    intro i hi
    have hlt : i.val < n := by
      apply Fin.val_lt_last
      simpa [outputProbeCounterIdx] using hi
    simpa [predStart, hlt] using hwork ⟨i.val, hlt⟩
  obtain ⟨predFinal, hpredRun, hpredHalt, hpredInput,
    hpredOther, hpredCounter, hpredOutput⟩ :=
      binaryPredTM_reachesIn_frame (outputProbeCounterIdx n) value
        predStart.input predStart.work predStart.output hcounterAt
        (by simpa [predStart] using hinput) hother
        (by simpa [predStart, nextOutput] using houtput)
  have hfirst := outputProbeTM_step_source_internal tm counter output
    (by
      rw [Tape.read, hcounter.2.1]
      exact Tape.cells_ne_start_of_hasBinaryString hcounter.2 1 le_rfl)
    hcursor
  have hsourceResult :
      outputProbeSourceResultCfg tm before after counter nextOutput =
        outputProbePredCfg tm after.state after.output predStart := by
    simpa [predStart, nextOutput] using
      outputProbeSourceResultCfg_positive_internal tm before after
        counter nextOutput hdir hcounter
  have hwrappedRun := outputProbeTM_reachesIn_pred_internal tm
    after.state after.output hpredRun
  have hfinal :
      outputProbePredCfg tm after.state after.output predFinal =
        outputProbeCfg tm after (outputProbeCounterTape value)
          nextOutput := by
    apply Cfg.ext
    · have hstate : predFinal.state = BinaryPredPhase.done := hpredHalt
      simp [outputProbePredCfg, outputProbeCfg, outputProbeAfterPred,
        hstate]
    · simpa [outputProbePredCfg, outputProbeCfg] using hpredInput
    · funext i
      by_cases hi : i = outputProbeCounterIdx n
      · subst i
        have hcounterEq :=
          Tape.eq_init_move_right_of_hasBinaryString hpredCounter.2
            hpredCounter.1
        simpa [outputProbePredCfg, outputProbeCfg, outputProbeCounterTape,
          outputProbeCounterIdx] using hcounterEq
      · have hlt : i.val < n := by
          apply Fin.val_lt_last
          simpa [outputProbeCounterIdx] using hi
        have hsame := hpredOther i hi
        simp only [outputProbePredCfg, outputProbeCfg, dif_pos hlt]
        calc
          predFinal.work i = predStart.work i := hsame
          _ = after.work ⟨i.val, hlt⟩ := by simp [predStart, hlt]
    · simpa [outputProbePredCfg, outputProbeCfg] using hpredOutput
  rw [hsourceResult] at hfirst
  rw [hfinal] at hwrappedRun
  exact .step hfirst hwrappedRun

theorem outputProbeTM_step_capture_internal (tm : TM n) (bit : Bool)
    (input : Tape) (work : Fin (n + 1) → Tape) (output : Tape)
    (houtput : output.read ≠ Γ.start) :
    (outputProbeTM tm).step
      (outputProbeCaptureCfg tm bit input work output) =
      some (outputProbeDoneCfg tm bit input work output) := by
  cases bit <;>
    simp [TM.step, outputProbeTM, outputProbeCaptureCfg,
      outputProbeDoneCfg, houtput]

theorem outputProbeTM_capture_hasOutput_internal (tm : TM n) (bit : Bool)
    (input : Tape) (work : Fin (n + 1) → Tape) (output : Tape)
    (hhead : output.head = 1)
    (hcells : output.cells = (Tape.init []).cells) :
    (outputProbeTM tm).reachesIn 1
      (outputProbeCaptureCfg tm bit input work output)
      (outputProbeDoneCfg tm bit input work output) ∧
    (outputProbeTM tm).halted
      (outputProbeDoneCfg tm bit input work output) ∧
    (outputProbeDoneCfg tm bit input work output).output.HasOutput [bit] := by
  have hread : output.read = Γ.blank := by
    rw [Tape.read, hhead, hcells]
    rfl
  refine ⟨TM.reachesIn.step
    (outputProbeTM_step_capture_internal tm bit input work output
      (by rw [hread]; decide)) .zero, rfl, ?_⟩
  cases bit <;>
    simp [outputProbeDoneCfg, Tape.HasOutput, Tape.writeAndMove,
      Tape.write, Tape.move, hhead, hcells, Tape.init,
      Function.update_apply, Γ.ofBool]

end TM

end Complexity
