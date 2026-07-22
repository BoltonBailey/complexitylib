/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbe.Defs
import Complexitylib.Models.TuringMachine.Combinators.WorkBranch
import Complexitylib.Models.TuringMachine.Subroutines.BinaryPred
import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc

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
  | prepare sourceState cursor =>
      cases outputHead <;> simp [outputProbeTM, allReadBack, idleDir]
  | pred sourceState cursor mask predPhase =>
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
  | restore sourceState cursor mask =>
      cases outputHead <;>
        simp [outputProbeTM, outputProbeRestoreDir, idleDir]
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
    (mask : OutputProbeStartMask n)
    {cfg cfg' : Cfg (n + 1)
      (binaryPredTM (outputProbeCounterIdx n)).Q}
    (hstep : (binaryPredTM (outputProbeCounterIdx n)).step cfg =
      some cfg') :
    (outputProbeTM tm).step
      (outputProbePredCfg tm sourceState cursor mask cfg) =
      some (outputProbePredCfg tm sourceState cursor mask cfg') := by
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
  have hcurrent : outputProbeAfterPred sourceState cursor mask cfg.state =
      .pred sourceState cursor mask cfg.state := by
    unfold outputProbeAfterPred
    exact if_neg hstate
  have hprobeNotHalt :
      (OutputProbeQ.pred sourceState cursor mask cfg.state :
        OutputProbeQ n tm.Q) ≠
        .done := by
    simp
  have hwrappedNotHalt :
      outputProbeAfterPred sourceState cursor mask cfg.state ≠
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
    (mask : OutputProbeStartMask n)
    {steps : ℕ}
    {cfg cfg' : Cfg (n + 1)
      (binaryPredTM (outputProbeCounterIdx n)).Q}
    (hreach : (binaryPredTM (outputProbeCounterIdx n)).reachesIn
      steps cfg cfg') :
    (outputProbeTM tm).reachesIn steps
      (outputProbePredCfg tm sourceState cursor mask cfg)
      (outputProbePredCfg tm sourceState cursor mask cfg') := by
  induction hreach with
  | zero => exact .zero
  | step hstep _ ih =>
      exact .step
        (outputProbeTM_step_pred_internal tm sourceState cursor mask hstep) ih

private theorem startInvariant_read_eq_start_iff_internal (tape : Tape)
    (hinv : tape.StartInvariant) :
    tape.read = Γ.start ↔ tape.head = 0 := by
  constructor
  · intro hread
    by_contra hhead
    exact hinv.2 tape.head (by omega) (by simpa [Tape.read] using hread)
  · intro hhead
    simp [Tape.read, hhead, hinv.1]

private theorem outputProbeNormalizeTape_eq_self_internal {tape : Tape}
    (hread : tape.read ≠ Γ.start) :
    outputProbeNormalizeTape tape = tape := by
  rw [outputProbeNormalizeTape, writeAndMove_readBack tape hread]
  simp [idleDir, hread, Tape.move]

private theorem outputProbeNormalizeInput_eq_self_internal {input : Tape}
    (hread : input.read ≠ Γ.start) :
    outputProbeNormalizeInput input = input := by
  simp [outputProbeNormalizeInput, idleDir, hread, Tape.move]

private theorem outputProbeNormalizeTape_read_ne_start_internal {tape : Tape}
    (hinv : tape.StartInvariant) :
    (outputProbeNormalizeTape tape).read ≠ Γ.start := by
  by_cases hread : tape.read = Γ.start
  · have hhead :=
      (startInvariant_read_eq_start_iff_internal tape hinv).mp hread
    have hnormalized : outputProbeNormalizeTape tape = tape.move .right := by
      unfold outputProbeNormalizeTape
      simp only [hread, readBackWrite, idleDir]
      change (tape.write Γ.blank).move Dir3.right = tape.move Dir3.right
      rw [show tape.write Γ.blank = tape by simp [Tape.write, hhead]]
    rw [hnormalized]
    exact (hinv.move .right).read_ne_start (by simp [Tape.move, hhead])
  · rw [outputProbeNormalizeTape_eq_self_internal hread]
    exact hread

private theorem outputProbeNormalizeInput_read_ne_start_internal {input : Tape}
    (hinv : input.StartInvariant) :
    (outputProbeNormalizeInput input).read ≠ Γ.start := by
  by_cases hread : input.read = Γ.start
  · have hhead :=
      (startInvariant_read_eq_start_iff_internal input hinv).mp hread
    rw [show outputProbeNormalizeInput input = input.move .right by
      simp [outputProbeNormalizeInput, idleDir, hread]]
    exact (hinv.move .right).read_ne_start (by simp [Tape.move, hhead])
  · rw [outputProbeNormalizeInput_eq_self_internal hread]
    exact hread

private theorem outputProbeRestoreInput_normalize_internal {input : Tape}
    (hinv : input.StartInvariant) :
    outputProbeRestoreInput (input.read == Γ.start)
      (outputProbeNormalizeInput input) = input := by
  by_cases hread : input.read = Γ.start
  · have hhead :=
      (startInvariant_read_eq_start_iff_internal input hinv).mp hread
    have hnormalized : outputProbeNormalizeInput input = input.move .right := by
      simp [outputProbeNormalizeInput, idleDir, hread]
    have hnormalizedRead : (input.move .right).read ≠ Γ.start :=
      (hinv.move .right).read_ne_start (by simp [Tape.move, hhead])
    simp only [hread, beq_self_eq_true, hnormalized,
      outputProbeRestoreInput]
    rw [show outputProbeRestoreDir true (input.move .right).read = .left by
      simp [outputProbeRestoreDir, hnormalizedRead]]
    apply Tape.ext
    · simp [Tape.move, hhead]
    · simp [Tape.move]
  · have hbeq : (input.read == Γ.start) = false := by
      exact beq_eq_false_iff_ne.mpr hread
    rw [hbeq, outputProbeNormalizeInput_eq_self_internal hread]
    simp [outputProbeRestoreInput, outputProbeRestoreDir, hread, Tape.move]

private theorem outputProbeRestoreTape_normalize_internal {tape : Tape}
    (hinv : tape.StartInvariant) :
    outputProbeRestoreTape (tape.read == Γ.start)
      (outputProbeNormalizeTape tape) = tape := by
  by_cases hread : tape.read = Γ.start
  · have hhead :=
      (startInvariant_read_eq_start_iff_internal tape hinv).mp hread
    have hnormalized : outputProbeNormalizeTape tape = tape.move .right := by
      unfold outputProbeNormalizeTape
      simp only [hread, readBackWrite, idleDir]
      change (tape.write Γ.blank).move Dir3.right = tape.move Dir3.right
      rw [show tape.write Γ.blank = tape by simp [Tape.write, hhead]]
    have hnormalizedRead : (tape.move .right).read ≠ Γ.start :=
      (hinv.move .right).read_ne_start (by simp [Tape.move, hhead])
    simp only [hread, beq_self_eq_true, hnormalized, outputProbeRestoreTape]
    rw [writeAndMove_readBack _ hnormalizedRead]
    rw [show outputProbeRestoreDir true (tape.move .right).read = .left by
      simp [outputProbeRestoreDir, hnormalizedRead]]
    apply Tape.ext
    · simp [Tape.move, hhead]
    · simp [Tape.move]
  · have hbeq : (tape.read == Γ.start) = false := by
      exact beq_eq_false_iff_ne.mpr hread
    rw [hbeq, outputProbeNormalizeTape_eq_self_internal hread,
      outputProbeRestoreTape, writeAndMove_readBack _ hread]
    simp [outputProbeRestoreDir, hread, Tape.move]

theorem outputProbeTM_step_prepare_internal (tm : TM n)
    (sourceState : tm.Q) (cursor : OutputCursor) (input : Tape)
    (work : Fin (n + 1) → Tape) (output : Tape) :
    (outputProbeTM tm).step
      (outputProbePrepareCfg tm sourceState cursor input work output) =
      some (outputProbePredCfg tm sourceState cursor
        (outputProbeCfgStartMask input work)
        (outputProbePredStartCfg input work output)) := by
  simp [TM.step, outputProbeTM, outputProbePrepareCfg,
    outputProbePredCfg, outputProbePredStartCfg,
    outputProbeCfgStartMask, outputProbeStartMask,
    outputProbeAfterPred, allReadBack, outputProbeNormalizeInput,
    outputProbeNormalizeTape]
  funext i
  rfl

theorem outputProbeTM_step_restore_internal (tm : TM n)
    (sourceState : tm.Q) (cursor : OutputCursor)
    (mask : OutputProbeStartMask n) (input : Tape)
    (work : Fin (n + 1) → Tape) (output : Tape) :
    (outputProbeTM tm).step
      (outputProbeRestoreCfg tm sourceState cursor mask input work output) =
      some
        { state := OutputProbeQ.source sourceState cursor
          input := outputProbeRestoreInput mask.input input
          work := outputProbeRestoreWork mask work
          output := outputProbeNormalizeTape output } := by
  simp only [TM.step, outputProbeTM, outputProbeRestoreCfg,
    outputProbeRestoreInput,
    outputProbeNormalizeTape, outputProbeRestoreWorkDirs]
  rw [if_neg (by simp)]
  congr 2
  funext i
  unfold outputProbeRestoreWork
  split <;> rfl

theorem outputProbeSourceResultCfg_positive_internal (tm : TM n)
    (before after : CursorCfg n tm.Q) (counter output : Tape)
    (hdir : tm.cursorOutputDirection before = Dir3.right)
    {value : ℕ} (hcounter : counter.HasBinaryNat (value + 1)) :
    outputProbeSourceResultCfg tm before after counter output =
      outputProbePrepareCfg tm after.state after.output after.input
        (fun i =>
          if h : i.val < n then after.work ⟨i.val, h⟩ else counter)
        output := by
  apply Cfg.ext
  · cases houtput : before.output with
    | start =>
        simp [outputProbeSourceResultCfg, outputProbePrepareCfg,
          outputProbeAfterSourceTransition, hdir,
          houtput]
    | cell symbol =>
        have hnotblank : counter.read ≠ Γ.blank :=
          hasBinaryNat_positive_read_ne_blank_internal hcounter (by omega)
        simp [outputProbeSourceResultCfg, outputProbePrepareCfg,
          outputProbeAfterSourceTransition, hdir,
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
    (hinput : after.input.StartInvariant)
    (hwork : ∀ i, (after.work i).StartInvariant)
    (houtput : (suppressOutputTapeStep output).read ≠ Γ.start) :
    (outputProbeTM tm).reachesIn (binaryPredTime value + 3)
      (outputProbeCfg tm before counter output)
      (outputProbeCfg tm after (outputProbeCounterTape value)
        (suppressOutputTapeStep output)) := by
  let nextOutput := suppressOutputTapeStep output
  let framedWork : Fin (n + 1) → Tape := fun i =>
    if h : i.val < n then after.work ⟨i.val, h⟩ else counter
  let mask := outputProbeCfgStartMask after.input framedWork
  let predStart := outputProbePredStartCfg after.input framedWork nextOutput
  have hcounterRead : counter.read ≠ Γ.start := by
    rw [Tape.read, hcounter.2.1]
    exact Tape.cells_ne_start_of_hasBinaryString hcounter.2 1 le_rfl
  have hcounterNormalized : outputProbeNormalizeTape counter = counter :=
    outputProbeNormalizeTape_eq_self_internal hcounterRead
  have hcounterAt :
      (predStart.work (outputProbeCounterIdx n)).HasBinaryNat
        (value + 1) := by
    simpa [predStart, outputProbePredStartCfg, outputProbeNormalizeWork,
      framedWork, outputProbeCounterIdx, hcounterNormalized] using hcounter
  have hother : ∀ i, i ≠ outputProbeCounterIdx n →
      (predStart.work i).read ≠ Γ.start := by
    intro i hi
    have hlt : i.val < n := by
      apply Fin.val_lt_last
      simpa [outputProbeCounterIdx] using hi
    simpa [predStart, outputProbePredStartCfg, outputProbeNormalizeWork,
      framedWork, hlt] using
      outputProbeNormalizeTape_read_ne_start_internal (hwork ⟨i.val, hlt⟩)
  obtain ⟨predFinal, hpredRun, hpredHalt, hpredInput,
    hpredOther, hpredCounter, hpredOutput⟩ :=
      binaryPredTM_reachesIn_frame (outputProbeCounterIdx n) value
        predStart.input predStart.work predStart.output hcounterAt
        (by
          simpa [predStart, outputProbePredStartCfg] using
            outputProbeNormalizeInput_read_ne_start_internal hinput)
        hother
        (by
          simpa [predStart, outputProbePredStartCfg, nextOutput,
            outputProbeNormalizeTape_eq_self_internal houtput] using houtput)
  have hfirst := outputProbeTM_step_source_internal tm counter output
    hcounterRead hcursor
  have hsourceResult :
      outputProbeSourceResultCfg tm before after counter nextOutput =
        outputProbePrepareCfg tm after.state after.output after.input
          framedWork nextOutput := by
    simpa [framedWork, nextOutput] using
      outputProbeSourceResultCfg_positive_internal tm before after
        counter nextOutput hdir hcounter
  have hprepare := outputProbeTM_step_prepare_internal tm after.state
    after.output after.input framedWork nextOutput
  have hprepareTarget :
      outputProbePredCfg tm after.state after.output mask predStart =
        outputProbePredCfg tm after.state after.output
          (outputProbeCfgStartMask after.input framedWork)
          (outputProbePredStartCfg after.input framedWork nextOutput) := by
    rfl
  rw [hprepareTarget] at hprepare
  have hwrappedRun := outputProbeTM_reachesIn_pred_internal tm
    after.state after.output mask hpredRun
  have hrestoreCfg :
      outputProbePredCfg tm after.state after.output mask predFinal =
        outputProbeRestoreCfg tm after.state after.output mask
          predFinal.input predFinal.work predFinal.output := by
    apply Cfg.ext
    · have hstate : predFinal.state = BinaryPredPhase.done := hpredHalt
      simp [outputProbePredCfg, outputProbeRestoreCfg, outputProbeAfterPred,
        hstate]
    · rfl
    · rfl
    · rfl
  have hrestore := outputProbeTM_step_restore_internal tm after.state
    after.output mask predFinal.input predFinal.work predFinal.output
  rw [← hrestoreCfg] at hrestore
  have hcounterEq :
      predFinal.work (outputProbeCounterIdx n) =
        outputProbeCounterTape value := by
    exact Tape.eq_init_move_right_of_hasBinaryString hpredCounter.2
      hpredCounter.1
  have hrestored :
      ({ state := OutputProbeQ.source after.state after.output
         input := outputProbeRestoreInput mask.input predFinal.input
         work := outputProbeRestoreWork mask predFinal.work
         output := outputProbeNormalizeTape predFinal.output } :
        Cfg (n + 1) (outputProbeTM tm).Q) =
      outputProbeCfg tm after (outputProbeCounterTape value) nextOutput := by
    apply Cfg.ext
    · rfl
    · rw [hpredInput]
      simpa [mask, predStart, outputProbePredStartCfg,
        outputProbeCfgStartMask, outputProbeStartMask] using
        outputProbeRestoreInput_normalize_internal hinput
    · change outputProbeRestoreWork mask predFinal.work =
        fun i =>
          if h : i.val < n then after.work ⟨i.val, h⟩
          else outputProbeCounterTape value
      funext i
      by_cases hi : i = outputProbeCounterIdx n
      · subst i
        have hcounterFinalRead :
            (outputProbeCounterTape value).read ≠ Γ.start := by
          rw [← hcounterEq]
          rw [Tape.read, hpredCounter.2.1]
          exact Tape.cells_ne_start_of_hasBinaryString hpredCounter.2 1 le_rfl
        have hlast : ¬ (outputProbeCounterIdx n).val < n := by
          simp [outputProbeCounterIdx]
        rw [show outputProbeRestoreWork mask predFinal.work
          (outputProbeCounterIdx n) = outputProbeNormalizeTape
            (predFinal.work (outputProbeCounterIdx n)) by
          simp [outputProbeRestoreWork, hlast], dif_neg hlast]
        rw [hcounterEq,
          outputProbeNormalizeTape_eq_self_internal hcounterFinalRead]
      · have hlt : i.val < n := by
          apply Fin.val_lt_last
          simpa [outputProbeCounterIdx] using hi
        have hsame := hpredOther i hi
        rw [dif_pos hlt]
        unfold outputProbeRestoreWork
        rw [dif_pos hlt]
        rw [hsame]
        have hmask : mask.work ⟨i.val, hlt⟩ =
            ((after.work ⟨i.val, hlt⟩).read == Γ.start) := by
          simp [mask, outputProbeCfgStartMask, outputProbeStartMask,
            outputProbeSourceHeads, framedWork]
        rw [hmask]
        simpa [predStart, outputProbePredStartCfg,
          outputProbeNormalizeWork, framedWork, hlt] using
          outputProbeRestoreTape_normalize_internal (hwork ⟨i.val, hlt⟩)
    · change outputProbeNormalizeTape predFinal.output = nextOutput
      rw [hpredOutput]
      change outputProbeNormalizeTape
        (outputProbeNormalizeTape nextOutput) = nextOutput
      rw [outputProbeNormalizeTape_eq_self_internal houtput,
        outputProbeNormalizeTape_eq_self_internal houtput]
  rw [hsourceResult] at hfirst
  rw [hrestored] at hrestore
  have hpredAndRestore :=
    (outputProbeTM tm).reachesIn_snoc hwrappedRun hrestore
  have hrun := TM.reachesIn.step hfirst
    (TM.reachesIn.step hprepare hpredAndRestore)
  have htime : binaryPredTime value + 1 + 1 + 1 =
      binaryPredTime value + 3 := by omega
  rw [← htime]
  simpa [nextOutput] using hrun

private theorem cursorStep_startInvariant_internal (tm : TM n)
    {before after : CursorCfg n tm.Q}
    (hstep : tm.cursorStep before = some after)
    (hinput : before.input.StartInvariant)
    (hwork : ∀ i, (before.work i).StartInvariant) :
    after.input.StartInvariant ∧
      ∀ i, (after.work i).StartInvariant := by
  by_cases hhalt : before.state = tm.qhalt
  · simp [cursorStep, hhalt] at hstep
  · generalize htransition :
      tm.δ before.state before.input.read
        (fun i => (before.work i).read) before.output.read = transition
    obtain ⟨state, workWrites, outputWrite, inputDir, workDirs,
      outputDir⟩ := transition
    simp only [cursorStep, hhalt, if_false, htransition,
      Option.some.injEq] at hstep
    subst after
    exact ⟨hinput.move inputDir,
      fun i => (hwork i).writeAndMove (workWrites i) (workDirs i)⟩

private theorem suppressOutputTapeStep_startInvariant_internal {output : Tape}
    (hinv : output.StartInvariant) :
    (suppressOutputTapeStep output).StartInvariant :=
  hinv.writeAndMove _ _

private theorem suppressOutputTapeStep_read_ne_start_internal {output : Tape}
    (hinv : output.StartInvariant) :
    (suppressOutputTapeStep output).read ≠ Γ.start := by
  simpa [suppressOutputTapeStep, outputProbeNormalizeTape] using
    outputProbeNormalizeTape_read_ne_start_internal hinv

private theorem outputProbeCounterTape_hasBinaryNat_internal (value : ℕ) :
    (outputProbeCounterTape value).HasBinaryNat value := by
  simpa [outputProbeCounterTape] using Tape.init_move_right_hasBinaryNat value

/-- Simulate an entire observed cursor run while retaining `remaining`
uncrossed output cells in the countdown. The starting counter represents the
sum of `remaining` and all right moves in the source run; the final counter is
canonical `remaining`. -/
theorem outputProbeTM_reachesIn_cursorTraceObserved_internal (tm : TM n)
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
          (suppressOutputTapeTrace steps output)) := by
  induction steps generalizing before counter output advances with
  | zero =>
      simp only [cursorTraceObserved, Option.some.injEq,
        Prod.mk.injEq] at htrace
      obtain ⟨rfl, rfl⟩ := htrace
      refine ⟨0, ?_⟩
      have hcounterEq := hcounter.eq_init_move_right
      simpa [outputProbeCounterTape, hcounterEq] using
        (TM.reachesIn.zero :
          (outputProbeTM tm).reachesIn 0
            (outputProbeCfg tm before counter output)
            (outputProbeCfg tm before counter output))
  | succ steps ih =>
      cases hfirst : tm.cursorStep before with
      | none =>
          simp [cursorTraceObserved, cursorStepObserved, hfirst] at htrace
      | some next =>
          cases hlater : tm.cursorTraceObserved steps next with
          | none =>
              simp [cursorTraceObserved, cursorStepObserved, hfirst,
                hlater] at htrace
          | some result =>
              obtain ⟨final, later⟩ := result
              simp [cursorTraceObserved, cursorStepObserved, hfirst,
                hlater] at htrace
              obtain ⟨hfinal, hadvances⟩ := htrace
              subst after
              subst advances
              obtain ⟨hnextInput, hnextWork⟩ :=
                cursorStep_startInvariant_internal tm hfirst hinput hwork
              have hnextOutputInv :=
                suppressOutputTapeStep_startInvariant_internal houtput
              have hnextOutputRead :=
                suppressOutputTapeStep_read_ne_start_internal houtput
              by_cases hdir :
                  tm.cursorOutputDirection before = Dir3.right
              · have hadvance :
                    (tm.cursorOutputEvent before).advance = 1 := by
                  cases hdirection : tm.cursorOutputDirection before <;>
                    simp_all [cursorOutputEvent, OutputCursor.advanceCount]
                have hcounterPositive : counter.HasBinaryNat
                    ((remaining + later) + 1) := by
                  convert hcounter using 1
                  simp [hadvance]
                  omega
                have hsource :=
                  outputProbeTM_reachesIn_source_positive_internal tm
                    counter output hfirst hdir hcounterPositive hnextInput
                    hnextWork hnextOutputRead
                obtain ⟨laterSteps, hlaterRun⟩ := ih
                  (outputProbeCounterTape (remaining + later))
                  (suppressOutputTapeStep output) hlater hnextInput hnextWork
                  (outputProbeCounterTape_hasBinaryNat_internal
                    (remaining + later)) hnextOutputInv
                refine ⟨(binaryPredTime (remaining + later) + 3) +
                  laterSteps, ?_⟩
                simpa [suppressOutputTapeTrace] using
                  (outputProbeTM tm).reachesIn_trans hsource hlaterRun
              · have hadvance :
                    (tm.cursorOutputEvent before).advance = 0 := by
                  cases hdirection : tm.cursorOutputDirection before <;>
                    simp_all [cursorOutputEvent, OutputCursor.advanceCount]
                have hcounterSame :
                    counter.HasBinaryNat (remaining + later) := by
                  simpa [hadvance] using hcounter
                have hcounterRead : counter.read ≠ Γ.start := by
                  rw [Tape.read, hcounterSame.2.1]
                  exact Tape.cells_ne_start_of_hasBinaryString
                    hcounterSame.2 1 le_rfl
                have hsource :=
                  outputProbeTM_reachesIn_source_not_right_internal tm
                    counter output hfirst hdir hcounterRead
                obtain ⟨laterSteps, hlaterRun⟩ := ih counter
                  (suppressOutputTapeStep output) hlater hnextInput hnextWork
                  hcounterSame hnextOutputInv
                refine ⟨1 + laterSteps, ?_⟩
                simpa [suppressOutputTapeTrace] using
                  (outputProbeTM tm).reachesIn_trans hsource hlaterRun

theorem outputProbeTM_step_halt_capture_internal (tm : TM n)
    (cfg : CursorCfg n tm.Q) (counter output : Tape) (bit : Bool)
    (hhalt : cfg.state = tm.qhalt)
    (hcursor : cfg.output = .cell (Γ.ofBool bit))
    (hcounter : counter.HasBinaryNat 0) :
    (outputProbeTM tm).step (outputProbeCfg tm cfg counter output) =
      some (outputProbeCaptureCfg tm bit
        (outputProbeNormalizeInput cfg.input)
        (outputProbeNormalizeWork fun i =>
          if h : i.val < n then cfg.work ⟨i.val, h⟩ else counter)
        (outputProbeNormalizeTape output)) := by
  have hblank : counter.read = Γ.blank :=
    hcounter.read_eq_blank_iff.mpr rfl
  cases bit <;>
    simp [TM.step, outputProbeTM, outputProbeCfg, outputProbeCaptureCfg,
      outputProbeCaptureCursor, outputProbeNormalizeInput,
      outputProbeNormalizeTape, allReadBack, outputProbeCounterIdx,
      Γ.ofBool, hhalt, hcursor, hblank] <;>
    funext i <;> rfl

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

/-- End-to-end capture when an observed source run halts on the selected
Boolean frontier cell. -/
theorem outputProbeTM_reachesIn_cursorTraceObserved_capture_internal
    (tm : TM n) {steps advances : ℕ}
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
      (outputProbeTM tm).halted done ∧ done.output.HasOutput [bit] := by
  obtain ⟨sourceSteps, hsourceRun⟩ :=
    outputProbeTM_reachesIn_cursorTraceObserved_internal
      (remaining := 0) tm counter output htrace hinput hwork
      (by simpa using hcounter) houtput
  let finalOutput := suppressOutputTapeTrace steps output
  let framedWork : Fin (n + 1) → Tape := fun i =>
    if h : i.val < n then after.work ⟨i.val, h⟩
    else outputProbeCounterTape 0
  let captureInput := outputProbeNormalizeInput after.input
  let captureWork := outputProbeNormalizeWork framedWork
  have hhaltStep := outputProbeTM_step_halt_capture_internal tm after
    (outputProbeCounterTape 0) finalOutput bit hhalt hcursor
    (outputProbeCounterTape_hasBinaryNat_internal 0)
  have hfinalRead : finalOutput.read ≠ Γ.start := by
    rw [Tape.read, hphysicalHead]
    intro hstart
    rw [hphysicalCells] at hstart
    simp [Tape.init] at hstart
  have hfinalNormalize : outputProbeNormalizeTape finalOutput = finalOutput :=
    outputProbeNormalizeTape_eq_self_internal hfinalRead
  have hhaltStep' :
      (outputProbeTM tm).step
        (outputProbeCfg tm after (outputProbeCounterTape 0) finalOutput) =
        some (outputProbeCaptureCfg tm bit captureInput captureWork
          finalOutput) := by
    simpa [captureInput, captureWork, framedWork, hfinalNormalize] using
      hhaltStep
  obtain ⟨hcaptureRun, hdoneHalt, hdoneOutput⟩ :=
    outputProbeTM_capture_hasOutput_internal tm bit captureInput captureWork
      finalOutput hphysicalHead hphysicalCells
  let done := outputProbeDoneCfg tm bit captureInput captureWork finalOutput
  have htoCapture :=
    (outputProbeTM tm).reachesIn_snoc hsourceRun hhaltStep'
  have hrun := (outputProbeTM tm).reachesIn_trans htoCapture hcaptureRun
  refine ⟨sourceSteps + 2, done, ?_, ?_, ?_⟩
  · simpa [done, finalOutput, Nat.add_assoc] using hrun
  · simpa [done] using hdoneHalt
  · simpa [done] using hdoneOutput

end TM

end Complexity
