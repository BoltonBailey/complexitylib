/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Combinators.WorkSymbolBranch
import Complexitylib.Models.TuringMachine.OutputProbeDecodeNat.Defs
import Complexitylib.Models.TuringMachine.OutputProbeDispatch
import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor
import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc
import Complexitylib.Models.TuringMachine.Subroutines.ClearWork

/-!
# Decoding terminated-unary fields through output probes -- internals
-/

namespace Complexity

namespace TM

private theorem outputProbeDecodeNatRun_inactive_internal
    (query : FormulaCode.BitOracle) (fuel cursor value : ℕ) :
    outputProbeDecodeNatRun query fuel
        { cursor := cursor, value := value, active := false } =
      { cursor := cursor, value := value, active := false } := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simpa [outputProbeDecodeNatRun, outputProbeDecodeNatStep] using ih

theorem outputProbeDecodeNatRun_result_internal
    (query : FormulaCode.BitOracle) (fuel cursor value : ℕ) :
    (outputProbeDecodeNatRun query fuel
      { cursor := cursor, value := value, active := true }).result? =
        FormulaCode.BitOracle.decodeNatAt? query fuel cursor value := by
  induction fuel generalizing cursor value with
  | zero => rfl
  | succ fuel ih =>
      rw [FormulaCode.BitOracle.decodeNatAt?]
      simp only [outputProbeDecodeNatRun, outputProbeDecodeNatStep, if_true]
      cases hbit : query cursor with
      | none =>
          simp only
          rw [ih]
          cases fuel <;>
            simp [FormulaCode.BitOracle.decodeNatAt?, hbit]
      | some bit =>
          cases bit with
          | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
              rw [outputProbeDecodeNatRun_inactive_internal]
              rfl
          | true =>
              simpa [hbit] using ih (cursor + 1) (value + 1)

private theorem outputProbeDecodeNatCounterTape_parked_internal
    (value : ℕ) : Parked (outputProbeCounterTape value) := by
  have h : (outputProbeCounterTape value).HasBinaryNat value := by
    simpa [outputProbeCounterTape] using
      Tape.init_move_right_hasBinaryNat value
  refine ⟨by rw [h.2.1], ?_⟩
  exact Tape.HasBinaryContent.cells_ne_start h.2.2

private theorem outputProbeDecodeNatUpdateOuter_parked_internal
    (n : ℕ) {controllerTapes : ℕ}
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (idx : Fin controllerTapes) (value : ℕ) :
    ∀ i, ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
      Parked (Function.update outerExtras
        (outputProbeIndexedControllerIdx n idx)
        (outputProbeCounterTape value) i) := by
  intro i hi
  by_cases heq : i = outputProbeIndexedControllerIdx n idx
  · subst i
    rw [Function.update_self]
    exact outputProbeDecodeNatCounterTape_parked_internal value
  · rw [Function.update_of_ne heq]
    exact houter i hi

private theorem outputProbeDecodeNatSucc_hoareTime_internal
    (tm : TM n) (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output) (idx : Fin controllerTapes) (value : ℕ)
    (hvalue :
      (outerExtras (outputProbeIndexedControllerIdx n idx)).HasBinaryNat
        value) :
    (binarySuccTM
      (outputProbeIndexedControllerIdx n idx)).HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (outputProbeLatchFramePost tm controllerTapes
        (Function.update outerExtras
          (outputProbeIndexedControllerIdx n idx)
          (outputProbeCounterTape (value + 1)))
        input output extras false)
      (binarySuccTime value) := by
  let physical := outputProbeIndexedControllerIdx n idx
  let nextTape := outputProbeCounterTape (value + 1)
  intro inp work out hpost
  obtain ⟨hinput, hwork, hout⟩ := outputProbeLatchFramePost_parked tm
    controllerTapes outerExtras input output extras false hextras houter
    houtput inp work out hpost
  have htarget : (work physical).HasBinaryNat value := by
    rw [outputProbeLatchFramePost_controller tm controllerTapes outerExtras
      input output extras false inp work out hpost idx]
    exact hvalue
  obtain ⟨done, hreach, hhalt, hinputDone, hotherDone, htargetDone,
      houtputDone⟩ :=
    binarySuccTM_reachesIn_frame physical value inp work out htarget
      hinput.read_ne_start (fun i _ => (hwork i).read_ne_start)
      hout.read_ne_start
  have hworkDone : done.work = Function.update work physical nextTape := by
    funext i
    by_cases hi : i = physical
    · subst i
      rw [Function.update_self]
      exact htargetDone.eq_init_move_right
    · rw [Function.update_of_ne hi]
      exact hotherDone i hi
  refine ⟨done, binarySuccTime value, le_rfl, hreach, hhalt, ?_⟩
  rw [hinputDone, hworkDone, houtputDone]
  simpa [physical, nextTape] using
    outputProbeLatchFramePost_updateController tm controllerTapes outerExtras
      input output extras false inp work out hpost idx nextTape

private theorem outputProbeDecodeNatClear_hoareTime_internal
    (tm : TM n) (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output) (idx : Fin controllerTapes)
    (hone :
      (outerExtras (outputProbeIndexedControllerIdx n idx)).HasBinaryNat 1) :
    (clearWorkTM
      (outputProbeIndexedControllerIdx n idx)).HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (outputProbeLatchFramePost tm controllerTapes
        (Function.update outerExtras
          (outputProbeIndexedControllerIdx n idx)
          (outputProbeCounterTape 0))
        input output extras false)
      (clearWorkTimeBound 1) := by
  let physical := outputProbeIndexedControllerIdx n idx
  intro inp work out hpost
  obtain ⟨hinput, hwork, hout⟩ := outputProbeLatchFramePost_parked tm
    controllerTapes outerExtras input output extras false hextras houter
    houtput inp work out hpost
  have htargetNat : (work physical).HasBinaryNat 1 := by
    rw [outputProbeLatchFramePost_controller tm controllerTapes outerExtras
      input output extras false inp work out hpost idx]
    exact hone
  have htarget : work physical =
      (Tape.init ((1 : ℕ).bits.map Γ.ofBool)).move Dir3.right :=
    htargetNat.eq_init_move_right
  have hclear := clearWorkTM_hoareTime_frame physical (1 : ℕ).bits inp work out
    htarget hinput (fun i _ => hwork i) hout
  obtain ⟨done, elapsed, helapsed, hreach, hhalt, hinputDone, hworkDone,
      houtputDone⟩ := hclear inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨done, elapsed, ?_, hreach, hhalt, ?_⟩
  · simpa using helapsed
  · rw [hinputDone, hworkDone, houtputDone]
    simpa [physical, outputProbeCounterTape] using
      outputProbeLatchFramePost_updateController tm controllerTapes
        outerExtras input output extras false inp work out hpost idx
        (outputProbeCounterTape 0)

theorem outputProbeDecodeNatZeroTM_hoareTime_internal
    (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx activeIdx : Fin controllerTapes)
    (hdistinct : cursorIdx ≠ activeIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output) (cursor : ℕ)
    (hcursor :
      (outerExtras (outputProbeDecodeNatCursorIdx n cursorIdx))
        |>.HasBinaryNat cursor)
    (hactive :
      (outerExtras (outputProbeDecodeNatActiveIdx n activeIdx))
        |>.HasBinaryNat 1) :
    (outputProbeDecodeNatZeroTM n controllerTapes cursorIdx
      activeIdx).HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeNatZeroOuterExtras n cursorIdx activeIdx outerExtras
          cursor)
        input output extras false)
      (clearWorkTimeBound 1 + 1 + binarySuccTime cursor) := by
  let activePhysical := outputProbeDecodeNatActiveIdx n activeIdx
  let cursorPhysical := outputProbeDecodeNatCursorIdx n cursorIdx
  let clearedOuter := Function.update outerExtras activePhysical
    (outputProbeCounterTape 0)
  have hphysical : cursorPhysical ≠ activePhysical := by
    intro heq
    exact hdistinct
      (outputProbeIndexedControllerIdx_injective n heq)
  have hclear := outputProbeDecodeNatClear_hoareTime_internal tm
    controllerTapes outerExtras input output extras hextras houter houtput
    activeIdx hactive
  have hclearedParked : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (clearedOuter i) :=
    outputProbeDecodeNatUpdateOuter_parked_internal n outerExtras houter
      activeIdx 0
  have hclearedCursor : (clearedOuter cursorPhysical).HasBinaryNat cursor := by
    dsimp only [clearedOuter]
    rw [Function.update_of_ne hphysical]
    exact hcursor
  have hsucc := outputProbeDecodeNatSucc_hoareTime_internal tm
    controllerTapes clearedOuter input output extras hextras hclearedParked
    houtput cursorIdx cursor hclearedCursor
  apply seqTM_hoareTime _ _ hclear
  · intro inp work out hpost
    obtain ⟨hinp, hwork, hout⟩ := outputProbeLatchFramePost_parked tm
      controllerTapes clearedOuter input output extras false hextras
      hclearedParked houtput inp work out hpost
    obtain ⟨hinpEq, hworkEq, houtEq⟩ :=
      phaseTransition_eq_self_of_reads_ne_start hinp.read_ne_start
        (fun i => (hwork i).read_ne_start) hout.read_ne_start
    simpa [hinpEq, hworkEq, houtEq] using hpost
  · simpa [outputProbeDecodeNatZeroTM,
      outputProbeDecodeNatZeroOuterExtras, clearedOuter, activePhysical,
      cursorPhysical] using hsucc

theorem outputProbeDecodeNatOneTM_hoareTime_internal
    (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx valueIdx : Fin controllerTapes)
    (hdistinct : cursorIdx ≠ valueIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output) (cursor value : ℕ)
    (hcursor :
      (outerExtras (outputProbeDecodeNatCursorIdx n cursorIdx))
        |>.HasBinaryNat cursor)
    (hvalue :
      (outerExtras (outputProbeDecodeNatValueIdx n valueIdx))
        |>.HasBinaryNat value) :
    (outputProbeDecodeNatOneTM n controllerTapes cursorIdx
      valueIdx).HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeNatOneOuterExtras n cursorIdx valueIdx outerExtras
          cursor value)
        input output extras false)
      (binarySuccTime value + 1 + binarySuccTime cursor) := by
  let valuePhysical := outputProbeDecodeNatValueIdx n valueIdx
  let cursorPhysical := outputProbeDecodeNatCursorIdx n cursorIdx
  let incrementedOuter := Function.update outerExtras valuePhysical
    (outputProbeCounterTape (value + 1))
  have hphysical : cursorPhysical ≠ valuePhysical := by
    intro heq
    exact hdistinct
      (outputProbeIndexedControllerIdx_injective n heq)
  have hvalueSucc := outputProbeDecodeNatSucc_hoareTime_internal tm
    controllerTapes outerExtras input output extras hextras houter houtput
    valueIdx value hvalue
  have hincrementedParked : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (incrementedOuter i) :=
    outputProbeDecodeNatUpdateOuter_parked_internal n outerExtras houter
      valueIdx (value + 1)
  have hincrementedCursor :
      (incrementedOuter cursorPhysical).HasBinaryNat cursor := by
    dsimp only [incrementedOuter]
    rw [Function.update_of_ne hphysical]
    exact hcursor
  have hcursorSucc := outputProbeDecodeNatSucc_hoareTime_internal tm
    controllerTapes incrementedOuter input output extras hextras
    hincrementedParked houtput cursorIdx cursor hincrementedCursor
  apply seqTM_hoareTime _ _ hvalueSucc
  · intro inp work out hpost
    obtain ⟨hinp, hwork, hout⟩ := outputProbeLatchFramePost_parked tm
      controllerTapes incrementedOuter input output extras false hextras
      hincrementedParked houtput inp work out hpost
    obtain ⟨hinpEq, hworkEq, houtEq⟩ :=
      phaseTransition_eq_self_of_reads_ne_start hinp.read_ne_start
        (fun i => (hwork i).read_ne_start) hout.read_ne_start
    simpa [hinpEq, hworkEq, houtEq] using hpost
  · simpa [outputProbeDecodeNatOneTM,
      outputProbeDecodeNatOneOuterExtras, incrementedOuter, valuePhysical,
      cursorPhysical] using hcursorSucc

theorem outputProbeDecodeNatActiveTM_of_latch_hoareTimeSpace_internal
    (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx scratchIdx valueIdx activeIdx : Fin controllerTapes)
    (hcursorValue : cursorIdx ≠ valueIdx)
    (hcursorActive : cursorIdx ≠ activeIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (bit : Bool)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output) (cursor value : ℕ)
    (hcursor :
      (outerExtras (outputProbeDecodeNatCursorIdx n cursorIdx))
        |>.HasBinaryNat cursor)
    (hvalue :
      (outerExtras (outputProbeDecodeNatValueIdx n valueIdx))
        |>.HasBinaryNat value)
    (hactive :
      (outerExtras (outputProbeDecodeNatActiveIdx n activeIdx))
        |>.HasBinaryNat 1)
    {pre : TapePred (0 + outputProbeControllerTapes n + controllerTapes)}
    {latchTime latchSpace inputLength clearInitialSpace zeroInitialSpace
      oneInitialSpace : ℕ}
    (hlatch : (outputProbeIndexedLatchTM tm controllerTapes cursorIdx
      scratchIdx).HoareTimeSpace pre
        (outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras bit)
        latchTime inputLength latchSpace)
    (hclearInitial : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras true inp work out →
        ({ state :=
              (clearWorkTM
                (outputProbeLatchIdx n controllerTapes)).qstart
           input := inp
           work := work
           output := out } :
          Cfg (0 + outputProbeControllerTapes n + controllerTapes)
            (clearWorkTM
              (outputProbeLatchIdx n controllerTapes)).Q).WithinAuxSpace
            inputLength clearInitialSpace)
    (hzeroInitial : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false inp work out →
        ({ state := (outputProbeDecodeNatZeroTM n controllerTapes cursorIdx
              activeIdx).qstart
           input := inp
           work := work
           output := out } :
          Cfg (0 + outputProbeControllerTapes n + controllerTapes)
            (outputProbeDecodeNatZeroTM n controllerTapes cursorIdx
              activeIdx).Q).WithinAuxSpace inputLength zeroInitialSpace)
    (honeInitial : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false inp work out →
        ({ state := (outputProbeDecodeNatOneTM n controllerTapes cursorIdx
              valueIdx).qstart
           input := inp
           work := work
           output := out } :
          Cfg (0 + outputProbeControllerTapes n + controllerTapes)
            (outputProbeDecodeNatOneTM n controllerTapes cursorIdx
              valueIdx).Q).WithinAuxSpace inputLength oneInitialSpace) :
    (outputProbeDecodeNatActiveTM tm controllerTapes cursorIdx scratchIdx
      valueIdx activeIdx).HoareTimeSpace pre
        (outputProbeLatchFramePost tm controllerTapes
          (outputProbeDecodeNatOuterExtrasAfter n cursorIdx valueIdx activeIdx
            outerExtras cursor value bit)
          input output extras false)
        (latchTime + 1 +
          outputProbeLatchDispatchTime bit
            (clearWorkTimeBound 1 + 1 + binarySuccTime cursor)
            (clearWorkTimeBound 1 + 1 +
              (binarySuccTime value + 1 + binarySuccTime cursor)))
        inputLength
        (max latchSpace
          (if bit then
            max (clearInitialSpace + clearWorkTimeBound 1)
              (oneInitialSpace +
                (binarySuccTime value + 1 + binarySuccTime cursor))
          else
            zeroInitialSpace +
              (clearWorkTimeBound 1 + 1 + binarySuccTime cursor))) := by
  have hzeroTime := outputProbeDecodeNatZeroTM_hoareTime_internal tm
    controllerTapes cursorIdx activeIdx hcursorActive outerExtras input output
    extras hextras houter houtput cursor hcursor hactive
  have hzero := hzeroTime.toHoareTimeSpace hzeroInitial
  have honeTime := outputProbeDecodeNatOneTM_hoareTime_internal tm
    controllerTapes cursorIdx valueIdx hcursorValue outerExtras input output
    extras hextras houter houtput cursor value hcursor hvalue
  have hone := honeTime.toHoareTimeSpace honeInitial
  simpa [outputProbeDecodeNatActiveTM,
    outputProbeDecodeNatOuterExtrasAfter] using
    outputProbeIndexedResetDispatchTM_of_latch_hoareTimeSpace tm
      controllerTapes cursorIdx scratchIdx outerExtras input output extras bit
      hextras houter houtput
      (outputProbeDecodeNatZeroTM n controllerTapes cursorIdx activeIdx)
      (outputProbeDecodeNatOneTM n controllerTapes cursorIdx valueIdx)
      (post := fun branch =>
        outputProbeLatchFramePost tm controllerTapes
          (outputProbeDecodeNatOuterExtrasAfter n cursorIdx valueIdx activeIdx
            outerExtras cursor value branch)
          input output extras false)
      hlatch hclearInitial hzero hone

theorem ComputesInSpace.outputProbeDecodeNatActiveTM_hoareTime_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (input : List Bool) (cursor : ℕ)
    (hcursorBound : cursor < (f input).length)
    (output : Tape) (houtput : Parked output)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (hcleanupCounter :
      (extras (outputProbeCleanupCounterIdx n)).HasBinaryNat 0)
    (cleanupLimit : ℕ)
    (hcleanupLimit :
      (extras (outputProbeCleanupLimitIdx n)).HasBinaryNat cleanupLimit)
    (hlimit : outputProbeCaptureSpace (max 1 (space input.length))
      (cursor + 1) ≤ cleanupLimit)
    (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (cursorIdx scratchIdx valueIdx activeIdx : Fin controllerTapes)
    (hcursorScratch : cursorIdx ≠ scratchIdx)
    (hcursorValue : cursorIdx ≠ valueIdx)
    (hcursorActive : cursorIdx ≠ activeIdx)
    (hcursor :
      (outerExtras (outputProbeDecodeNatCursorIdx n cursorIdx))
        |>.HasBinaryNat cursor)
    (hscratch :
      (outerExtras (outputProbeIndexedControllerIdx n scratchIdx))
        |>.HasBinaryNat 0)
    (value : ℕ)
    (hvalue :
      (outerExtras (outputProbeDecodeNatValueIdx n valueIdx))
        |>.HasBinaryNat value)
    (hactive :
      (outerExtras (outputProbeDecodeNatActiveIdx n activeIdx))
        |>.HasBinaryNat 1) :
    ∃ (bodyBound : ℕ)
      (pre : TapePred
        (0 + outputProbeControllerTapes n + controllerTapes)),
      pre
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).input
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).work
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).output ∧
      (outputProbeDecodeNatActiveTM tm controllerTapes cursorIdx scratchIdx
        valueIdx activeIdx).HoareTime pre
          (outputProbeLatchFramePost tm controllerTapes
            (outputProbeDecodeNatOuterExtrasAfter n cursorIdx valueIdx
              activeIdx outerExtras cursor value
              ((f input)[cursor]'hcursorBound))
            input output extras false)
          bodyBound := by
  let frame := outputProbeLatchFrameCfg tm controllerTapes outerExtras input
    output extras false
  let queryFrame := placeWorkCfg (outputProbePlacedTM tm) 0 controllerTapes
    outerExtras
    (outputProbePlacedFrameCfg tm input
      (outputProbeCounterTape (cursor + 1)) output extras)
  let frameSpace := Finset.univ.sup fun i => (extras i).head
  let outerFrameSpace := Finset.univ.sup fun i => (outerExtras i).head
  let initialSpace := Finset.univ.sup fun i => (frame.work i).head
  let pre : TapePred
      (0 + outputProbeControllerTapes n + controllerTapes) :=
    fun inp work out =>
      inp = queryFrame.input ∧ work = frame.work ∧ out = output
  have hframePost := outputProbeLatchFrameCfg_post tm controllerTapes
    outerExtras input output extras false
  have hparked := outputProbeLatchFramePost_parked tm controllerTapes
    outerExtras input output extras false hextras houter houtput frame.input
    frame.work frame.output hframePost
  have hframeBound : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i →
      (extras i).head ≤ frameSpace := by
    intro i _hi
    exact Finset.le_sup (f := fun j => (extras j).head)
      (Finset.mem_univ i)
  have houterRead : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        (outerExtras i).read ≠ Γ.start := by
    intro i hi
    exact (houter i hi).read_ne_start
  have houterBound : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        (outerExtras i).head ≤ outerFrameSpace := by
    intro i _hi
    exact Finset.le_sup (f := fun j => (outerExtras j).head)
      (Finset.mem_univ i)
  have hworkBound : ∀ i, (frame.work i).head ≤ initialSpace := by
    intro i
    exact Finset.le_sup (f := fun j => (frame.work j).head)
      (Finset.mem_univ i)
  have hqueryInput : queryFrame.input = frame.input := by
    rfl
  have hqueryOutput : frame.output = output := by
    simp [frame, outputProbeLatchFrameCfg, outputProbeLatchInnerFrameCfg,
      outputProbePlacedFrameCfg]
  have hcursorWork :
      (frame.work (outputProbeIndexedControllerIdx n cursorIdx))
        |>.HasBinaryNat cursor := by
    rw [outputProbeLatchFramePost_controller tm controllerTapes outerExtras
      input output extras false frame.input frame.work frame.output hframePost
      cursorIdx]
    exact hcursor
  have hscratchWork :
      (frame.work (outputProbeIndexedControllerIdx n scratchIdx))
        |>.HasBinaryNat 0 := by
    rw [outputProbeLatchFramePost_controller tm controllerTapes outerExtras
      input output extras false frame.input frame.work frame.output hframePost
      scratchIdx]
    exact hscratch
  have hframeWork : frame.work = Function.update queryFrame.work
      (outputProbeIndexedCountdownIdx n controllerTapes)
      (outputProbeCounterTape 0) := by
    exact outputProbeLatchFrameCfg_work_eq_queryUpdate tm input output extras
      hcleanupCounter controllerTapes cursor outerExtras
  have hcountdown :
      (frame.work (outputProbeIndexedCountdownIdx n controllerTapes))
        |>.HasBinaryNat 0 := by
    rw [hframeWork, Function.update_self]
    exact Tape.init_move_right_hasBinaryNat 0
  have hqueryWork : ∀ i,
      i ≠ outputProbeIndexedCountdownIdx n controllerTapes →
      frame.work i = queryFrame.work i := by
    intro i hi
    rw [hframeWork, Function.update_of_ne hi]
  have hinputSpace : queryFrame.input.head ≤
      input.length + initialSpace + 1 := by
    simp [queryFrame, outputProbePlacedFrameCfg, outputProbeStartedCfg,
      Tape.move]
  obtain ⟨latchTime, hlatch⟩ :=
    hcomp.outputProbeIndexedLatchTM_hoareTimeSpace input cursor hcursorBound
      output houtput extras frameSpace cleanupLimit hextras hframeBound
      hcleanupCounter hcleanupLimit hlimit controllerTapes outerExtras
      outerFrameSpace houterRead houterBound cursorIdx scratchIdx
      hcursorScratch initialSpace frame.work hcursorWork hcountdown
      hscratchWork (hqueryInput ▸ hparked.1) hparked.2.1 hworkBound hinputSpace
      hqueryWork
  let falseFrame := outputProbeLatchFrameCfg tm controllerTapes outerExtras
    input output extras false
  let trueFrame := outputProbeLatchFrameCfg tm controllerTapes outerExtras
    input output extras true
  let falseSpace := Finset.univ.sup fun i => (falseFrame.work i).head
  let trueSpace := Finset.univ.sup fun i => (trueFrame.work i).head
  have hframeInitial (bit : Bool) : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras bit inp work out →
      ({ state := (skipTM (n := 0 + outputProbeControllerTapes n +
              controllerTapes)).qstart
         input := inp
         work := work
         output := out } :
        Cfg (0 + outputProbeControllerTapes n + controllerTapes)
          (skipTM (n := 0 + outputProbeControllerTapes n +
            controllerTapes)).Q).WithinAuxSpace input.length
          (Finset.univ.sup fun i =>
            ((outputProbeLatchFrameCfg tm controllerTapes outerExtras input
              output extras bit).work i).head) := by
    intro inp work out hpost
    obtain ⟨hinp, hwork, _hout⟩ := outputProbeLatchFramePost_eq_frameCfg tm
      controllerTapes outerExtras input output extras bit inp work out hpost
    subst inp
    subst work
    constructor
    · intro i
      exact Finset.le_sup
        (f := fun j =>
          ((outputProbeLatchFrameCfg tm controllerTapes outerExtras input
            output extras bit).work j).head)
        (Finset.mem_univ i)
    · simp [outputProbeLatchFrameCfg, outputProbeLatchInnerFrameCfg,
        outputProbePlacedFrameCfg, outputProbeStartedCfg, Tape.move]
  have hclearInitial : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras true inp work out →
      ({ state := (clearWorkTM
              (outputProbeLatchIdx n controllerTapes)).qstart
         input := inp
         work := work
         output := out } :
        Cfg (0 + outputProbeControllerTapes n + controllerTapes)
          (clearWorkTM (outputProbeLatchIdx n controllerTapes)).Q
        ).WithinAuxSpace input.length trueSpace := by
    simpa [trueSpace, trueFrame] using hframeInitial true
  have hzeroInitial : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false inp work out →
      ({ state := (outputProbeDecodeNatZeroTM n controllerTapes cursorIdx
              activeIdx).qstart
         input := inp
         work := work
         output := out } :
        Cfg (0 + outputProbeControllerTapes n + controllerTapes)
          (outputProbeDecodeNatZeroTM n controllerTapes cursorIdx
            activeIdx).Q).WithinAuxSpace input.length falseSpace := by
    simpa [falseSpace, falseFrame] using hframeInitial false
  have honeInitial : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false inp work out →
      ({ state := (outputProbeDecodeNatOneTM n controllerTapes cursorIdx
              valueIdx).qstart
         input := inp
         work := work
         output := out } :
        Cfg (0 + outputProbeControllerTapes n + controllerTapes)
          (outputProbeDecodeNatOneTM n controllerTapes cursorIdx
            valueIdx).Q).WithinAuxSpace input.length falseSpace := by
    simpa [falseSpace, falseFrame] using hframeInitial false
  let bodyBound := outputProbeIndexedPrepareTime cursor + 1 + latchTime + 1 +
    outputProbeLatchDispatchTime ((f input)[cursor]'hcursorBound)
      (clearWorkTimeBound 1 + 1 + binarySuccTime cursor)
      (clearWorkTimeBound 1 + 1 +
        (binarySuccTime value + 1 + binarySuccTime cursor))
  have hbody :=
    outputProbeDecodeNatActiveTM_of_latch_hoareTimeSpace_internal tm
      controllerTapes cursorIdx scratchIdx valueIdx activeIdx hcursorValue
      hcursorActive outerExtras input output extras
      ((f input)[cursor]'hcursorBound) hextras houter houtput cursor value
      hcursor hvalue hactive hlatch hclearInitial hzeroInitial honeInitial
  refine ⟨bodyBound, pre, ?_, ?_⟩
  · exact ⟨hqueryInput.symm, rfl, hqueryOutput⟩
  · simpa [bodyBound] using hbody.1

private theorem skipTM_isTransducer_internal {n : ℕ} :
    (skipTM (n := n)).IsTransducer := by
  intro state _iHead _wHeads oHead
  cases state <;> cases oHead <;> simp [skipTM, idleDir]

theorem outputProbeDecodeNatZeroTM_isTransducer_internal
    (n controllerTapes : ℕ) (cursorIdx activeIdx : Fin controllerTapes) :
    (outputProbeDecodeNatZeroTM n controllerTapes cursorIdx
      activeIdx).IsTransducer := by
  apply IsTransducer.seqTM
  · exact clearWorkTM_isTransducer _
  · exact binarySuccTM_isTransducer _

theorem outputProbeDecodeNatOneTM_isTransducer_internal
    (n controllerTapes : ℕ) (cursorIdx valueIdx : Fin controllerTapes) :
    (outputProbeDecodeNatOneTM n controllerTapes cursorIdx
      valueIdx).IsTransducer := by
  apply IsTransducer.seqTM
  · exact binarySuccTM_isTransducer _
  · exact binarySuccTM_isTransducer _

theorem outputProbeDecodeNatActiveTM_isTransducer_internal
    (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx scratchIdx valueIdx activeIdx : Fin controllerTapes) :
    (outputProbeDecodeNatActiveTM tm controllerTapes cursorIdx scratchIdx
      valueIdx activeIdx).IsTransducer := by
  apply IsTransducer.outputProbeIndexedResetDispatchTM
  · exact outputProbeDecodeNatZeroTM_isTransducer_internal n controllerTapes
      cursorIdx activeIdx
  · exact outputProbeDecodeNatOneTM_isTransducer_internal n controllerTapes
      cursorIdx valueIdx

theorem outputProbeDecodeNatBodyTM_isTransducer_internal
    (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx scratchIdx valueIdx activeIdx : Fin controllerTapes) :
    (outputProbeDecodeNatBodyTM tm controllerTapes cursorIdx scratchIdx
      valueIdx activeIdx).IsTransducer := by
  apply IsTransducer.branchWorkSymbolTM
  · exact outputProbeDecodeNatActiveTM_isTransducer_internal tm
      controllerTapes cursorIdx scratchIdx valueIdx activeIdx
  · exact skipTM_isTransducer_internal

theorem outputProbeDecodeNatTM_isTransducer_internal
    (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx scratchIdx valueIdx activeIdx loopIdx fuelIdx :
      Fin controllerTapes) :
    (outputProbeDecodeNatTM tm controllerTapes cursorIdx scratchIdx valueIdx
      activeIdx loopIdx fuelIdx).IsTransducer := by
  apply IsTransducer.binaryForTM
  exact outputProbeDecodeNatBodyTM_isTransducer_internal tm controllerTapes
    cursorIdx scratchIdx valueIdx activeIdx

end TM

end Complexity
