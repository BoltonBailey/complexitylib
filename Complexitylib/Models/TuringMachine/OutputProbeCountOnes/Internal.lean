/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Hoare.Space
import Complexitylib.Models.TuringMachine.OutputProbeCountOnes.Defs
import Complexitylib.Models.TuringMachine.OutputProbeDispatch
import Complexitylib.Models.TuringMachine.OutputProbeIndexed
import Complexitylib.Models.TuringMachine.OutputProbeScan.Internal
import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc

/-!
# Counting one bits through dynamically indexed output probes -- internals
-/

namespace Complexity

namespace TM

private theorem skipTM_isTransducer_internal {n : ℕ} :
    (skipTM (n := n)).IsTransducer := by
  intro state _iHead _wHeads oHead
  cases state <;> cases oHead <;> simp [skipTM, idleDir]

theorem outputProbeCountOnes_zero_hoareTimeSpace_internal
    (tm : TM n) (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (countIdx : Fin controllerTapes) (count inputLength initialSpace : ℕ)
    (hinitial : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false inp work out →
        ({ state := (skipTM (n := 0 + outputProbeControllerTapes n +
              controllerTapes)).qstart
           input := inp
           work := work
           output := out } :
          Cfg (0 + outputProbeControllerTapes n + controllerTapes)
            (skipTM (n := 0 + outputProbeControllerTapes n +
              controllerTapes)).Q).WithinAuxSpace inputLength initialSpace) :
    (skipTM (n := 0 + outputProbeControllerTapes n +
      controllerTapes)).HoareTimeSpace
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeCountOnesOuterExtrasAfter n countIdx outerExtras count
          false)
        input output extras false)
      1 inputLength (initialSpace + 1) := by
  have htime : (skipTM (n := 0 + outputProbeControllerTapes n +
      controllerTapes)).HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeCountOnesOuterExtrasAfter n countIdx outerExtras count
          false)
        input output extras false) 1 := by
    intro inp work out hpost
    obtain ⟨hinput, hwork, hout⟩ := outputProbeLatchFramePost_parked tm
      controllerTapes outerExtras input output extras false hextras houter
      houtput inp work out hpost
    have hskip := skipTM_hoareTime_frame inp work out hinput hwork hout
    obtain ⟨done, elapsed, helapsed, hreach, hhalt, hinputDone,
        hworkDone, houtputDone⟩ :=
      hskip inp work out ⟨rfl, rfl, rfl⟩
    refine ⟨done, elapsed, helapsed, hreach, hhalt, ?_⟩
    rw [hinputDone, hworkDone, houtputDone]
    simpa [outputProbeCountOnesOuterExtrasAfter] using hpost
  exact htime.toHoareTimeSpace hinitial

theorem outputProbeCountOnes_one_hoareTimeSpace_internal
    (tm : TM n) (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (countIdx : Fin controllerTapes) (count inputLength initialSpace : ℕ)
    (hcount :
      (outerExtras (outputProbeIndexedControllerIdx n countIdx)).HasBinaryNat
        count)
    (hinitial : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false inp work out →
        ({ state := (binarySuccTM
              (outputProbeIndexedControllerIdx n countIdx)).qstart
           input := inp
           work := work
           output := out } :
          Cfg (0 + outputProbeControllerTapes n + controllerTapes)
            (binarySuccTM
              (outputProbeIndexedControllerIdx n countIdx)).Q).WithinAuxSpace
            inputLength initialSpace) :
    (binarySuccTM
      (outputProbeIndexedControllerIdx n countIdx)).HoareTimeSpace
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeCountOnesOuterExtrasAfter n countIdx outerExtras count true)
        input output extras false)
      (binarySuccTime count) inputLength
      (initialSpace + binarySuccTime count) := by
  let physicalCount := outputProbeIndexedControllerIdx n countIdx
  let nextTape := outputProbeCounterTape (count + 1)
  have htime : (binarySuccTM physicalCount).HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeCountOnesOuterExtrasAfter n countIdx outerExtras count true)
        input output extras false)
      (binarySuccTime count) := by
    intro inp work out hpost
    obtain ⟨hinput, hwork, hout⟩ := outputProbeLatchFramePost_parked tm
      controllerTapes outerExtras input output extras false hextras houter
      houtput inp work out hpost
    have hcountWork : (work physicalCount).HasBinaryNat count := by
      rw [outputProbeLatchFramePost_controller tm controllerTapes
        outerExtras input output extras false inp work out hpost countIdx]
      exact hcount
    obtain ⟨done, hreach, hhalt, hinputDone, hotherDone, hcountDone,
        houtputDone⟩ :=
      binarySuccTM_reachesIn_frame physicalCount count inp work out
        hcountWork hinput.read_ne_start
        (fun i _ => (hwork i).read_ne_start) hout.read_ne_start
    have hnext : done.work = Function.update work physicalCount nextTape := by
      funext i
      by_cases hi : i = physicalCount
      · subst i
        rw [Function.update_self]
        exact hcountDone.eq_init_move_right
      · rw [Function.update_of_ne hi]
        exact hotherDone i hi
    refine ⟨done, binarySuccTime count, le_rfl, hreach, hhalt, ?_⟩
    rw [hinputDone, hnext, houtputDone]
    simpa [physicalCount, nextTape, outputProbeCountOnesOuterExtrasAfter]
      using outputProbeLatchFramePost_updateController tm controllerTapes
        outerExtras input output extras false inp work out hpost countIdx
        nextTape
  exact htime.toHoareTimeSpace hinitial

theorem outputProbeCountOnesBodyTM_of_latch_hoareTimeSpace_internal
    (tm : TM n) (controllerTapes : ℕ)
    (addressIdx scratchIdx countIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (bit : Bool)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (count : ℕ)
    (hcount :
      (outerExtras (outputProbeIndexedControllerIdx n countIdx)).HasBinaryNat
        count)
    {pre : TapePred (0 + outputProbeControllerTapes n + controllerTapes)}
    {latchTime latchSpace inputLength clearInitialSpace zeroInitialSpace
      oneInitialSpace : ℕ}
    (hlatch : (outputProbeIndexedLatchTM tm controllerTapes addressIdx
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
        ({ state := (skipTM (n := 0 + outputProbeControllerTapes n +
              controllerTapes)).qstart
           input := inp
           work := work
           output := out } :
          Cfg (0 + outputProbeControllerTapes n + controllerTapes)
            (skipTM (n := 0 + outputProbeControllerTapes n +
              controllerTapes)).Q).WithinAuxSpace inputLength
            zeroInitialSpace)
    (honeInitial : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false inp work out →
        ({ state := (binarySuccTM
              (outputProbeIndexedControllerIdx n countIdx)).qstart
           input := inp
           work := work
           output := out } :
          Cfg (0 + outputProbeControllerTapes n + controllerTapes)
            (binarySuccTM
              (outputProbeIndexedControllerIdx n countIdx)).Q).WithinAuxSpace
            inputLength oneInitialSpace) :
    (outputProbeCountOnesBodyTM tm controllerTapes addressIdx scratchIdx
      countIdx).HoareTimeSpace pre
        (outputProbeLatchFramePost tm controllerTapes
          (outputProbeCountOnesOuterExtrasAfter n countIdx outerExtras count
            bit)
          input output extras false)
        (latchTime + 1 +
          outputProbeLatchDispatchTime bit 1
            (clearWorkTimeBound 1 + 1 + binarySuccTime count))
        inputLength
        (max latchSpace
          (if bit then
            max (clearInitialSpace + clearWorkTimeBound 1)
              (oneInitialSpace + binarySuccTime count)
          else zeroInitialSpace + 1)) := by
  have hzero := outputProbeCountOnes_zero_hoareTimeSpace_internal tm
    controllerTapes outerExtras input output extras hextras houter houtput
    countIdx count inputLength zeroInitialSpace hzeroInitial
  have hone := outputProbeCountOnes_one_hoareTimeSpace_internal tm
    controllerTapes outerExtras input output extras hextras houter houtput
    countIdx count inputLength oneInitialSpace hcount honeInitial
  simpa [outputProbeCountOnesBodyTM] using
    outputProbeIndexedResetDispatchTM_of_latch_hoareTimeSpace tm
      controllerTapes addressIdx scratchIdx outerExtras input output extras bit
      hextras houter houtput skipTM
      (binarySuccTM (outputProbeIndexedControllerIdx n countIdx))
      (post := fun branch =>
        outputProbeLatchFramePost tm controllerTapes
          (outputProbeCountOnesOuterExtrasAfter n countIdx outerExtras count
            branch)
          input output extras false)
      hlatch
      hclearInitial hzero hone

theorem IsTransducer.outputProbeCountOnesTM_internal
    {tm : TM n} {controllerTapes : ℕ}
    {addressIdx scratchIdx limitIdx countIdx : Fin controllerTapes} :
    (outputProbeCountOnesTM tm controllerTapes addressIdx scratchIdx limitIdx
      countIdx).IsTransducer := by
  unfold outputProbeCountOnesTM
  exact (skipTM_isTransducer_internal.outputProbeIndexedResetDispatchTM
      (binarySuccTM_isTransducer
        (outputProbeIndexedControllerIdx n countIdx))).binaryForTM
    (outputProbeIndexedControllerIdx n addressIdx)
    (outputProbeIndexedControllerIdx n limitIdx)

end TM

end Complexity
