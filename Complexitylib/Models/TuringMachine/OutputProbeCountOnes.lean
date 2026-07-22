/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeCountOnes.Defs
import Complexitylib.Models.TuringMachine.OutputProbeCountOnes.Internal

/-!
# Counting one bits through dynamically indexed output probes

This module certifies the Boolean continuations used by an occupancy-counting
scan. Both branches start with the physical query latch reset to zero. The
zero branch preserves the complete controller frame; the one branch increments
one canonical binary count register and updates only that register.
-/

namespace Complexity

namespace TM

/-- The zero continuation preserves the complete reset-latch controller frame. -/
theorem outputProbeCountOnes_zero_hoareTimeSpace
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
      1 inputLength (initialSpace + 1) :=
  outputProbeCountOnes_zero_hoareTimeSpace_internal tm controllerTapes
    outerExtras input output extras hextras houter houtput countIdx count
    inputLength initialSpace hinitial

/-- The one continuation increments exactly the designated canonical binary
count and preserves every other tape in the reset-latch controller frame. -/
theorem outputProbeCountOnes_one_hoareTimeSpace
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
      (initialSpace + binarySuccTime count) :=
  outputProbeCountOnes_one_hoareTimeSpace_internal tm controllerTapes
    outerExtras input output extras hextras houter houtput countIdx count
    inputLength initialSpace hcount hinitial

/-- A certified dynamic latch phase composes with reset-and-count dispatch.
The resulting body preserves the reset latch and updates only the count frame
when the queried bit is true. -/
theorem outputProbeCountOnesBodyTM_of_latch_hoareTimeSpace
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
          else zeroInitialSpace + 1)) :=
  outputProbeCountOnesBodyTM_of_latch_hoareTimeSpace_internal tm
    controllerTapes addressIdx scratchIdx countIdx outerExtras input output
    extras bit hextras houter houtput count hcount hlatch hclearInitial
    hzeroInitial honeInitial

/-- Counting queried one bits preserves one-way output safety. -/
theorem outputProbeCountOnesTM_isTransducer
    (tm : TM n) (controllerTapes : ℕ)
    (addressIdx scratchIdx limitIdx countIdx : Fin controllerTapes) :
    (outputProbeCountOnesTM tm controllerTapes addressIdx scratchIdx limitIdx
      countIdx).IsTransducer :=
  IsTransducer.outputProbeCountOnesTM_internal

end TM

end Complexity
