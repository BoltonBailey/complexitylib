/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeDecodeNat.Defs
import Complexitylib.Models.TuringMachine.OutputProbeDecodeNat.Internal

/-!
# Decoding terminated-unary fields through output probes

This module exposes the first formula-code query controller used by the
uniform Barrington construction. It scans a terminated-unary field with a
bounded dynamic output probe, preserving a success/failure flag in a concrete
one-bit work register.
-/

namespace Complexity

namespace TM

/-- The bounded semantic controller agrees exactly with the existing
probe-oracle terminated-unary decoder, including unavailable positions and
fuel exhaustion. -/
theorem outputProbeDecodeNatRun_result
    (query : FormulaCode.BitOracle) (fuel cursor value : ℕ) :
    (outputProbeDecodeNatRun query fuel
      { cursor := cursor, value := value, active := true }).result? =
        FormulaCode.BitOracle.decodeNatAt? query fuel cursor value :=
  outputProbeDecodeNatRun_result_internal query fuel cursor value

/-- On a zero terminator, the concrete selected continuation clears the
active flag and advances the cursor exactly once. -/
theorem outputProbeDecodeNatZeroTM_hoareTime
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
      (clearWorkTimeBound 1 + 1 + binarySuccTime cursor) :=
  outputProbeDecodeNatZeroTM_hoareTime_internal tm controllerTapes cursorIdx
    activeIdx hdistinct outerExtras input output extras hextras houter houtput
    cursor hcursor hactive

/-- On a unary one-bit, the concrete selected continuation increments both
the accumulator and cursor exactly once. -/
theorem outputProbeDecodeNatOneTM_hoareTime
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
      (binarySuccTime value + 1 + binarySuccTime cursor) :=
  outputProbeDecodeNatOneTM_hoareTime_internal tm controllerTapes cursorIdx
    valueIdx hdistinct outerExtras input output extras hextras houter houtput
    cursor value hcursor hvalue

/-- Compose a certified dynamic source probe with the exact terminated-unary
zero/one register updates. Both branches restore the physical probe latch to
canonical zero before exposing the updated controller frame. -/
theorem outputProbeDecodeNatActiveTM_of_latch_hoareTimeSpace
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
              (clearWorkTimeBound 1 + 1 + binarySuccTime cursor))) :=
  outputProbeDecodeNatActiveTM_of_latch_hoareTimeSpace_internal tm
    controllerTapes cursorIdx scratchIdx valueIdx activeIdx hcursorValue
    hcursorActive outerExtras input output extras bit hextras houter houtput
    cursor value hcursor hvalue hactive hlatch hclearInitial hzeroInitial
    honeInitial

/-- Derive one exact active decoder step directly from a space-bounded source
transducer. Finite frame maxima and the private countdown-reset seam are chosen
internally; the caller supplies only the stable controller invariants. -/
theorem ComputesInSpace.outputProbeDecodeNatActiveTM_hoareTime
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
          bodyBound :=
  hcomp.outputProbeDecodeNatActiveTM_hoareTime_internal input cursor
    hcursorBound output houtput extras hextras hcleanupCounter cleanupLimit
    hcleanupLimit hlimit controllerTapes outerExtras houter cursorIdx
    scratchIdx valueIdx activeIdx hcursorScratch hcursorValue hcursorActive
    hcursor hscratch value hvalue hactive

/-- The complete bounded decoder preserves the append-only output discipline. -/
theorem outputProbeDecodeNatTM_isTransducer
    (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx scratchIdx valueIdx activeIdx loopIdx fuelIdx :
      Fin controllerTapes) :
    (outputProbeDecodeNatTM tm controllerTapes cursorIdx scratchIdx valueIdx
      activeIdx loopIdx fuelIdx).IsTransducer :=
  outputProbeDecodeNatTM_isTransducer_internal tm controllerTapes cursorIdx
    scratchIdx valueIdx activeIdx loopIdx fuelIdx

end TM

end Complexity
