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
