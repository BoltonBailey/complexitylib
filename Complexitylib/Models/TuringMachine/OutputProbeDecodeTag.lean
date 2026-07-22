/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeDecodeTag.Defs
import Complexitylib.Models.TuringMachine.OutputProbeDecodeTag.Internal

/-!
# Decoding fixed formula-token tags through output probes

This module exposes the pure three-bit tag classifier and the concrete
restartable-probe machine that retains each queried bit in a distinct
controller register.
-/

namespace Complexity

namespace TM

/-- Finite-list sources instantiate the tag decoder by three ordinary optional
index operations. -/
theorem outputProbeDecodeTag?_ofList (bits : List Bool) (cursor : ℕ) :
    outputProbeDecodeTag? (FormulaCode.BitOracle.ofList bits) cursor = (do
      let tag₀ ← bits[cursor]?
      let tag₁ ← bits[cursor + 1]?
      let tag₂ ← bits[cursor + 2]?
      let tag ← outputProbeTokenTag? tag₀ tag₁ tag₂
      some (tag, cursor + 3)) :=
  outputProbeDecodeTag?_ofList_internal bits cursor

/-- Every decoded non-variable tag agrees immediately with the established
oracle token decoder. The variable case deliberately leaves its following
terminated-unary payload to `outputProbeDecodeNatTM`. -/
theorem outputProbeDecodeTag?_fixed_token
    (query : FormulaCode.BitOracle) (cursor bitFuel : ℕ)
    (tag : OutputProbeTokenTag) (nextCursor : ℕ)
    (hdecode : outputProbeDecodeTag? query cursor =
      some (tag, nextCursor)) :
    match tag with
    | .var => True
    | .tru => FormulaCode.BitOracle.decodeTokenAt? query bitFuel cursor =
        some (.tru, nextCursor)
    | .fls => FormulaCode.BitOracle.decodeTokenAt? query bitFuel cursor =
        some (.fls, nextCursor)
    | .neg => FormulaCode.BitOracle.decodeTokenAt? query bitFuel cursor =
        some (.neg, nextCursor)
    | .conj => FormulaCode.BitOracle.decodeTokenAt? query bitFuel cursor =
        some (.conj, nextCursor)
    | .disj => FormulaCode.BitOracle.decodeTokenAt? query bitFuel cursor =
        some (.disj, nextCursor) :=
  outputProbeDecodeTag?_fixed_token_internal query cursor bitFuel tag
    nextCursor hdecode

/-- Derive one exact query/reset/retain/cursor step directly from a
space-bounded source transducer. The selected bit register starts at zero and
ends at the queried Boolean value. -/
theorem ComputesInSpace.outputProbeDecodeTagBitTM_hoareTime
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
    (layout : OutputProbeDecodeTagLayout controllerTapes)
    (bitIdx : Fin controllerTapes)
    (hcursorScratch : layout.cursorIdx ≠ layout.scratchIdx)
    (hcursorBit : layout.cursorIdx ≠ bitIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (hcursor :
      (outerExtras (outputProbeDecodeTagCursorIdx n layout)).HasBinaryNat
        cursor)
    (hscratch :
      (outerExtras
        (outputProbeIndexedControllerIdx n layout.scratchIdx)).HasBinaryNat
          0)
    (hbit :
      (outerExtras (outputProbeDecodeTagBitIdx n bitIdx)).HasBinaryNat 0) :
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
      (outputProbeDecodeTagBitTM tm controllerTapes layout bitIdx).HoareTime
        pre
        (outputProbeLatchFramePost tm controllerTapes
          (outputProbeDecodeTagBitOuterExtrasAfter n layout bitIdx outerExtras
            cursor ((f input)[cursor]'hcursorBound))
          input output extras false)
        (bodyBound + 1 + binarySuccTime cursor) :=
  hcomp.outputProbeDecodeTagBitTM_hoareTime_internal input cursor
    hcursorBound output houtput extras hextras hcleanupCounter cleanupLimit
    hcleanupLimit hlimit controllerTapes layout bitIdx hcursorScratch
    hcursorBit outerExtras houter hcursor hscratch hbit

/-- Compose the three exact query/reset/retain/cursor steps into the complete
fixed-width tag probe. The final frame contains the three source bits and the
cursor advanced by exactly three positions. -/
theorem ComputesInSpace.outputProbeDecodeTagTM_hoareTime
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (input : List Bool) (cursor : ℕ)
    (hcursorBound : cursor + 2 < (f input).length)
    (output : Tape) (houtput : Parked output)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (hcleanupCounter :
      (extras (outputProbeCleanupCounterIdx n)).HasBinaryNat 0)
    (cleanupLimit : ℕ)
    (hcleanupLimit :
      (extras (outputProbeCleanupLimitIdx n)).HasBinaryNat cleanupLimit)
    (hlimit₀ : outputProbeCaptureSpace (max 1 (space input.length))
      (cursor + 1) ≤ cleanupLimit)
    (hlimit₁ : outputProbeCaptureSpace (max 1 (space input.length))
      (cursor + 2) ≤ cleanupLimit)
    (hlimit₂ : outputProbeCaptureSpace (max 1 (space input.length))
      (cursor + 3) ≤ cleanupLimit)
    (controllerTapes : ℕ)
    (layout : OutputProbeDecodeTagLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (hcursor :
      (outerExtras (outputProbeDecodeTagCursorIdx n layout)).HasBinaryNat
        cursor)
    (hscratch :
      (outerExtras
        (outputProbeIndexedControllerIdx n layout.scratchIdx)).HasBinaryNat
          0)
    (htag₀ :
      (outerExtras (outputProbeDecodeTagBitIdx n layout.tag₀Idx))
        |>.HasBinaryNat 0)
    (htag₁ :
      (outerExtras (outputProbeDecodeTagBitIdx n layout.tag₁Idx))
        |>.HasBinaryNat 0)
    (htag₂ :
      (outerExtras (outputProbeDecodeTagBitIdx n layout.tag₂Idx))
        |>.HasBinaryNat 0) :
    ∃ (bound₀ bound₁ bound₂ : ℕ)
      (pre : TapePred
        (0 + outputProbeControllerTapes n + controllerTapes)),
      pre
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).input
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).work
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).output ∧
      (outputProbeDecodeTagTM tm controllerTapes layout).HoareTime pre
        (outputProbeLatchFramePost tm controllerTapes
          (outputProbeDecodeTagOuterExtrasAfter n layout outerExtras cursor
            ((f input)[cursor]) ((f input)[cursor + 1])
            ((f input)[cursor + 2]))
          input output extras false)
        ((bound₀ + 1 + binarySuccTime cursor) + 1 +
          ((bound₁ + 1 + binarySuccTime (cursor + 1)) + 1 +
            (bound₂ + 1 + binarySuccTime (cursor + 2)))) :=
  hcomp.outputProbeDecodeTagTM_hoareTime_internal input cursor hcursorBound
    output houtput extras hextras hcleanupCounter cleanupLimit hcleanupLimit
    hlimit₀ hlimit₁ hlimit₂ controllerTapes layout outerExtras houter
    hcursor hscratch htag₀ htag₁ htag₂

/-- The complete fixed-width tag decoder preserves append-only output. -/
theorem outputProbeDecodeTagTM_isTransducer
    (tm : TM n) (controllerTapes : ℕ)
    (layout : OutputProbeDecodeTagLayout controllerTapes) :
    (outputProbeDecodeTagTM tm controllerTapes layout).IsTransducer :=
  outputProbeDecodeTagTM_isTransducer_internal tm controllerTapes layout

end TM

end Complexity
