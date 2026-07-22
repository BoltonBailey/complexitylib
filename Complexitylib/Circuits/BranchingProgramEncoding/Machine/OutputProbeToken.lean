/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.OutputProbeToken.Defs
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.OutputProbeToken.Internal

/-!
# Barrington leaf emission after output-probe token decoding

This module exposes the concrete variable-token continuation: it decodes the
terminated-unary payload, preserves the restartable query frame, and appends
the exact canonical Barrington variable instruction.
-/

namespace Complexity

namespace BPCode

namespace Machine

open TM

/-- Decode a variable payload from the normalized post-tag frame and append
the resulting canonical Barrington instruction. -/
theorem outputProbeDecodeVarInstrTM_hoareTime
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (input : List Bool) (output : Tape) (ys : List Bool)
    (houtput : OutAcc ys output)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (hcleanupCounter :
      (extras (outputProbeCleanupCounterIdx n)).HasBinaryNat 0)
    (cleanupLimit : ℕ)
    (hcleanupLimit :
      (extras (outputProbeCleanupLimitIdx n)).HasBinaryNat cleanupLimit)
    (controllerTapes : ℕ)
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (cursor : ℕ) (tag₀ tag₁ tag₂ : Bool)
    (hscratch :
      (outerExtras
        (outputProbeIndexedControllerIdx n layout.natLayout.scratchIdx))
        |>.HasBinaryNat 0)
    (htag₀Zero :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₀Idx))
        |>.HasBinaryNat 0)
    (htag₁Zero :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₁Idx))
        |>.HasBinaryNat 0)
    (htag₂Zero :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₂Idx))
        |>.HasBinaryNat 0)
    (hvalue :
      (outerExtras
        (outputProbeIndexedControllerIdx n layout.natLayout.valueIdx))
        |>.HasBinaryNat 0)
    (hactive :
      (outerExtras
        (outputProbeIndexedControllerIdx n layout.natLayout.activeIdx))
        |>.HasBinaryNat 1)
    (hloop :
      (outerExtras
        (outputProbeIndexedControllerIdx n layout.natLayout.loopIdx))
        |>.HasBinaryNat 0)
    (fuelValue : ℕ)
    (hfuel :
      (outerExtras
        (outputProbeIndexedControllerIdx n layout.natLayout.fuelIdx))
        |>.HasBinaryNat fuelValue)
    (hqueryValid : ∀ value, value < fuelValue →
      (outputProbeDecodeNatStateAt (f input)
        (outputProbeDecodeTokenVarInitial cursor) value).active = true →
      (outputProbeDecodeNatStateAt (f input)
        (outputProbeDecodeTokenVarInitial cursor) value).cursor <
          (f input).length)
    (hqueryLimit : ∀ value, value < fuelValue →
      (outputProbeDecodeNatStateAt (f input)
        (outputProbeDecodeTokenVarInitial cursor) value).active = true →
      outputProbeCaptureSpace (max 1 (space input.length))
        ((outputProbeDecodeNatStateAt (f input)
          (outputProbeDecodeTokenVarInitial cursor) value).cursor + 1) ≤
            cleanupLimit)
    (target : Equiv.Perm (Fin 5)) :
    let finalState := outputProbeDecodeNatStateAt (f input)
      (outputProbeDecodeTokenVarInitial cursor) fuelValue
    let finalOuter := outputProbeDecodeNatLoopOuterExtras n
      layout.natLayout.cursorIdx layout.natLayout.valueIdx
      layout.natLayout.activeIdx layout.natLayout.loopIdx
      (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor
        tag₀ tag₁ tag₂)
      finalState fuelValue
    ∃ bodyTime : ℕ → ℕ,
      (outputProbeDecodeVarInstrTM tm controllerTapes layout target).HoareTime
        (outputProbeLatchFramePost tm controllerTapes
          (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor
            tag₀ tag₁ tag₂)
          input output extras false)
        (EmitPred
          (outputProbeLatchFrameCfg tm controllerTapes finalOuter input output
            extras false).input
          (outputProbeLatchFrameCfg tm controllerTapes finalOuter input output
            extras false).work
          (ys ++ Instr.encode ⟨finalState.value, 1, target⟩))
        (outputProbeDecodeVarInstrTime bodyTime fuelValue finalState.value) :=
  outputProbeDecodeVarInstrTM_hoareTime_internal hcomp input output ys
    houtput extras hextras hcleanupCounter cleanupLimit hcleanupLimit
    controllerTapes layout outerExtras houter cursor tag₀ tag₁ tag₂ hscratch
    htag₀Zero htag₁Zero htag₂Zero hvalue hactive hloop fuelValue hfuel
    hqueryValid hqueryLimit target

end Machine

end BPCode

end Complexity
