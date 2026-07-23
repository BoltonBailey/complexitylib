/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.ForwardScanToken.Defs
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.ForwardScanToken.Internal

/-!
# Token decoding for the forward postfix scan

This module exposes the combined token-decoder and numeric-scan register
layout, the variable-decoder normalization contract, and append-only safety of
the assembled one-token controller.
-/

namespace Complexity

namespace BPCode

namespace Machine

open TM

/-- The complete decoder and numeric scan use the same physical source cursor. -/
@[simp]
theorem ForwardScanTokenLayout.scanLayout_cursorIdx
    (layout : ForwardScanTokenLayout controllerTapes) :
    (layout.scanLayout n).cursorIdx =
      outputProbeIndexedControllerIdx n
        layout.tokenLayout.natLayout.cursorIdx := by
  simpa using layout.scanLayout_cursorIdx_internal (n := n)

/-- Normalizing the private variable-decoder registers preserves every numeric
forward-scan register literally. -/
theorem ForwardScanFrame.forwardScanVarResetWork
    (layout : ForwardScanTokenLayout controllerTapes)
    (cursor height tokenCount lastOneCount lastOneCursor : ℕ)
    (work : Fin (0 + outputProbeControllerTapes n + controllerTapes) →
      Tape)
    (hframe : ForwardScanFrame (layout.scanLayout n) cursor height tokenCount
      lastOneCount lastOneCursor work) :
    ForwardScanFrame (layout.scanLayout n) cursor height tokenCount
      lastOneCount lastOneCursor (forwardScanVarResetWork n layout work) :=
  hframe.forwardScanVarResetWork_internal layout cursor height tokenCount
    lastOneCount lastOneCursor work

/-- Normalize the value, active, and loop registers left by completed variable
decoding, preserving every other tape literally. -/
theorem forwardScanVarResetTM_hoareTime (n controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes)
    (value fuel : ℕ)
    (inp₀ : Tape)
    (work₀ : Fin (0 + outputProbeControllerTapes n + controllerTapes) →
      Tape)
    (out₀ : Tape)
    (hvalue :
      (work₀ (outputProbeIndexedControllerIdx n
        layout.tokenLayout.natLayout.valueIdx)).HasBinaryNat value)
    (hactive :
      (work₀ (outputProbeIndexedControllerIdx n
        layout.tokenLayout.natLayout.activeIdx)).HasBinaryNat 0)
    (hloop :
      (work₀ (outputProbeIndexedControllerIdx n
        layout.tokenLayout.natLayout.loopIdx)).HasBinaryNat fuel)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) :
    (forwardScanVarResetTM n controllerTapes layout).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = forwardScanVarResetWork n layout work₀ ∧
        out = out₀)
      (forwardScanVarResetTime value fuel) :=
  forwardScanVarResetTM_hoareTime_internal n controllerTapes layout value
    fuel inp₀ work₀ out₀ hvalue hactive hloop hinput hwork houtput

/-- Variable-decoder normalization is append-only. -/
theorem forwardScanVarResetTM_isTransducer (n controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes) :
    (forwardScanVarResetTM n controllerTapes layout).IsTransducer :=
  forwardScanVarResetTM_isTransducer_internal n controllerTapes layout

/-- Variable decoding, normalization, and its leaf scan update are append-only. -/
theorem forwardScanVarTokenStepTM_isTransducer (tm : TM n)
    (controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes) :
    (forwardScanVarTokenStepTM tm controllerTapes layout).IsTransducer :=
  forwardScanVarTokenStepTM_isTransducer_internal tm controllerTapes layout

/-- One complete decoded forward-scan token step is append-only. -/
theorem forwardScanDecodedTokenTM_isTransducer (tm : TM n)
    (controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes) :
    (forwardScanDecodedTokenTM tm controllerTapes layout).IsTransducer :=
  forwardScanDecodedTokenTM_isTransducer_internal tm controllerTapes layout

end Machine

end BPCode

end Complexity
