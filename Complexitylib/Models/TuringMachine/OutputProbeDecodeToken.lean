/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeDecodeToken.Defs
import Complexitylib.Models.TuringMachine.OutputProbeDecodeToken.Internal

/-!
# Shared formula-token decoder layout

This module exposes the structural bridge between fixed-width tag probing and
terminated-unary variable decoding. Both controllers use the same cursor and
query scratch, while every retained tag and unary-loop register stays distinct.
-/

namespace Complexity

namespace TM

/-- Fixed-tag and terminated-unary decoding share one source cursor. -/
@[simp]
theorem OutputProbeDecodeTokenLayout.tagLayout_cursorIdx
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.tagLayout.cursorIdx = layout.natLayout.cursorIdx :=
  layout.tagLayout_cursorIdx_internal

/-- Fixed-tag and terminated-unary decoding share one query scratch register. -/
@[simp]
theorem OutputProbeDecodeTokenLayout.tagLayout_scratchIdx
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.tagLayout.scratchIdx = layout.natLayout.scratchIdx :=
  layout.tagLayout_scratchIdx_internal

/-- The first retained tag bit occupies complete-layout role two. -/
@[simp]
theorem OutputProbeDecodeTokenLayout.tagLayout_tag₀Idx
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.tagLayout.tag₀Idx = layout.roles 2 :=
  layout.tagLayout_tag₀Idx_internal

/-- The second retained tag bit occupies complete-layout role three. -/
@[simp]
theorem OutputProbeDecodeTokenLayout.tagLayout_tag₁Idx
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.tagLayout.tag₁Idx = layout.roles 3 :=
  layout.tagLayout_tag₁Idx_internal

/-- The third retained tag bit occupies complete-layout role four. -/
@[simp]
theorem OutputProbeDecodeTokenLayout.tagLayout_tag₂Idx
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.tagLayout.tag₂Idx = layout.roles 4 :=
  layout.tagLayout_tag₂Idx_internal

/-- The unary accumulator occupies complete-layout role five. -/
@[simp]
theorem OutputProbeDecodeTokenLayout.natLayout_valueIdx
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.natLayout.valueIdx = layout.roles 5 :=
  layout.natLayout_valueIdx_internal

/-- The unary active flag occupies complete-layout role six. -/
@[simp]
theorem OutputProbeDecodeTokenLayout.natLayout_activeIdx
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.natLayout.activeIdx = layout.roles 6 :=
  layout.natLayout_activeIdx_internal

/-- The unary loop counter occupies complete-layout role seven. -/
@[simp]
theorem OutputProbeDecodeTokenLayout.natLayout_loopIdx
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.natLayout.loopIdx = layout.roles 7 :=
  layout.natLayout_loopIdx_internal

/-- The preserved unary fuel occupies complete-layout role eight. -/
@[simp]
theorem OutputProbeDecodeTokenLayout.natLayout_fuelIdx
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.natLayout.fuelIdx = layout.roles 8 :=
  layout.natLayout_fuelIdx_internal

/-- Clearing retained tags preserves every other physical controller tape. -/
theorem outputProbeDecodeTokenClearedTagExtras_eq_of_ne
    (n : ℕ) {controllerTapes : ℕ}
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (idx : Fin (0 + outputProbeControllerTapes n + controllerTapes))
    (htag₀ : idx ≠
      outputProbeDecodeTagBitIdx n layout.tagLayout.tag₀Idx)
    (htag₁ : idx ≠
      outputProbeDecodeTagBitIdx n layout.tagLayout.tag₁Idx)
    (htag₂ : idx ≠
      outputProbeDecodeTagBitIdx n layout.tagLayout.tag₂Idx) :
    outputProbeDecodeTokenClearedTagExtras n layout outerExtras idx =
      outerExtras idx :=
  outputProbeDecodeTokenClearedTagExtras_eq_of_ne_internal n layout
    outerExtras idx htag₀ htag₁ htag₂

/-- Clearing retained tags restores the first tag register to canonical zero. -/
theorem outputProbeDecodeTokenClearedTagExtras_tag₀
    (n : ℕ) {controllerTapes : ℕ}
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape) :
    (outputProbeDecodeTokenClearedTagExtras n layout outerExtras
      (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₀Idx)).HasBinaryNat
        0 :=
  outputProbeDecodeTokenClearedTagExtras_tag₀_internal n layout outerExtras

/-- Clearing retained tags restores the second tag register to canonical zero. -/
theorem outputProbeDecodeTokenClearedTagExtras_tag₁
    (n : ℕ) {controllerTapes : ℕ}
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape) :
    (outputProbeDecodeTokenClearedTagExtras n layout outerExtras
      (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₁Idx)).HasBinaryNat
        0 :=
  outputProbeDecodeTokenClearedTagExtras_tag₁_internal n layout outerExtras

/-- Clearing retained tags restores the third tag register to canonical zero. -/
theorem outputProbeDecodeTokenClearedTagExtras_tag₂
    (n : ℕ) {controllerTapes : ℕ}
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape) :
    (outputProbeDecodeTokenClearedTagExtras n layout outerExtras
      (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₂Idx)).HasBinaryNat
        0 :=
  outputProbeDecodeTokenClearedTagExtras_tag₂_internal n layout outerExtras

/-- Clear all three retained tag registers from a literal restored probe
frame, preserving every other tape and exposing the exact cleanup time. -/
theorem outputProbeDecodeTokenClearTagsTM_hoareTime
    (tm : TM n) (controllerTapes : ℕ)
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (tag₀ tag₁ tag₂ : Bool)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (htag₀ :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₀Idx))
        |>.HasBinaryNat (if tag₀ then 1 else 0))
    (htag₁ :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₁Idx))
        |>.HasBinaryNat (if tag₁ then 1 else 0))
    (htag₂ :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₂Idx))
        |>.HasBinaryNat (if tag₂ then 1 else 0)) :
    (outputProbeDecodeTokenClearTagsTM n controllerTapes layout).HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTokenClearedTagExtras n layout outerExtras)
        input output extras false)
      (outputProbeDecodeTokenClearTagsTime tag₀ tag₁ tag₂) :=
  outputProbeDecodeTokenClearTagsTM_hoareTime_internal tm controllerTapes
    layout outerExtras input output extras tag₀ tag₁ tag₂ hextras houter
    houtput htag₀ htag₁ htag₂

/-- Retained-tag cleanup preserves the append-only output discipline. -/
theorem outputProbeDecodeTokenClearTagsTM_isTransducer
    (n controllerTapes : ℕ)
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    (outputProbeDecodeTokenClearTagsTM n controllerTapes
      layout).IsTransducer :=
  outputProbeDecodeTokenClearTagsTM_isTransducer_internal n controllerTapes
    layout

end TM

end Complexity
