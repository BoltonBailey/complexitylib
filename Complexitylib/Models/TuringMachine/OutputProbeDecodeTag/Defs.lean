/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.FormulaEncoding.ProbeNavigation.Defs
import Complexitylib.Models.TuringMachine.OutputProbeCountOnes.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc.Defs

/-!
# Decoding fixed formula-token tags through output probes -- definitions

Every formula token begins with one of six legal three-bit tags. This module
classifies those tags through three restartable source probes, advances a
persistent bit cursor, and retains the queried bits in three one-bit controller
registers. Variable payload decoding remains the responsibility of the bounded
terminated-unary controller.
-/

namespace Complexity

namespace TM

/-- The six legal fixed-width formula-token tags. -/
inductive OutputProbeTokenTag where
  | var
  | tru
  | fls
  | neg
  | conj
  | disj
  deriving DecidableEq, Repr

/-- Classify one three-bit formula-token tag. Tags `110` and `111` are
reserved. -/
def outputProbeTokenTag? (tag₀ tag₁ tag₂ : Bool) :
    Option OutputProbeTokenTag :=
  match tag₀, tag₁, tag₂ with
  | false, false, false => some .var
  | false, false, true => some .tru
  | false, true, false => some .fls
  | false, true, true => some .neg
  | true, false, false => some .conj
  | true, false, true => some .disj
  | true, true, _ => none

/-- Decode the fixed tag at `cursor` and return the first payload position. -/
def outputProbeDecodeTag? (query : FormulaCode.BitOracle) (cursor : ℕ) :
    Option (OutputProbeTokenTag × ℕ) := do
  let tag₀ ← query cursor
  let tag₁ ← query (cursor + 1)
  let tag₂ ← query (cursor + 2)
  let tag ← outputProbeTokenTag? tag₀ tag₁ tag₂
  some (tag, cursor + 3)

/-- Five distinct controller registers used by the fixed-width tag decoder.

The role order is cursor, query scratch, and the three retained tag bits. -/
structure OutputProbeDecodeTagLayout (controllerTapes : ℕ) where
  /-- Injective assignment of logical roles to controller tapes. -/
  roles : Fin 5 ↪ Fin controllerTapes

/-- Cursor register selected by a tag-decoder layout. -/
def OutputProbeDecodeTagLayout.cursorIdx
    (layout : OutputProbeDecodeTagLayout controllerTapes) :
    Fin controllerTapes :=
  layout.roles 0

/-- Query scratch register selected by a tag-decoder layout. -/
def OutputProbeDecodeTagLayout.scratchIdx
    (layout : OutputProbeDecodeTagLayout controllerTapes) :
    Fin controllerTapes :=
  layout.roles 1

/-- First retained tag-bit register. -/
def OutputProbeDecodeTagLayout.tag₀Idx
    (layout : OutputProbeDecodeTagLayout controllerTapes) :
    Fin controllerTapes :=
  layout.roles 2

/-- Second retained tag-bit register. -/
def OutputProbeDecodeTagLayout.tag₁Idx
    (layout : OutputProbeDecodeTagLayout controllerTapes) :
    Fin controllerTapes :=
  layout.roles 3

/-- Third retained tag-bit register. -/
def OutputProbeDecodeTagLayout.tag₂Idx
    (layout : OutputProbeDecodeTagLayout controllerTapes) :
    Fin controllerTapes :=
  layout.roles 4

/-- Physical cursor tape in the complete output-probe controller frame. -/
def outputProbeDecodeTagCursorIdx (n : ℕ) {controllerTapes : ℕ}
    (layout : OutputProbeDecodeTagLayout controllerTapes) :
    Fin (0 + outputProbeControllerTapes n + controllerTapes) :=
  outputProbeIndexedControllerIdx n layout.cursorIdx

/-- Physical retained tag-bit tape in the complete controller frame. -/
def outputProbeDecodeTagBitIdx (n : ℕ) {controllerTapes : ℕ}
    (idx : Fin controllerTapes) :
    Fin (0 + outputProbeControllerTapes n + controllerTapes) :=
  outputProbeIndexedControllerIdx n idx

/-- Canonical controller frame after retaining one queried tag bit and
advancing the source cursor. -/
def outputProbeDecodeTagBitOuterExtrasAfter (n : ℕ)
    {controllerTapes : ℕ}
    (layout : OutputProbeDecodeTagLayout controllerTapes)
    (bitIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (cursor : ℕ) (bit : Bool) :
    Fin (0 + outputProbeControllerTapes n + controllerTapes) → Tape :=
  Function.update
    (outputProbeCountOnesOuterExtrasAfter n bitIdx outerExtras 0 bit)
    (outputProbeDecodeTagCursorIdx n layout)
    (outputProbeCounterTape (cursor + 1))

/-- Query, reset the shared latch, retain one selected tag bit, and advance the
source cursor. The selected bit register must initially contain zero. -/
def outputProbeDecodeTagBitTM (tm : TM n) (controllerTapes : ℕ)
    (layout : OutputProbeDecodeTagLayout controllerTapes)
    (bitIdx : Fin controllerTapes) :
    TM (0 + outputProbeControllerTapes n + controllerTapes) :=
  seqTM
    (outputProbeCountOnesBodyTM tm controllerTapes layout.cursorIdx
      layout.scratchIdx bitIdx)
    (binarySuccTM (outputProbeDecodeTagCursorIdx n layout))

/-- Decode and retain all three fixed tag bits in source order. -/
def outputProbeDecodeTagTM (tm : TM n) (controllerTapes : ℕ)
    (layout : OutputProbeDecodeTagLayout controllerTapes) :
    TM (0 + outputProbeControllerTapes n + controllerTapes) :=
  seqTM
    (outputProbeDecodeTagBitTM tm controllerTapes layout layout.tag₀Idx)
    (seqTM
      (outputProbeDecodeTagBitTM tm controllerTapes layout layout.tag₁Idx)
      (outputProbeDecodeTagBitTM tm controllerTapes layout layout.tag₂Idx))

end TM

end Complexity
