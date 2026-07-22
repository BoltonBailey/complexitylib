/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.FormulaEncoding.ProbeNavigation.Defs
import Complexitylib.Models.TuringMachine.OutputProbeDispatch.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor.Defs

/-!
# Decoding terminated-unary fields through output probes -- definitions

Formula headers and variable tokens encode natural numbers as a run of one
bits followed by a zero terminator. This module gives that scan a concrete
restartable-probe controller. A persistent `active` register records whether
the terminator is still owed; after it becomes zero, the remaining bounded
iterations are no-ops.
-/

namespace Complexity

namespace TM

/-- Pure controller state for a bounded terminated-unary probe scan. -/
structure OutputProbeDecodeNatState where
  /-- Current zero-based source-output position. -/
  cursor : ℕ
  /-- Accumulated unary value. -/
  value : ℕ
  /-- Whether the scan is still waiting for a zero terminator. -/
  active : Bool
  deriving DecidableEq

/-- One semantic decoder iteration against a position-indexed bit oracle.

An unavailable position leaves the decoder active, hence makes the final
bounded result fail. A zero bit consumes the terminator and clears `active`;
a one bit advances both cursor and accumulator. -/
def outputProbeDecodeNatStep (query : FormulaCode.BitOracle)
    (state : OutputProbeDecodeNatState) : OutputProbeDecodeNatState :=
  if state.active then
    match query state.cursor with
    | none => state
    | some bit =>
        { cursor := state.cursor + 1
          value := state.value + if bit then 1 else 0
          active := bit }
  else
    state

/-- Run exactly `fuel` semantic decoder iterations. -/
def outputProbeDecodeNatRun (query : FormulaCode.BitOracle) :
    ℕ → OutputProbeDecodeNatState → OutputProbeDecodeNatState
  | 0, state => state
  | fuel + 1, state =>
      outputProbeDecodeNatRun query fuel
        (outputProbeDecodeNatStep query state)

/-- Read a successful value/cursor pair from a completed decoder state. -/
def OutputProbeDecodeNatState.result?
    (state : OutputProbeDecodeNatState) : Option (ℕ × ℕ) :=
  if state.active then none else some (state.value, state.cursor)

/-- Physical controller tape holding the cursor. -/
def outputProbeDecodeNatCursorIdx (n : ℕ) {controllerTapes : ℕ}
    (cursorIdx : Fin controllerTapes) :
    Fin (0 + outputProbeControllerTapes n + controllerTapes) :=
  outputProbeIndexedControllerIdx n cursorIdx

/-- Physical controller tape holding the unary accumulator. -/
def outputProbeDecodeNatValueIdx (n : ℕ) {controllerTapes : ℕ}
    (valueIdx : Fin controllerTapes) :
    Fin (0 + outputProbeControllerTapes n + controllerTapes) :=
  outputProbeIndexedControllerIdx n valueIdx

/-- Physical one-bit register recording whether the terminator is still owed. -/
def outputProbeDecodeNatActiveIdx (n : ℕ) {controllerTapes : ℕ}
    (activeIdx : Fin controllerTapes) :
    Fin (0 + outputProbeControllerTapes n + controllerTapes) :=
  outputProbeIndexedControllerIdx n activeIdx

/-- Stable controller frame after consuming a zero terminator. -/
def outputProbeDecodeNatZeroOuterExtras (n : ℕ)
    {controllerTapes : ℕ} (cursorIdx activeIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (cursor : ℕ) :
    Fin (0 + outputProbeControllerTapes n + controllerTapes) → Tape :=
  Function.update
    (Function.update outerExtras
      (outputProbeDecodeNatActiveIdx n activeIdx)
      (outputProbeCounterTape 0))
    (outputProbeDecodeNatCursorIdx n cursorIdx)
    (outputProbeCounterTape (cursor + 1))

/-- Stable controller frame after consuming one unary one-bit. -/
def outputProbeDecodeNatOneOuterExtras (n : ℕ)
    {controllerTapes : ℕ} (cursorIdx valueIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (cursor value : ℕ) :
    Fin (0 + outputProbeControllerTapes n + controllerTapes) → Tape :=
  Function.update
    (Function.update outerExtras
      (outputProbeDecodeNatValueIdx n valueIdx)
      (outputProbeCounterTape (value + 1)))
    (outputProbeDecodeNatCursorIdx n cursorIdx)
    (outputProbeCounterTape (cursor + 1))

/-- Stable controller frame after consuming the selected decoder bit. -/
def outputProbeDecodeNatOuterExtrasAfter (n : ℕ)
    {controllerTapes : ℕ}
    (cursorIdx valueIdx activeIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (cursor value : ℕ) (bit : Bool) :
    Fin (0 + outputProbeControllerTapes n + controllerTapes) → Tape :=
  if bit then
    outputProbeDecodeNatOneOuterExtras n cursorIdx valueIdx outerExtras
      cursor value
  else
    outputProbeDecodeNatZeroOuterExtras n cursorIdx activeIdx outerExtras
      cursor

/-- Consume a zero terminator: clear `active`, then advance the cursor. -/
def outputProbeDecodeNatZeroTM (n controllerTapes : ℕ)
    (cursorIdx activeIdx : Fin controllerTapes) :
    TM (0 + outputProbeControllerTapes n + controllerTapes) :=
  seqTM
    (clearWorkTM (outputProbeDecodeNatActiveIdx n activeIdx))
    (binarySuccTM (outputProbeDecodeNatCursorIdx n cursorIdx))

/-- Consume a unary one: increment the value, then advance the cursor. -/
def outputProbeDecodeNatOneTM (n controllerTapes : ℕ)
    (cursorIdx valueIdx : Fin controllerTapes) :
    TM (0 + outputProbeControllerTapes n + controllerTapes) :=
  seqTM
    (binarySuccTM (outputProbeDecodeNatValueIdx n valueIdx))
    (binarySuccTM (outputProbeDecodeNatCursorIdx n cursorIdx))

/-- Query and consume one bit while the decoder is active. -/
def outputProbeDecodeNatActiveTM (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx scratchIdx valueIdx activeIdx : Fin controllerTapes) :
    TM (0 + outputProbeControllerTapes n + controllerTapes) :=
  outputProbeIndexedResetDispatchTM tm controllerTapes cursorIdx scratchIdx
    (outputProbeDecodeNatZeroTM n controllerTapes cursorIdx activeIdx)
    (outputProbeDecodeNatOneTM n controllerTapes cursorIdx valueIdx)

/-- One bounded decoder body iteration.

The active branch consumes one probed source bit. The inactive branch is a
literal no-op, so a found terminator freezes the decoded value and cursor for
the rest of the public fuel loop. -/
def outputProbeDecodeNatBodyTM (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx scratchIdx valueIdx activeIdx : Fin controllerTapes) :
    TM (0 + outputProbeControllerTapes n + controllerTapes) :=
  branchWorkSymbolTM (outputProbeDecodeNatActiveIdx n activeIdx) Γ.one
    (outputProbeDecodeNatActiveTM tm controllerTapes cursorIdx scratchIdx
      valueIdx activeIdx)
    skipTM

/-- Decode one terminated-unary field using at most the fuel stored in a
preserved limit register.

The caller initializes `loopIdx` to zero, `fuelIdx` to the desired fuel,
`activeIdx` to one, and the cursor/value registers to their initial values.
On success `activeIdx` is zero; if fuel is exhausted first it remains one. -/
def outputProbeDecodeNatTM (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx scratchIdx valueIdx activeIdx loopIdx fuelIdx :
      Fin controllerTapes) :
    TM (0 + outputProbeControllerTapes n + controllerTapes) :=
  binaryForTM
    (outputProbeDecodeNatBodyTM tm controllerTapes cursorIdx scratchIdx
      valueIdx activeIdx)
    (outputProbeIndexedControllerIdx n loopIdx)
    (outputProbeIndexedControllerIdx n fuelIdx)

end TM

end Complexity
