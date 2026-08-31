/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.BinaryComparison.Defs
public import Complexitylib.Circuits.Encoding.FixedWidth.Codec.Defs
public import Complexitylib.Circuits.Encoding.Formula.Batch.Defs

/-!
# Fixed-width description validity formulas -- definitions

This module defines a Boolean formula for structural validity of one bounded
fixed-width circuit description. Formula variables address the codec through
typed count and slot coordinates, avoiding an auxiliary parser or arithmetic
casts between unrelated fields.

The formula checks that the active count is positive and in range. For every
gate slot it then checks one of two cases: active slots have backward-pointing
references, while inactive slots are the canonical all-zero slot.
-/


@[expose] public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace Description

/-- A code is structurally valid when decoding succeeds and the resulting
fixed-width description satisfies all three validity conditions. -/
def EncodedWellFormed {inputWidth gateBound : Nat}
    (code : BitString (codeWidth inputWidth gateBound)) : Prop :=
  match decode? code with
  | none => False
  | some description => description.WellFormed

instance {inputWidth gateBound : Nat}
    (code : BitString (codeWidth inputWidth gateBound)) :
    Decidable (EncodedWellFormed code) := by
  unfold EncodedWellFormed
  split <;> infer_instance

namespace ValidityFormula

/-- Embed one count-field coordinate into the full description code. -/
def countCoordinate (inputWidth gateBound : Nat)
    (coordinate : Fin (gateCountWidth gateBound)) :
    Fin (codeWidth inputWidth gateBound) :=
  Fin.castAdd (gateBound * gateSlotWidth inputWidth gateBound) coordinate

/-- Embed one coordinate of one gate slot into the full description code. -/
def slotCoordinate (inputWidth gateBound : Nat)
    (slot : Fin gateBound)
    (coordinate : Fin (gateSlotWidth inputWidth gateBound)) :
    Fin (codeWidth inputWidth gateBound) :=
  Fin.natAdd (gateCountWidth gateBound)
    (finProdFinEquiv (slot, coordinate))

/-- Coordinate of a first-reference bit inside one gate slot. -/
def input0Coordinate (inputWidth gateBound : Nat)
    (coordinate : Fin (referenceWidth inputWidth gateBound)) :
    Fin (gateSlotWidth inputWidth gateBound) :=
  Fin.natAdd 3
    (Fin.castAdd (referenceWidth inputWidth gateBound) coordinate)

/-- Coordinate of a second-reference bit inside one gate slot. -/
def input1Coordinate (inputWidth gateBound : Nat)
    (coordinate : Fin (referenceWidth inputWidth gateBound)) :
    Fin (gateSlotWidth inputWidth gateBound) :=
  Fin.natAdd 3
    (Fin.natAdd (referenceWidth inputWidth gateBound) coordinate)

/-- Variable formula for one count-field bit. -/
def countBit (inputWidth gateBound : Nat)
    (coordinate : Fin (gateCountWidth gateBound)) : BoolFormula :=
  .var (countCoordinate inputWidth gateBound coordinate).val

/-- Variable formula for one bit of one encoded gate slot. -/
def slotBit (inputWidth gateBound : Nat) (slot : Fin gateBound)
    (coordinate : Fin (gateSlotWidth inputWidth gateBound)) : BoolFormula :=
  .var (slotCoordinate inputWidth gateBound slot coordinate).val

/-- Variable formula for one first-reference bit. -/
def input0Bit (inputWidth gateBound : Nat) (slot : Fin gateBound)
    (coordinate : Fin (referenceWidth inputWidth gateBound)) : BoolFormula :=
  slotBit inputWidth gateBound slot
    (input0Coordinate inputWidth gateBound coordinate)

/-- Variable formula for one second-reference bit. -/
def input1Bit (inputWidth gateBound : Nat) (slot : Fin gateBound)
    (coordinate : Fin (referenceWidth inputWidth gateBound)) : BoolFormula :=
  slotBit inputWidth gateBound slot
    (input1Coordinate inputWidth gateBound coordinate)

/-- Formula asserting that the encoded active count is at least `minimum`. -/
def countAtLeast (inputWidth gateBound minimum : Nat) : BoolFormula :=
  BoolFormula.unsignedLEOf
    (fun coordinate => BoolFormula.ofBool
      (GateSlot.referenceBits (gateCountWidth gateBound) minimum coordinate))
    (countBit inputWidth gateBound)

/-- Formula asserting that the encoded active count is at most `maximum`. -/
def countAtMost (inputWidth gateBound maximum : Nat) : BoolFormula :=
  BoolFormula.unsignedLEOf
    (countBit inputWidth gateBound)
    (fun coordinate => BoolFormula.ofBool
      (GateSlot.referenceBits (gateCountWidth gateBound) maximum coordinate))

/-- Formula asserting that one encoded reference is below the number of wires
available before its gate. -/
def referenceBelow (inputWidth gateBound : Nat) (slot : Fin gateBound)
    (first : Bool) (available : Nat) : BoolFormula :=
  let bits := if first then
      input0Bit inputWidth gateBound slot
    else
      input1Bit inputWidth gateBound slot
  .neg <| BoolFormula.unsignedLEOf
    (fun coordinate => BoolFormula.ofBool
      (GateSlot.referenceBits
        (referenceWidth inputWidth gateBound) available coordinate))
    bits

/-- Formula asserting that one complete inactive slot is the all-zero word. -/
def slotZero (inputWidth gateBound : Nat)
    (slot : Fin gateBound) : BoolFormula :=
  BoolFormula.unsignedLEOf
    (slotBit inputWidth gateBound slot)
    (fun _ => .fls)

/-- Formula asserting that both references of one active slot point backward. -/
def slotWellFormed (inputWidth gateBound : Nat)
    (slot : Fin gateBound) : BoolFormula :=
  .conj
    (referenceBelow inputWidth gateBound slot true
      (inputWidth + slot.val))
    (referenceBelow inputWidth gateBound slot false
      (inputWidth + slot.val))

/-- Formula asserting the active or inactive invariant for one fixed slot. -/
def slotValid (inputWidth gateBound : Nat)
    (slot : Fin gateBound) : BoolFormula :=
  let active := countAtLeast inputWidth gateBound (slot.val + 1)
  .conj
    (.disj (.neg active) (slotWellFormed inputWidth gateBound slot))
    (.disj active (slotZero inputWidth gateBound slot))

/-- Exact tree size of one slot-validity formula. -/
def slotValidSize (inputWidth gateBound : Nat) : Nat :=
  30 * gateCountWidth gateBound +
    30 * referenceWidth inputWidth gateBound +
    15 * gateSlotWidth inputWidth gateBound + 12

/-- Exact tree size of the complete description-validity formula. -/
def wellFormedSize (inputWidth gateBound : Nat) : Nat :=
  30 * gateCountWidth gateBound + 5 +
    gateBound * (slotValidSize inputWidth gateBound + 1)

/-- Complete structural-validity formula for one fixed-width description code. -/
def wellFormed (inputWidth gateBound : Nat) : BoolFormula :=
  .conj
    (countAtLeast inputWidth gateBound 1)
    (.conj
      (countAtMost inputWidth gateBound gateBound)
      (BoolFormula.conjs <| List.ofFn fun slot : Fin gateBound =>
        slotValid inputWidth gateBound slot))

end ValidityFormula

end Description

end FixedWidth

end CircuitCode

end Complexity
