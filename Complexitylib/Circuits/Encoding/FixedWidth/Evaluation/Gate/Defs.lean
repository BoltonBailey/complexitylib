/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Lookup.Defs
public import Complexitylib.Circuits.Encoding.FixedWidth.Validity.Defs

/-!
# Fixed-width encoded-gate evaluation formulas -- definitions

This module defines the formula-level step used to evaluate one gate slot in
a fixed-width circuit description. Its two binary references select primary
inputs or already-computed gate values, its negation bits conditionally flip
those values, and its operation bit selects AND or OR.

The source formulas are abstract. A later sequential construction instantiates
them with primary-input wires and output wires of earlier gate-step fragments.
-/


@[expose] public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace Description

namespace GateFormula

/-- Restrict an unbounded assignment to the encoded-description prefix. -/
def codeOfAssignment (inputWidth gateBound : Nat)
    (assignment : Nat → Bool) :
    BitString (codeWidth inputWidth gateBound) :=
  fun coordinate => assignment coordinate.val

/-- Decode one gate slot from the description prefix of an assignment. -/
def decodedSlot (inputWidth gateBound : Nat) (slot : Fin gateBound)
    (assignment : Nat → Bool) :
    GateSlot (referenceWidth inputWidth gateBound) :=
  GateSlot.decode <|
    slotBits (codeOfAssignment inputWidth gateBound assignment) slot

/-- Formula for the operation bit of one encoded gate slot. -/
def operationBit (inputWidth gateBound : Nat)
    (slot : Fin gateBound) : BoolFormula :=
  ValidityFormula.slotBit inputWidth gateBound slot
    ⟨0, by unfold gateSlotWidth; omega⟩

/-- Formula for the first negation bit of one encoded gate slot. -/
def negated0Bit (inputWidth gateBound : Nat)
    (slot : Fin gateBound) : BoolFormula :=
  ValidityFormula.slotBit inputWidth gateBound slot
    ⟨1, by unfold gateSlotWidth; omega⟩

/-- Formula for the second negation bit of one encoded gate slot. -/
def negated1Bit (inputWidth gateBound : Nat)
    (slot : Fin gateBound) : BoolFormula :=
  ValidityFormula.slotBit inputWidth gateBound slot
    ⟨2, by unfold gateSlotWidth; omega⟩

/-- Conditionally negate a formula value according to a Boolean flag formula. -/
def negateIf (flag value : BoolFormula) : BoolFormula :=
  .conj
    (.disj flag value)
    (.neg (.conj flag value))

/-- Apply the encoded operation convention: true selects AND and false OR. -/
def applyOperation (operation left right : BoolFormula) : BoolFormula :=
  .disj
    (.conj left right)
    (.conj (.neg operation) (.disj left right))

/-- Select the first referenced source value for one gate slot. -/
def selected0 (inputWidth gateBound : Nat) (slot : Fin gateBound)
    (sources : Fin (inputWidth + slot.val) → BoolFormula) : BoolFormula :=
  LookupFormula.select
    (ValidityFormula.input0Bit inputWidth gateBound slot) sources

/-- Select the second referenced source value for one gate slot. -/
def selected1 (inputWidth gateBound : Nat) (slot : Fin gateBound)
    (sources : Fin (inputWidth + slot.val) → BoolFormula) : BoolFormula :=
  LookupFormula.select
    (ValidityFormula.input1Bit inputWidth gateBound slot) sources

/-- Evaluate one encoded gate from an abstract family of available sources. -/
def gate (inputWidth gateBound : Nat) (slot : Fin gateBound)
    (sources : Fin (inputWidth + slot.val) → BoolFormula) : BoolFormula :=
  let value0 := negateIf (negated0Bit inputWidth gateBound slot)
    (selected0 inputWidth gateBound slot sources)
  let value1 := negateIf (negated1Bit inputWidth gateBound slot)
    (selected1 inputWidth gateBound slot sources)
  applyOperation (operationBit inputWidth gateBound slot) value0 value1

/-- Exact tree size of one encoded-gate formula when every source is a
one-node variable formula. -/
def gateSize (inputWidth gateBound : Nat) (slot : Fin gateBound) : Nat :=
  8 * LookupFormula.selectSize
    (referenceWidth inputWidth gateBound) (inputWidth + slot.val) + 30

end GateFormula

end Description

end FixedWidth

end CircuitCode

end Complexity
