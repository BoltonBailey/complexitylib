/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth

/-!
# Conversion between raw circuits and fixed-width descriptions -- definitions

This module encodes each bounded topologically ordered raw circuit into the
fixed gate-slot representation. Active slots contain fixed-width little-endian
references and all inactive slots are zero. The inverse direction is the
`Description.toRawCircuit` operation from the core fixed-width layer.
-/


@[expose] public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace GateSlot

/-- A natural number truncated to one fixed-width little-endian reference
word. -/
def referenceBits (width value : Nat) : BitString width :=
  BitString.ofList (Nat.toBitsLE width value)
    (Nat.length_toBitsLE width value)

/-- Encode one raw gate into a fixed-width slot. References outside the word
range are truncated; bounded well-formed circuits never take that path. -/
def ofRawGate (width : Nat) (gate : RawGate) : GateSlot width where
  op := gate.opBit
  negated0 := gate.negated₀
  negated1 := gate.negated₁
  input0 := referenceBits width gate.input₀
  input1 := referenceBits width gate.input₁

end GateSlot

namespace Description

/-- Canonical fixed-slot description of a raw circuit within `gateBound`.
Slots after the circuit's final gate are all zero. -/
def ofRawCircuit {inputWidth gateBound : Nat} (circuit : RawCircuit)
    (hbound : circuit.length ≤ gateBound) :
    Description inputWidth gateBound where
  gateCount := ⟨circuit.length, by omega⟩
  slots := fun index =>
    if hindex : index.val < circuit.length then
      GateSlot.ofRawGate (referenceWidth inputWidth gateBound)
        circuit[index.val]
    else
      GateSlot.zero _

end Description

/-- Valid fixed-width descriptions at one arity and gate bound. -/
def ValidDescription (inputWidth gateBound : Nat) :=
  { description : Description inputWidth gateBound // description.WellFormed }

noncomputable instance (inputWidth gateBound : Nat) :
    Fintype (ValidDescription inputWidth gateBound) :=
  inferInstanceAs (Fintype
    { description : Description inputWidth gateBound // description.WellFormed })

instance (inputWidth gateBound : Nat) :
    DecidableEq (ValidDescription inputWidth gateBound) :=
  inferInstanceAs (DecidableEq
    { description : Description inputWidth gateBound // description.WellFormed })

/-- Nonempty topologically ordered raw circuits within one gate bound. -/
def BoundedRawCircuit (inputWidth gateBound : Nat) :=
  { circuit : RawCircuit //
    circuit.WellFormed inputWidth ∧ circuit.length ≤ gateBound }

instance (inputWidth gateBound : Nat) :
    DecidableEq (BoundedRawCircuit inputWidth gateBound) :=
  inferInstanceAs (DecidableEq
    { circuit : RawCircuit //
      circuit.WellFormed inputWidth ∧ circuit.length ≤ gateBound })

end FixedWidth

end CircuitCode

end Complexity
