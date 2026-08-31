/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Conversion.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Fixed-width binary circuit-description codec -- definitions

This module flattens bounded gate-slot descriptions into one Boolean cube.
Gate slots have a total fixed-width codec. Description decoding is partial
only because the count word can represent values above `gateBound`.
-/


@[expose] public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace GateSlot

/-- Flatten one gate slot into its three control bits followed by its two
little-endian reference words. -/
def encode {width : Nat} (slot : GateSlot width) :
    BitString (3 + (width + width)) :=
  Fin.append ![slot.op, slot.negated0, slot.negated1]
    (Fin.append slot.input0 slot.input1)

/-- Split one fixed-width gate-slot word into its structural fields. -/
def decode {width : Nat} (bits : BitString (3 + (width + width))) :
    GateSlot width :=
  let blocks := (Fin.appendEquiv 3 (width + width)).symm bits
  let inputs := (Fin.appendEquiv width width).symm blocks.2
  { op := blocks.1 0
    negated0 := blocks.1 1
    negated1 := blocks.1 2
    input0 := inputs.1
    input1 := inputs.2 }

end GateSlot

namespace Description

/-- Flatten a bounded description into its count word followed by all gate
slots in row-major order. -/
def encode {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) :
    BitString (codeWidth inputWidth gateBound) :=
  Fin.append
    (GateSlot.referenceBits (gateCountWidth gateBound)
      description.gateCountNat)
    (fun coordinate =>
      let position := finProdFinEquiv.symm coordinate
      GateSlot.encode (description.slots position.1) position.2)

/-- Extract the leading fixed-width gate-count word. -/
def countBits {inputWidth gateBound : Nat}
    (code : BitString (codeWidth inputWidth gateBound)) :
    BitString (gateCountWidth gateBound) :=
  ((Fin.appendEquiv (gateCountWidth gateBound)
    (gateBound * gateSlotWidth inputWidth gateBound)).symm code).1

/-- Extract one fixed-width gate slot from a flattened description. -/
def slotBits {inputWidth gateBound : Nat}
    (code : BitString (codeWidth inputWidth gateBound))
    (slot : Fin gateBound) :
    BitString (gateSlotWidth inputWidth gateBound) :=
  fun coordinate =>
    ((Fin.appendEquiv (gateCountWidth gateBound)
      (gateBound * gateSlotWidth inputWidth gateBound)).symm code).2
        (finProdFinEquiv (slot, coordinate))

/-- Natural value represented by the leading little-endian count word. -/
def countValue {inputWidth gateBound : Nat}
    (code : BitString (codeWidth inputWidth gateBound)) : Nat :=
  Nat.fromBitsLE (countBits code).toList

/-- Decode one flattened description, rejecting exactly the out-of-range
gate-count words. -/
def decode? {inputWidth gateBound : Nat}
    (code : BitString (codeWidth inputWidth gateBound)) :
    Option (Description inputWidth gateBound) :=
  if hcount : countValue code < gateBound + 1 then
    some
      { gateCount := ⟨countValue code, hcount⟩
        slots := fun slot => GateSlot.decode (slotBits code slot) }
  else
    none

end Description

end FixedWidth

end CircuitCode

end Complexity
