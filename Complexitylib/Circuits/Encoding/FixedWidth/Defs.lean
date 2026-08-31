/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Defs
public import Complexitylib.Circuits.BitString
public import Complexitylib.Mathlib.NatBits
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod

/-!
# Fixed-width binary circuit descriptions -- definitions

This module gives fan-in-two raw circuits an Algebraic-style gate-slot view.
Every slot has fixed-width binary references, and a bounded description stores
exactly `gateBound` slots together with an explicit active gate count. Active
slots must point strictly backward; inactive slots are canonically zero.

The representation is proof-free and finite. A later codec flattens it into
the Boolean cube used by approximate counting without parsing variable-length
fields.
-/


@[expose] public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

/-- Positive binary width sufficient for every wire below
`inputWidth + gateBound`. Keeping the width positive lets the verified binary
comparator handle even the one-wire edge case. -/
def referenceWidth (inputWidth gateBound : Nat) : Nat :=
  max 1 (Fin.bitWidth (inputWidth + gateBound))

/-- Positive binary width sufficient for every gate count through
`gateBound`. -/
def gateCountWidth (gateBound : Nat) : Nat :=
  max 1 (Fin.bitWidth (gateBound + 1))

/-- Three control bits and two fixed-width wire references per gate. -/
def gateSlotWidth (inputWidth gateBound : Nat) : Nat :=
  3 + 2 * referenceWidth inputWidth gateBound

/-- Width of a flattened bounded description: one count field followed by
exactly `gateBound` gate slots. -/
def codeWidth (inputWidth gateBound : Nat) : Nat :=
  gateCountWidth gateBound + gateBound * gateSlotWidth inputWidth gateBound

/-- One fixed-width fan-in-two gate slot.

The operation bit uses the existing raw codec convention: `true` is AND and
`false` is OR. Reference words are little-endian so the circuit comparator can
validate them directly. -/
structure GateSlot (width : Nat) where
  /-- Raw operation selector. -/
  op : Bool
  /-- Whether the first input is negated. -/
  negated0 : Bool
  /-- Whether the second input is negated. -/
  negated1 : Bool
  /-- Little-endian first wire reference. -/
  input0 : BitString width
  /-- Little-endian second wire reference. -/
  input1 : BitString width
  deriving DecidableEq

/-- Product view used to enumerate fixed-width gate slots exactly. -/
def gateSlotEquiv (width : Nat) :
    Equiv (GateSlot width)
      (Bool × Bool × Bool × BitString width × BitString width) where
  toFun slot :=
    (slot.op, slot.negated0, slot.negated1, slot.input0, slot.input1)
  invFun slot :=
    { op := slot.1
      negated0 := slot.2.1
      negated1 := slot.2.2.1
      input0 := slot.2.2.2.1
      input1 := slot.2.2.2.2 }
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance (width : Nat) : Fintype (GateSlot width) :=
  Fintype.ofEquiv
    (Bool × Bool × Bool × BitString width × BitString width)
    (gateSlotEquiv width).symm

namespace GateSlot

/-- Natural value of the first little-endian reference word. -/
def input0Value {width : Nat} (slot : GateSlot width) : Nat :=
  Nat.fromBitsLE slot.input0.toList

/-- Natural value of the second little-endian reference word. -/
def input1Value {width : Nat} (slot : GateSlot width) : Nat :=
  Nat.fromBitsLE slot.input1.toList

/-- Convert a fixed slot to the existing proof-free gate syntax. -/
def toRawGate {width : Nat} (slot : GateSlot width) : RawGate where
  op := RawGate.opOfBit slot.op
  input₀ := slot.input0Value
  input₁ := slot.input1Value
  negated₀ := slot.negated0
  negated₁ := slot.negated1

/-- Canonical all-zero inactive slot. -/
def zero (width : Nat) : GateSlot width where
  op := false
  negated0 := false
  negated1 := false
  input0 := fun _ => false
  input1 := fun _ => false

/-- Both binary references point to already available wires. -/
def WellFormedAt {width : Nat} (slot : GateSlot width)
    (available : Nat) : Prop :=
  slot.input0Value < available ∧ slot.input1Value < available

instance {width : Nat} (slot : GateSlot width) (available : Nat) :
    Decidable (slot.WellFormedAt available) := by
  unfold WellFormedAt
  infer_instance

end GateSlot

/-- A bounded fixed-slot description.

`gateCount.val` slots are active, while all remaining slots are present so the
eventual bit encoding has one parameter-determined width. -/
structure Description (inputWidth gateBound : Nat) where
  /-- Number of active gates, ranging from zero through `gateBound`. -/
  gateCount : Fin (gateBound + 1)
  /-- Fixed collection of gate slots. -/
  slots : Fin gateBound → GateSlot (referenceWidth inputWidth gateBound)
  deriving DecidableEq

/-- Product view used to enumerate bounded descriptions exactly. -/
def descriptionEquiv (inputWidth gateBound : Nat) :
    Equiv (Description inputWidth gateBound)
      (Fin (gateBound + 1) ×
        (Fin gateBound → GateSlot (referenceWidth inputWidth gateBound))) where
  toFun description := (description.gateCount, description.slots)
  invFun description :=
    { gateCount := description.1
      slots := description.2 }
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance (inputWidth gateBound : Nat) :
    Fintype (Description inputWidth gateBound) :=
  Fintype.ofEquiv
    (Fin (gateBound + 1) ×
      (Fin gateBound → GateSlot (referenceWidth inputWidth gateBound)))
    (descriptionEquiv inputWidth gateBound).symm

namespace Description

/-- Active gate count as a natural number. -/
def gateCountNat {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) : Nat :=
  description.gateCount.val

/-- View an active slot through the full fixed slot array. -/
def activeSlot {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound)
    (index : Fin description.gateCountNat) :
    GateSlot (referenceWidth inputWidth gateBound) :=
  description.slots ⟨index.val, by
    have hindex := index.isLt
    change index.val < description.gateCount.val at hindex
    exact lt_of_lt_of_le hindex
      (Nat.le_of_lt_succ description.gateCount.isLt)⟩

/-- Existing raw-circuit syntax represented by the active slots. -/
def toRawCircuit {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) : RawCircuit :=
  List.ofFn fun index => (description.activeSlot index).toRawGate

/-- The description has at least one active gate, hence a designated output. -/
def Positive {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) : Prop :=
  0 < description.gateCountNat

/-- Every active gate points to a primary input or an earlier active gate. -/
def TopologicallyWellFormed {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) : Prop :=
  ∀ index : Fin description.gateCountNat,
    (description.activeSlot index).WellFormedAt (inputWidth + index.val)

/-- Every inactive slot is the canonical all-zero slot. -/
def CanonicallyPadded {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) : Prop :=
  ∀ index : Fin gateBound,
    description.gateCountNat ≤ index.val →
      description.slots index = GateSlot.zero _

/-- Valid fixed-width descriptions are nonempty, topologically ordered, and
canonically padded. -/
def WellFormed {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) : Prop :=
  description.Positive ∧
    description.TopologicallyWellFormed ∧
    description.CanonicallyPadded

instance {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) :
    Decidable description.Positive := by
  unfold Positive
  infer_instance

instance {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) :
    Decidable description.TopologicallyWellFormed := by
  unfold TopologicallyWellFormed
  infer_instance

instance {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) :
    Decidable description.CanonicallyPadded := by
  unfold CanonicallyPadded
  infer_instance

instance {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) :
    Decidable description.WellFormed := by
  unfold WellFormed
  infer_instance

end Description

end FixedWidth

end CircuitCode

end Complexity
