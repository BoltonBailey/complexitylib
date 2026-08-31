/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Conversion.Defs
import Complexitylib.Circuits.Encoding.FixedWidth.Conversion.Internal

/-!
# Conversion between raw circuits and fixed-width descriptions

Canonical zero padding makes valid fixed-width descriptions exactly equivalent
to nonempty topologically ordered raw circuits within the gate bound. The two
round trips preserve every gate, reference, and control bit.
-/


public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace GateSlot

/-- A fixed-width reference word serializes to the expected little-endian
bits. -/
@[simp] theorem toList_referenceBits (width value : Nat) :
    (referenceBits width value).toList = Nat.toBitsLE width value :=
  toList_referenceBits_internal width value

/-- Encoding and decoding a raw gate is exact when both references fit. -/
theorem toRawGate_ofRawGate {width : Nat} {gate : RawGate}
    (hinput0 : gate.input₀ < 2 ^ width)
    (hinput1 : gate.input₁ < 2 ^ width) :
    (ofRawGate width gate).toRawGate = gate :=
  toRawGate_ofRawGate_internal hinput0 hinput1

/-- Every fixed slot is recovered after conversion through raw-gate syntax. -/
@[simp] theorem ofRawGate_toRawGate {width : Nat}
    (slot : GateSlot width) :
    ofRawGate width slot.toRawGate = slot :=
  ofRawGate_toRawGate_internal slot

end GateSlot

namespace Description

/-- Encoding a bounded topologically ordered raw circuit and converting it
back preserves the exact gate list. -/
theorem toRawCircuit_ofRawCircuit
    {inputWidth gateBound : Nat} {circuit : RawCircuit}
    (htopological : circuit.TopologicallyWellFormed inputWidth)
    (hbound : circuit.length ≤ gateBound) :
    (ofRawCircuit (inputWidth := inputWidth) circuit hbound).toRawCircuit =
      circuit :=
  toRawCircuit_ofRawCircuit_internal htopological hbound

/-- A bounded valid raw circuit produces a valid fixed-width description. -/
theorem ofRawCircuit_wellFormed
    {inputWidth gateBound : Nat} {circuit : RawCircuit}
    (hcircuit : circuit.WellFormed inputWidth)
    (hbound : circuit.length ≤ gateBound) :
    (ofRawCircuit (inputWidth := inputWidth) circuit hbound).WellFormed :=
  ofRawCircuit_wellFormed_internal hcircuit hbound

/-- Canonical padding makes conversion from a description through raw syntax
an exact round trip. -/
theorem ofRawCircuit_toRawCircuit
    {inputWidth gateBound : Nat}
    {description : Description inputWidth gateBound}
    (hcanonical : description.CanonicallyPadded) :
    ofRawCircuit description.toRawCircuit
        (by
          rw [Description.length_toRawCircuit]
          exact description.gateCountNat_le_gateBound) = description :=
  ofRawCircuit_toRawCircuit_internal hcanonical

end Description

/-- Valid fixed-width descriptions are exactly bounded valid raw circuits. -/
def wellFormedEquiv (inputWidth gateBound : Nat) :
    Equiv (ValidDescription inputWidth gateBound)
      (BoundedRawCircuit inputWidth gateBound) :=
  wellFormedEquivInternal inputWidth gateBound

/-- The forward equivalence map is the raw-circuit view of a valid fixed-width
description. -/
@[simp] theorem wellFormedEquiv_apply_val
    {inputWidth gateBound : Nat}
    (description : ValidDescription inputWidth gateBound) :
    (wellFormedEquiv inputWidth gateBound description).val =
      description.val.toRawCircuit := by
  change (wellFormedEquivInternal inputWidth gateBound description).val =
    description.val.toRawCircuit
  exact wellFormedEquiv_apply_val_internal description

/-- The inverse equivalence map is canonical fixed-width conversion of a
bounded raw circuit. -/
@[simp] theorem wellFormedEquiv_symm_val
    {inputWidth gateBound : Nat}
    (circuit : BoundedRawCircuit inputWidth gateBound) :
    ((wellFormedEquiv inputWidth gateBound).symm circuit).val =
      Description.ofRawCircuit circuit.val circuit.property.2 := by
  change ((wellFormedEquivInternal inputWidth gateBound).symm circuit).val =
    Description.ofRawCircuit circuit.val circuit.property.2
  exact wellFormedEquiv_symm_val_internal circuit

noncomputable instance (inputWidth gateBound : Nat) :
    Fintype (BoundedRawCircuit inputWidth gateBound) :=
  Fintype.ofEquiv (ValidDescription inputWidth gateBound)
    (wellFormedEquiv inputWidth gateBound)

end FixedWidth

end CircuitCode

end Complexity
