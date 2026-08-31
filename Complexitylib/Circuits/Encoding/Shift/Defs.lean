/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Defs

/-!
# Relocating raw circuit fragments -- definitions

A raw fragment whose incoming wires begin at zero can be mounted after an
arbitrary prefix by adding the prefix width to every wire reference. Gate order,
negation flags, and operations are unchanged.
-/


@[expose] public section

namespace Complexity

namespace CircuitCode

namespace RawGate

/-- Add a fixed offset to both input references of a raw gate. -/
def shift (offset : Nat) (gate : RawGate) : RawGate where
  op := gate.op
  input₀ := offset + gate.input₀
  input₁ := offset + gate.input₁
  negated₀ := gate.negated₀
  negated₁ := gate.negated₁

end RawGate

namespace RawCircuit

/-- Relocate every reference in a raw circuit by the same wire offset. -/
def shift (offset : Nat) (circuit : RawCircuit) : RawCircuit :=
  circuit.map (RawGate.shift offset)

end RawCircuit

end CircuitCode

end Complexity
