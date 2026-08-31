/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Shift.Defs
public import Complexitylib.Circuits.Encoding.Shift.Internal

/-!
# Relocating raw circuit fragments

Uniformly shifting a raw fragment preserves its gate count and local topology.
Evaluation after a memo prefix is exactly the prefix followed by the original
local evaluation result.
-/


public section

namespace Complexity

namespace CircuitCode

namespace RawGate

/-- Wire relocation does not change a gate's Boolean operation. -/
@[simp] theorem eval_shift (offset : Nat) (gate : RawGate)
    (value₀ value₁ : Bool) :
    (gate.shift offset).eval value₀ value₁ = gate.eval value₀ value₁ :=
  eval_shift_internal offset gate value₀ value₁

/-- A shifted gate is valid at the shifted boundary exactly when the original
gate is valid at its local boundary. -/
theorem wellFormedAt_shift_iff (offset available : Nat) (gate : RawGate) :
    (gate.shift offset).WellFormedAt (offset + available) ↔
      gate.WellFormedAt available :=
  wellFormedAt_shift_iff_internal offset available gate

end RawGate

namespace RawCircuit

/-- Wire relocation preserves the exact gate count. -/
@[simp] theorem length_shift (offset : Nat) (circuit : RawCircuit) :
    (circuit.shift offset).length = circuit.length :=
  length_shift_internal offset circuit

/-- Uniform relocation preserves and reflects local topological validity. -/
theorem topologicallyWellFormed_shift_iff
    (offset available : Nat) (circuit : RawCircuit) :
    (circuit.shift offset).TopologicallyWellFormed (offset + available) ↔
      circuit.TopologicallyWellFormed available :=
  topologicallyWellFormed_shift_iff_internal offset available circuit

/-- Evaluating a relocated fragment after a prefix preserves that prefix and
reproduces the original local result behind it. -/
theorem evalAux?_shift (offset : Nat) (circuit : RawCircuit)
    (leading wires : Array Bool) (hleading : leading.size = offset) :
    evalAux? (circuit.shift offset) (leading ++ wires) =
      (evalAux? circuit wires).map fun result => leading ++ result :=
  evalAux?_shift_internal offset circuit leading wires hleading

end RawCircuit

end CircuitCode

end Complexity
