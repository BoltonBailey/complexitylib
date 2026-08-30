/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.InputReindexing.Defs
public import Complexitylib.Circuits.InputReindexing.Internal

/-!
# Circuit input reindexing

Reindexing transports a circuit along an arbitrary map from its original
primary inputs into a new positive input tuple. It preserves the internal and
output gates exactly, so size is unchanged and evaluation is precomposition
with the supplied input map.
-/


public section

namespace Complexity

namespace Circuit

/-- Reindexing maps a primary-input wire through the supplied input map. -/
@[simp] theorem reindexInputWire_input {N N' G : ℕ}
    (mapInput : Fin N → Fin N') (input : Fin N) :
    reindexInputWire (G := G) mapInput (Fin.castAdd G input) =
      Fin.castAdd G (mapInput input) :=
  reindexInputWire_input_internal mapInput input

/-- Reindexing preserves every internal-gate wire index. -/
@[simp] theorem reindexInputWire_gate {N N' G : ℕ}
    (mapInput : Fin N → Fin N') (gate : Fin G) :
    reindexInputWire mapInput (Fin.natAdd N gate) =
      Fin.natAdd N' gate :=
  reindexInputWire_gate_internal mapInput gate

/-- Reindexing preserves the value of every source wire after input
precomposition. -/
theorem wireValue_reindexInputs {B : Basis} {N N' M G : ℕ}
    [NeZero N] [NeZero N'] [NeZero M]
    (circuit : Circuit B N M G) (mapInput : Fin N → Fin N')
    (input : BitString N') (wire : Fin (N + G)) :
    (circuit.reindexInputs mapInput).wireValue input
        (reindexInputWire mapInput wire) =
      circuit.wireValue (input ∘ mapInput) wire :=
  wireValue_reindexInputs_internal circuit mapInput input wire

/-- Reindexing circuit inputs is semantic precomposition. -/
@[simp] theorem eval_reindexInputs {B : Basis} {N N' M G : ℕ}
    [NeZero N] [NeZero N'] [NeZero M]
    (circuit : Circuit B N M G) (mapInput : Fin N → Fin N')
    (input : BitString N') :
    (circuit.reindexInputs mapInput).eval input =
      circuit.eval (input ∘ mapInput) :=
  eval_reindexInputs_internal circuit mapInput input

/-- Reindexing primary inputs preserves exact circuit size. -/
@[simp] theorem size_reindexInputs {B : Basis} {N N' M G : ℕ}
    [NeZero N] [NeZero N'] [NeZero M]
    (circuit : Circuit B N M G) (mapInput : Fin N → Fin N') :
    (circuit.reindexInputs mapInput).size = circuit.size :=
  rfl

end Circuit

end Complexity
