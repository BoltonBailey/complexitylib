/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Parity.Defs
import Complexitylib.Circuits.Encoding.Parity.Internal

/-!
# Raw parity-circuit fragments

The compiler in this module emits one false initializer and three shared gates
per selected existing wire. It exposes exact size, topological well-formedness,
and iterative evaluation theorems for use in larger raw-circuit builders.
-/


public section

namespace Complexity

namespace CircuitCode

namespace Parity

/-- Parity compilation emits exactly one initializer and three gates per
selected wire. -/
@[simp] theorem length_compileRaw (available : ℕ) {inputCount : ℕ}
    (refs : Fin inputCount → ℕ) :
    (compileRaw available refs).length = 1 + 3 * inputCount :=
  length_compileRaw_internal available refs

/-- The last gate emitted by parity compilation carries its result. -/
theorem outputWire_eq (available : ℕ) {inputCount : ℕ}
    (refs : Fin inputCount → ℕ) :
    outputWire available inputCount =
      available + (compileRaw available refs).length - 1 :=
  outputWire_eq_internal available refs

/-- The parity fragment is topologically ordered whenever every selected
reference names a pre-existing wire. -/
theorem topologicallyWellFormed_compileRaw (available : ℕ)
    [NeZero available] {inputCount : ℕ} (refs : Fin inputCount → ℕ)
    (hrefs : ∀ i, refs i < available) :
    (compileRaw available refs).TopologicallyWellFormed available :=
  topologicallyWellFormed_compileRaw_internal available refs hrefs

/-- The parity fragment is a valid nonempty raw circuit whenever its selected
references name pre-existing wires. -/
theorem compileRaw_wellFormed (available : ℕ) [NeZero available]
    {inputCount : ℕ} (refs : Fin inputCount → ℕ)
    (hrefs : ∀ i, refs i < available) :
    (compileRaw available refs).WellFormed available :=
  compileRaw_wellFormed_internal available refs hrefs

/-- Iterative evaluation of the parity fragment returns the XOR of the
selected input bits. -/
theorem eval?_compileRaw (available : ℕ) [NeZero available]
    {inputCount : ℕ} (refs : Fin inputCount → ℕ)
    (hrefs : ∀ i, refs i < available) (input : BitString available) :
    RawCircuit.eval? (compileRaw available refs) input.toList =
      some (foldXor inputCount (fun i => input ⟨refs i, hrefs i⟩)) :=
  eval?_compileRaw_internal available refs hrefs input

/-- Fragment evaluation appends the parity value while preserving every
pre-existing memo wire. -/
theorem evalAux?_compileRaw (available : ℕ) [NeZero available]
    {inputCount : ℕ} (refs : Fin inputCount → ℕ)
    (bits : Fin inputCount → Bool) (wires : Array Bool)
    (hsize : wires.size = available)
    (hrefs : ∀ i, refs i < available)
    (hinputs : ∀ i, wires[refs i]? = some (bits i)) :
    ∃ result,
      RawCircuit.evalAux? (compileRaw available refs) wires = some result ∧
      result.size = wires.size + (1 + 3 * inputCount) ∧
      (∀ i < wires.size, result[i]? = wires[i]?) ∧
      result[outputWire available inputCount]? = some (foldXor inputCount bits) :=
  evalAux?_compileRaw_internal available refs bits wires hsize hrefs hinputs

end Parity

end CircuitCode

end Complexity
