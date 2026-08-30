/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Defs
public import Complexitylib.Metacomplexity.MCSP.Defs

/-!
# Executable raw-circuit witnesses for MCSP -- definitions

This layer turns the mathematical MCSP predicate into a finite witness
relation over the existing machine-facing circuit syntax. Positive-arity
witnesses must be exact canonical `CircuitCode.RawCircuit` encodings, satisfy
the size threshold, and agree with every truth-table entry. The unique
zero-arity function uses the empty witness, matching its size-zero convention.

`verifyRawCircuit` is executable, but this module does not yet claim a machine
time bound or membership in `NP`. In particular, its code-length bound still
depends on the numeric threshold; oversized binary thresholds must be
normalized before the final NP packaging.
-/


@[expose] public section

namespace Complexity

namespace MCSP

namespace Instance

/-- A canonical encoded raw circuit witnesses that an MCSP instance is small.

At positive arity, verification checks syntax, size, and all `2^arity`
truth-table entries. At arity zero, the unique canonical witness is empty. -/
def IsRawCircuitWitness (inst : Instance) (code : List Bool) : Prop :=
  if inst.arity = 0 then
    code = []
  else
    match CircuitCode.RawCircuit.decode? code with
    | none => False
    | some circuit =>
        circuit.WellFormed inst.arity ∧
          circuit.length ≤ inst.threshold ∧
            ∀ index : Fin (2 ^ inst.arity),
              circuit.eval? (inputOfIndex index).toList = some (inst.table index)

instance (inst : Instance) (code : List Bool) :
    Decidable (inst.IsRawCircuitWitness code) := by
  unfold IsRawCircuitWitness
  split
  · exact inferInstance
  · split
    · exact inferInstance
    · exact inferInstance

/-- Executable Boolean checker for the raw-circuit witness relation. -/
def verifyRawCircuit (inst : Instance) (code : List Bool) : Bool :=
  decide (inst.IsRawCircuitWitness code)

/-- Concrete code-length envelope obtained by serializing a typed circuit no
larger than the instance threshold. This is not yet polynomial in encoded
input length when the binary threshold is oversized. -/
def rawWitnessCodeLengthBound (inst : Instance) : ℕ :=
  1 + inst.threshold * (2 * (inst.arity + inst.threshold) + 6)

end Instance

end MCSP

end Complexity
