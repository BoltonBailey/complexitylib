/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Defs
public import Complexitylib.Metacomplexity.MCSP.Succinct.Defs

/-!
# Executable raw-circuit witnesses for SuccinctMCSP -- definitions

This layer checks the existing machine-facing fan-in-two circuit encoding
against a sampled instance. Positive-arity witnesses must be canonical raw
circuits, fit the size threshold, and match every listed sample. At arity zero,
the one-bit witness is the selected constant output and must satisfy every
sample.

The relation is executable. Its initial code-length envelope depends on the
numeric threshold; a later normalization layer will replace that threshold by
a polynomial sampled-circuit upper bound before packaging the relation in FNP.
-/


@[expose] public section

namespace Complexity

namespace SuccinctMCSP

namespace Instance

/-- A canonical raw circuit, or a zero-arity constant bit, witnessing sampled
circuit feasibility. -/
def IsRawCircuitWitness (inst : Instance) (code : List Bool) : Prop :=
  if inst.arity = 0 then
    match code with
    | [output] =>
        inst.samples.Forall (fun sample => output = sample.output)
    | _ => False
  else
    match CircuitCode.RawCircuit.decode? code with
    | none => False
    | some circuit =>
        circuit.WellFormed inst.arity ∧
          circuit.length ≤ inst.threshold ∧
            inst.samples.Forall fun sample =>
              circuit.eval? sample.input.toList = some sample.output

instance (inst : Instance) (code : List Bool) :
    Decidable (inst.IsRawCircuitWitness code) := by
  unfold IsRawCircuitWitness
  split
  · cases code with
    | nil =>
        change Decidable False
        exact inferInstance
    | cons output rest =>
        cases rest with
        | nil =>
            change Decidable
              (inst.samples.Forall (fun sample => output = sample.output))
            exact inferInstance
        | cons next rest =>
            change Decidable False
            exact inferInstance
  · cases CircuitCode.RawCircuit.decode? code <;> exact inferInstance

/-- Executable Boolean checker for sampled raw-circuit witnesses. -/
def verifyRawCircuit (inst : Instance) (code : List Bool) : Bool :=
  decide (inst.IsRawCircuitWitness code)

/-- Serialization envelope for a typed circuit within the stored threshold.

The leading one also covers the zero-arity constant witness. -/
def rawWitnessCodeLengthBound (inst : Instance) : ℕ :=
  1 + inst.threshold * (2 * (inst.arity + inst.threshold) + 6)

end Instance

end SuccinctMCSP

end Complexity
