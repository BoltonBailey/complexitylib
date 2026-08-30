/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Succinct.Witness.Defs
public import Complexitylib.Metacomplexity.MCSP.Succinct.Witness.Internal

/-!
# Executable raw-circuit witnesses for SuccinctMCSP

This module exposes the finite witness relation for sampled circuit
minimization. It reuses the canonical machine-facing circuit decoder and
evaluator, checks every listed sample, and agrees exactly with the typed
`SuccinctMCSP.Instance.HasCircuitAtMost` predicate. Zero arity uses a one-bit
constant witness rather than the positive-arity circuit encoding.
-/


public section

namespace Complexity

namespace SuccinctMCSP

namespace Instance

/-- The Boolean raw-circuit verifier decides its advertised relation. -/
@[simp] theorem verifyRawCircuit_eq_true_iff (inst : Instance)
    (code : List Bool) :
    inst.verifyRawCircuit code = true ↔ inst.IsRawCircuitWitness code :=
  verifyRawCircuit_eq_true_iff_internal inst code

/-- Serializing a positive-arity typed circuit within the threshold produces
a witness matching exactly the listed samples. -/
theorem isRawCircuitWitness_encodeCircuit (inst : Instance)
    [NeZero inst.arity] {internalGates : ℕ}
    (circuit : Circuit Basis.andOr2 inst.arity 1 internalGates)
    (hsize : circuit.size ≤ inst.threshold)
    (hsamples : inst.SamplesFunction (fun input => circuit.eval input 0)) :
    inst.IsRawCircuitWitness (CircuitCode.encodeCircuit circuit) :=
  isRawCircuitWitness_encodeCircuit_internal inst circuit hsize hsamples

/-- Every valid positive-arity raw witness reconstructs a typed circuit within
the threshold that matches every listed sample. -/
theorem hasCircuitAtMost_of_isRawCircuitWitness (inst : Instance)
    [NeZero inst.arity] {code : List Bool}
    (hwitness : inst.IsRawCircuitWitness code) : inst.HasCircuitAtMost :=
  hasCircuitAtMost_of_isRawCircuitWitness_internal inst hwitness

/-- Typed sampled feasibility is equivalent to existence of a finite raw
witness, including the zero-arity constant convention. -/
theorem exists_isRawCircuitWitness_iff (inst : Instance) :
    (∃ code, inst.IsRawCircuitWitness code) ↔ inst.HasCircuitAtMost :=
  exists_isRawCircuitWitness_iff_internal inst

/-- Increasing the threshold preserves every valid sampled raw witness. -/
theorem IsRawCircuitWitness.mono (inst : Instance) {first second : ℕ}
    (hthreshold : first ≤ second) {code : List Bool}
    (hwitness :
      ({ inst with threshold := first } : Instance).IsRawCircuitWitness code) :
    ({ inst with threshold := second } : Instance).IsRawCircuitWitness code :=
  isRawCircuitWitness_threshold_mono_internal inst hthreshold hwitness

/-- Every accepted raw witness satisfies the concrete serialization envelope. -/
theorem IsRawCircuitWitness.length_le (inst : Instance) {code : List Bool}
    (hwitness : inst.IsRawCircuitWitness code) :
    code.length ≤ inst.rawWitnessCodeLengthBound :=
  isRawCircuitWitness_length_le_internal inst hwitness

/-- Every sampled yes-instance has a raw witness within the explicit envelope.

The envelope still depends on the numeric threshold; the normalization layer
will turn it into a polynomial bound in encoded input length. -/
theorem exists_isRawCircuitWitness_length_le (inst : Instance)
    (hsmall : inst.HasCircuitAtMost) :
    ∃ code,
      inst.IsRawCircuitWitness code ∧
        code.length ≤ inst.rawWitnessCodeLengthBound :=
  exists_isRawCircuitWitness_length_le_internal inst hsmall

end Instance

end SuccinctMCSP

end Complexity
