/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Witness.Defs
public import Complexitylib.Metacomplexity.MCSP.Witness.Internal

/-!
# Executable raw-circuit witnesses for MCSP

This module exposes the finite witness relation underlying the eventual proof
that MCSP is in NP. The relation reuses the existing canonical raw-circuit
decoder and evaluator and is proved equivalent to the typed MCSP semantics.
-/


public section

namespace Complexity

namespace MCSP

namespace Instance

/-- The Boolean raw-circuit verifier decides its advertised witness relation. -/
@[simp] theorem verifyRawCircuit_eq_true_iff (inst : Instance) (code : List Bool) :
    inst.verifyRawCircuit code = true ↔ inst.IsRawCircuitWitness code :=
  verifyRawCircuit_eq_true_iff_internal inst code

/-- Serializing any typed circuit within the threshold yields a valid raw MCSP
witness with identical truth-table semantics. -/
theorem isRawCircuitWitness_encodeCircuit (inst : Instance)
    [NeZero inst.arity] {internalGates : ℕ}
    (circuit : Circuit Basis.andOr2 inst.arity 1 internalGates)
    (hsize : circuit.size ≤ inst.threshold)
    (hcomputes : circuit.Computes inst.function) :
    inst.IsRawCircuitWitness (CircuitCode.encodeCircuit circuit) :=
  isRawCircuitWitness_encodeCircuit_internal inst circuit hsize hcomputes

/-- Every valid positive-arity raw witness reconstructs a typed circuit within
the instance threshold. -/
theorem hasCircuitAtMost_of_isRawCircuitWitness (inst : Instance)
    [NeZero inst.arity] {code : List Bool}
    (hwitness : inst.IsRawCircuitWitness code) : inst.HasCircuitAtMost :=
  hasCircuitAtMost_of_isRawCircuitWitness_internal inst hwitness

/-- An instance has a sufficiently small typed circuit exactly when it has a
finite canonical raw-circuit witness, including the zero-arity convention. -/
theorem exists_isRawCircuitWitness_iff (inst : Instance) :
    (∃ code, inst.IsRawCircuitWitness code) ↔ inst.HasCircuitAtMost :=
  exists_isRawCircuitWitness_iff_internal inst

/-- Every MCSP yes-instance has a raw witness within the explicit serialization
bound. Threshold normalization is still required before treating this as a
polynomial bound in encoded instance length. -/
theorem exists_isRawCircuitWitness_length_le (inst : Instance)
    (hsmall : inst.HasCircuitAtMost) :
    ∃ code,
      inst.IsRawCircuitWitness code ∧ code.length ≤ inst.rawWitnessCodeLengthBound :=
  exists_isRawCircuitWitness_length_le_internal inst hsmall

end Instance

end MCSP

end Complexity
