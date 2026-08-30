/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Normalization.Defs
public import Complexitylib.Metacomplexity.MCSP.Normalization.Internal

/-!
# Threshold normalization for MCSP

This module caps binary MCSP thresholds at a concrete unconditional
truth-table-size bound, proves that the cap preserves membership, and derives a
raw-witness length bound that is polynomial in encoded instance length.
-/


public section

namespace Complexity

namespace MCSP

namespace Instance

/-- Function arity never exceeds its truth-table length. -/
theorem arity_le_tableLength (arity : ℕ) : arity ≤ 2 ^ arity :=
  arity_le_tableLength_internal arity

/-- Every Boolean function has an `andOr2` circuit within the chosen coarse
truth-table-square bound. -/
theorem exists_circuit_size_le_trivialCircuitSizeBound (inst : Instance)
    [NeZero inst.arity] :
    ∃ (internalGates : ℕ)
        (circuit : Circuit Basis.andOr2 inst.arity 1 internalGates),
      circuit.size ≤ inst.trivialCircuitSizeBound ∧
        circuit.Computes inst.function :=
  exists_circuit_size_le_trivialCircuitSizeBound_internal inst

/-- The unconditional bound itself always makes an instance a yes-instance,
including the explicit zero-arity case. -/
theorem hasCircuitAtMost_trivialCircuitSizeBound (inst : Instance) :
    (inst.withThreshold inst.trivialCircuitSizeBound).HasCircuitAtMost :=
  hasCircuitAtMost_trivialCircuitSizeBound_internal inst

/-- The effective threshold never exceeds the threshold supplied in the input. -/
theorem effectiveThreshold_le_threshold (inst : Instance) :
    inst.effectiveThreshold ≤ inst.threshold :=
  effectiveThreshold_le_threshold_internal inst

/-- The effective threshold never exceeds the unconditional circuit bound. -/
theorem effectiveThreshold_le_trivialCircuitSizeBound (inst : Instance) :
    inst.effectiveThreshold ≤ inst.trivialCircuitSizeBound :=
  effectiveThreshold_le_trivialCircuitSizeBound_internal inst

/-- Capping an oversized threshold preserves MCSP yes/no semantics exactly. -/
theorem hasCircuitAtMost_normalizeThreshold_iff (inst : Instance) :
    inst.normalizeThreshold.HasCircuitAtMost ↔ inst.HasCircuitAtMost :=
  hasCircuitAtMost_normalizeThreshold_iff_internal inst

/-- The unconditional cap is at most a square in total encoded input length. -/
theorem trivialCircuitSizeBound_le_encodeLength (inst : Instance) :
    inst.trivialCircuitSizeBound ≤ (inst.encode.length + 2) ^ 2 :=
  trivialCircuitSizeBound_le_encodeLength_internal inst

/-- Every witness accepted against the normalized threshold has length bounded
by the fixed polynomial in the original canonical instance-code length. -/
theorem IsRawCircuitWitness.normalizeThreshold_length_le_encode
    (inst : Instance) {code : List Bool}
    (hwitness : inst.normalizeThreshold.IsRawCircuitWitness code) :
    code.length ≤ rawWitnessLengthPolynomial inst.encode.length :=
  isRawCircuitWitness_normalizeThreshold_length_le_encode_internal inst hwitness

/-- The normalized raw-witness envelope is pointwise polynomially bounded. -/
theorem rawWitnessLengthPolynomial_polyBound :
    PolyBound rawWitnessLengthPolynomial :=
  rawWitnessLengthPolynomial_polyBound_internal

/-- Every MCSP yes-instance has a canonical raw-circuit witness whose code
length is bounded by one fixed polynomial in the encoded instance length. -/
theorem exists_isRawCircuitWitness_length_le_encode (inst : Instance)
    (hsmall : inst.HasCircuitAtMost) :
    ∃ code,
      inst.IsRawCircuitWitness code ∧
        code.length ≤ rawWitnessLengthPolynomial inst.encode.length :=
  exists_isRawCircuitWitness_length_le_encode_internal inst hsmall

end Instance

/-- The normalized raw-circuit relation is polynomially balanced: every
accepted witness, not merely one selected witness, has polynomial length. -/
theorem rawWitnessRelation_polyBalanced :
    PolyBalanced RawWitnessRelation :=
  rawWitnessRelation_polyBalanced_internal

/-- MCSP membership is exactly existential acceptance by the normalized raw
circuit witness relation, with malformed inputs rejected on both sides. -/
theorem mem_MCSP_iff_exists_rawWitnessRelation (bits : List Bool) :
    bits ∈ MCSP ↔ ∃ witness, RawWitnessRelation bits witness :=
  mem_MCSP_iff_exists_rawWitnessRelation_internal bits

end MCSP

end Complexity
