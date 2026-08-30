/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Succinct.Normalization.Defs
public import Complexitylib.Metacomplexity.MCSP.Succinct.Normalization.Internal

/-!
# Threshold normalization for SuccinctMCSP

This module caps sampled-circuit thresholds at a semantics-preserving linear
interpolation bound. A direct DNF uses one exact-input term per positive sample;
an existing witness guarantees that no negative sample has the same input as a
positive one. The resulting normalized raw witness relation is polynomially
balanced in the canonical instance-code length, including empty sample lists
at very large binary-encoded arities.
-/


public section

namespace Complexity

namespace SuccinctMCSP

namespace Instance

/-- Every feasible instance remains feasible at the explicit sampled DNF
upper bound. Contradictory instances are not claimed to become feasible. -/
theorem hasCircuitAtMost_trivialCircuitSizeBound (inst : Instance)
    (hsmall : inst.HasCircuitAtMost) :
    ({ inst with threshold := inst.trivialCircuitSizeBound } : Instance).HasCircuitAtMost :=
  hasCircuitAtMost_trivialCircuitSizeBound_internal inst hsmall

/-- The effective threshold never exceeds the threshold supplied in the code. -/
theorem effectiveThreshold_le_threshold (inst : Instance) :
    inst.effectiveThreshold ≤ inst.threshold :=
  effectiveThreshold_le_threshold_internal inst

/-- The effective threshold never exceeds the sampled interpolation bound. -/
theorem effectiveThreshold_le_trivialCircuitSizeBound (inst : Instance) :
    inst.effectiveThreshold ≤ inst.trivialCircuitSizeBound :=
  effectiveThreshold_le_trivialCircuitSizeBound_internal inst

/-- Capping the threshold at the sampled interpolation bound preserves
feasibility in both directions. -/
@[simp] theorem hasCircuitAtMost_normalizeThreshold_iff (inst : Instance) :
    inst.normalizeThreshold.HasCircuitAtMost ↔ inst.HasCircuitAtMost :=
  hasCircuitAtMost_normalizeThreshold_iff_internal inst

/-- The sampled interpolation bound is no larger than the canonical instance
code itself. -/
theorem trivialCircuitSizeBound_le_encodeLength (inst : Instance) :
    inst.trivialCircuitSizeBound ≤ inst.encode.length :=
  trivialCircuitSizeBound_le_encodeLength_internal inst

/-- The explicit normalized raw-witness envelope is polynomial. -/
theorem rawWitnessLengthPolynomial_polyBound :
    PolyBound rawWitnessLengthPolynomial :=
  rawWitnessLengthPolynomial_polyBound_internal

/-- Every sampled yes-instance has a normalized raw witness whose code is
polynomially bounded by the canonical instance-code length. -/
theorem exists_normalizedRawWitness_length_le_encode
    (inst : Instance) (hsmall : inst.HasCircuitAtMost) :
    ∃ code,
      inst.normalizeThreshold.IsRawCircuitWitness code ∧
        code.length ≤ rawWitnessLengthPolynomial inst.encode.length :=
  exists_normalizedRawWitness_length_le_encode_internal inst hsmall

end Instance

/-- The normalized raw witness relation is polynomially balanced. -/
theorem rawWitnessRelation_polyBalanced :
    PolyBalanced RawWitnessRelation :=
  rawWitnessRelation_polyBalanced_internal

/-- SuccinctMCSP membership is exactly existence of a normalized, polynomially
bounded raw witness. -/
theorem mem_iff_exists_rawWitnessRelation (bits : List Bool) :
    bits ∈ Complexity.SuccinctMCSP ↔
      ∃ witness, RawWitnessRelation bits witness :=
  mem_iff_exists_rawWitnessRelation_internal bits

end SuccinctMCSP

end Complexity
