/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.AverageCase.AuxiliaryUnary
public import Complexitylib.Metacomplexity.Kolmogorov.Incompressibility
public import Complexitylib.Metacomplexity.MINKT.AuxiliaryUnary.Defs
public import Complexitylib.Metacomplexity.MINKT.AuxiliaryUnary.Internal

/-!
# The auxiliary-unary distribution as canonical MINKT instances

Every seed in Hirahara's auxiliary-unary ensemble samples the canonical MINKT
code of its retained binary prefix and remaining unary clock. This module makes
that identity explicit and transfers exact decoding, membership, and point-mass
facts to MINKT notation.
-/


public section

namespace Complexity

namespace AuxiliaryUnarySeed

variable {tapes : ℕ}

/-- The sampled MINKT output is exactly the retained binary prefix. -/
@[simp] theorem minktInstance_output {m : ℕ} (seed : AuxiliaryUnarySeed m) :
    seed.minktInstance.output = seed.binary :=
  minktInstance_output_internal seed

/-- The sampled MINKT clock fills the part after the retained prefix. -/
@[simp] theorem minktInstance_time {m : ℕ} (seed : AuxiliaryUnarySeed m) :
    seed.minktInstance.time = m - seed.split :=
  minktInstance_time_internal seed

/-- The sampled instance's output length is the selected split. -/
theorem minktInstance_output_length {m : ℕ}
    (seed : AuxiliaryUnarySeed m) :
    seed.minktInstance.output.length = seed.split :=
  minktInstance_output_length_internal seed

/-- Every positive auxiliary-unary slice gives its MINKT instance a positive
clock. -/
theorem minktInstance_time_pos {m : ℕ} (hm : 0 < m)
    (seed : AuxiliaryUnarySeed m) : 0 < seed.minktInstance.time :=
  minktInstance_time_pos_internal hm seed

/-- The auxiliary-unary sample is definitionally the canonical encoding of its
MINKT instance. -/
@[simp] theorem encode_minktInstance {m : ℕ} (seed : AuxiliaryUnarySeed m) :
    seed.minktInstance.encode = seed.sample :=
  encode_minktInstance_internal seed

/-- MINKT decoding of every auxiliary-unary sample succeeds exactly. -/
@[simp] theorem decode?_sample_minktInstance {m : ℕ}
    (seed : AuxiliaryUnarySeed m) :
    MINKT.Instance.decode? seed.sample = some seed.minktInstance :=
  decode?_sample_internal seed

/-- Auxiliary-unary sample membership is membership of the sampled canonical
MINKT instance. -/
theorem sample_mem_minkt_iff {m : ℕ} (seed : AuxiliaryUnarySeed m)
    (machine : TM tapes) (threshold : ℕ → ℕ) :
    seed.sample ∈ MINKT machine threshold ↔
      seed.minktInstance.IsBelow machine threshold :=
  sample_mem_minkt_iff_internal seed machine threshold

/-- Expanded sample membership uses the selected prefix length and remaining
primitive clock directly. -/
theorem sample_mem_minkt_iff_complexity {m : ℕ}
    (seed : AuxiliaryUnarySeed m) (machine : TM tapes)
    (threshold : ℕ → ℕ) :
    seed.sample ∈ MINKT machine threshold ↔
      machine.timeBoundedKolmogorovComplexity seed.binary
          (m - seed.split) <
        (threshold seed.split : WithTop ℕ) :=
  sample_mem_minkt_iff_complexity_internal seed machine threshold

/-- The MINKT event of a seed is exactly membership of its retained prefix in
the corresponding fixed-length strict-compressibility set. -/
theorem sample_mem_minkt_iff_mem_strictlyCompressible {m : ℕ}
    (seed : AuxiliaryUnarySeed m) (machine : TM tapes)
    (threshold : ℕ → ℕ) :
    seed.sample ∈ MINKT machine threshold ↔
      seed.binaryBits ∈ machine.timeBoundedStrictlyCompressibleStrings
        seed.split (m - seed.split) (threshold seed.split) :=
  sample_mem_minkt_iff_mem_strictlyCompressible_internal
    seed machine threshold

end AuxiliaryUnarySeed

namespace FiniteEnsemble

/-- Exact conditioning identity for strict MINKT under a positive
auxiliary-unary slice: its probability is the uniform average of the
fixed-length strict-compressibility probabilities over all split lengths. -/
theorem probability_auxiliaryUnary_minkt_eq_average
    {tapes m : ℕ} (hm : 0 < m) (machine : TM tapes)
    (threshold : ℕ → ℕ) :
    auxiliaryUnaryMINKTProbability machine threshold m =
      (1 / (m : ℚ)) * ∑ n : Fin m,
        eventProb (machine.timeBoundedStrictlyCompressibleStrings
          n.val (m - n.val) (threshold n.val)) :=
  probability_auxiliaryUnary_minkt_eq_average_internal hm machine threshold

/-- Strict incompressibility bounds the MINKT probability by the average of
the sharp per-length ratios `(2^r(n) - 1) / 2^n`. -/
theorem probability_auxiliaryUnary_minkt_le_average_incompressibility
    {tapes m : ℕ} (hm : 0 < m) (machine : TM tapes)
    (threshold : ℕ → ℕ) :
    auxiliaryUnaryMINKTProbability machine threshold m ≤
      (1 / (m : ℚ)) * ∑ n : Fin m,
        ((2 ^ threshold n.val - 1 : ℕ) : ℚ) / (2 : ℚ) ^ n.val :=
  probability_auxiliaryUnary_minkt_le_average_incompressibility_internal
    hm machine threshold

/-- Any common upper bound on the strict incompressibility ratios bounds the
entire positive auxiliary-unary slice. -/
theorem probability_auxiliaryUnary_minkt_le_of_pointwise
    {tapes m : ℕ} (hm : 0 < m) (machine : TM tapes)
    (threshold : ℕ → ℕ) (bound : ℚ)
    (hbound : ∀ n : Fin m,
      ((2 ^ threshold n.val - 1 : ℕ) : ℚ) / (2 : ℚ) ^ n.val ≤ bound) :
    auxiliaryUnaryMINKTProbability machine threshold m ≤ bound :=
  probability_auxiliaryUnary_minkt_le_of_pointwise_internal
    hm machine threshold bound hbound

/-- Exact point mass of a canonical MINKT instance in the auxiliary-unary
ensemble. -/
theorem mass_auxiliaryUnary_minktInstance {m n : ℕ} (hn : n < m)
    (output : Fin n → Bool) :
    auxiliaryUnary.mass m
        (MINKT.Instance.encode
          { output := List.ofFn output, time := m - n }) =
      1 / ((m : ℚ) * (2 : ℚ) ^ n) :=
  mass_auxiliaryUnary_minktInstance_internal hn output

end FiniteEnsemble

end Complexity
