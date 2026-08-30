/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.AverageCase.AuxiliaryUnary
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

end AuxiliaryUnarySeed

namespace FiniteEnsemble

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
