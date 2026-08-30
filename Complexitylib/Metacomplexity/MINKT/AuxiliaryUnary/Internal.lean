/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.AverageCase.AuxiliaryUnary.Internal
public import Complexitylib.Metacomplexity.MINKT.AuxiliaryUnary.Defs
public import Complexitylib.Metacomplexity.MINKT.Internal

/-!
# Auxiliary-unary MINKT instances -- proof internals

Proofs that auxiliary-unary samples are exact canonical MINKT codes, together
with their machine-relative membership and point-mass characterizations.
-/


public section

namespace Complexity

namespace AuxiliaryUnarySeed

variable {tapes : ℕ}

theorem minktInstance_output_internal {m : ℕ} (seed : AuxiliaryUnarySeed m) :
    seed.minktInstance.output = seed.binary := rfl

theorem minktInstance_time_internal {m : ℕ} (seed : AuxiliaryUnarySeed m) :
    seed.minktInstance.time = m - seed.split := rfl

theorem minktInstance_output_length_internal {m : ℕ}
    (seed : AuxiliaryUnarySeed m) :
    seed.minktInstance.output.length = seed.split := by
  exact binary_length_internal seed

theorem minktInstance_time_pos_internal {m : ℕ} (hm : 0 < m)
    (seed : AuxiliaryUnarySeed m) : 0 < seed.minktInstance.time := by
  exact Nat.sub_pos_of_lt (split_lt_internal hm seed)

theorem encode_minktInstance_internal {m : ℕ} (seed : AuxiliaryUnarySeed m) :
    seed.minktInstance.encode = seed.sample := by
  rfl

theorem decode?_sample_internal {m : ℕ} (seed : AuxiliaryUnarySeed m) :
    MINKT.Instance.decode? seed.sample = some seed.minktInstance := by
  rw [← encode_minktInstance_internal]
  exact MINKT.Instance.decode?_encode_internal seed.minktInstance

theorem sample_mem_minkt_iff_internal {m : ℕ} (seed : AuxiliaryUnarySeed m)
    (machine : TM tapes) (threshold : ℕ → ℕ) :
    seed.sample ∈ MINKT machine threshold ↔
      seed.minktInstance.IsBelow machine threshold := by
  rw [← encode_minktInstance_internal]
  simp [MINKT, MINKT.Instance.decode?_encode_internal]

theorem sample_mem_minkt_iff_complexity_internal {m : ℕ}
    (seed : AuxiliaryUnarySeed m) (machine : TM tapes)
    (threshold : ℕ → ℕ) :
    seed.sample ∈ MINKT machine threshold ↔
      machine.timeBoundedKolmogorovComplexity seed.binary
          (m - seed.split) <
        (threshold seed.split : WithTop ℕ) := by
  rw [sample_mem_minkt_iff_internal]
  simp only [MINKT.Instance.IsBelow, minktInstance_output_internal,
    minktInstance_time_internal, binary_length_internal]

end AuxiliaryUnarySeed

namespace FiniteEnsemble

theorem mass_auxiliaryUnary_minktInstance_internal {m n : ℕ} (hn : n < m)
    (output : Fin n → Bool) :
    auxiliaryUnary.mass m
        (MINKT.Instance.encode
          { output := List.ofFn output, time := m - n }) =
      1 / ((m : ℚ) * (2 : ℚ) ^ n) := by
  simpa [MINKT.Instance.encode, MINKT.Instance.unaryClock] using
    mass_auxiliaryUnary_pair_internal hn output

end FiniteEnsemble

end Complexity
