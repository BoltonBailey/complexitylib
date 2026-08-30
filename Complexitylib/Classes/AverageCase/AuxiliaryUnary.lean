/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.AverageCase.AuxiliaryUnary.Defs
public import Complexitylib.Classes.AverageCase.AuxiliaryUnary.Internal

/-!
# The auxiliary-unary distribution

This module exposes the exact sampler shape and counting theory for Hirahara's
uniform distribution with auxiliary unary input. At positive parameter `m`, a
sample is `pair x (List.replicate t true)` for uniform `t ∈ {1, ..., m}` and
uniform `x ∈ {0,1}^{m-t}`.
-/


public section

namespace Complexity

namespace AuxiliaryUnarySeed

/-- The selected binary length is strictly below every positive slice
parameter. -/
theorem split_lt {m : ℕ} (hm : 0 < m) (seed : AuxiliaryUnarySeed m) :
    seed.split < m :=
  split_lt_internal hm seed

/-- The retained binary component has the selected length. -/
@[simp] theorem binary_length {m : ℕ} (seed : AuxiliaryUnarySeed m) :
    seed.binary.length = seed.split :=
  binary_length_internal seed

/-- The unary component fills the remainder of the size parameter. -/
@[simp] theorem unary_length {m : ℕ} (seed : AuxiliaryUnarySeed m) :
    seed.unary.length = m - seed.split :=
  unary_length_internal seed

/-- The auxiliary unary clock is nonempty on every positive slice. -/
theorem unary_length_pos {m : ℕ} (hm : 0 < m)
    (seed : AuxiliaryUnarySeed m) : 0 < seed.unary.length :=
  unary_length_pos_internal hm seed

/-- The two decoded component lengths sum to the slice parameter. -/
theorem component_length_sum {m : ℕ} (seed : AuxiliaryUnarySeed m) :
    seed.binary.length + seed.unary.length = m :=
  component_length_sum_internal seed

/-- Decoding an auxiliary-unary sample recovers its two components exactly. -/
@[simp] theorem unpair?_sample {m : ℕ} (seed : AuxiliaryUnarySeed m) :
    unpair? seed.sample = some (seed.binary, seed.unary) :=
  unpair?_sample_internal seed

/-- The `m`th seed space contains `max 1 m * 2^m` equiprobable seeds. -/
theorem card (m : ℕ) :
    Fintype.card (AuxiliaryUnarySeed m) = Nat.max 1 m * 2 ^ m :=
  card_internal m

/-- A uniform `m`-bit string has any fixed length-`n` prefix with probability
exactly `2^-n`. -/
theorem prefix_probability {m n : ℕ} (hn : n ≤ m)
    (x : Fin n → Bool) :
    uniformProbability
        (Finset.univ.filter fun bits : Fin m → Bool =>
          (bitBlocks hn bits).1 = x) =
      1 / (2 : ℚ) ^ n :=
  prefix_probability_internal hn x

/-- Retaining a uniform prefix preserves the exact uniform probability of
every finite event on prefixes, not only singleton events. -/
theorem prefix_event_probability {m n : ℕ} (hn : n ≤ m)
    (event : Finset (Fin n → Bool)) :
    uniformProbability
        (Finset.univ.filter fun bits : Fin m → Bool =>
          (bitBlocks hn bits).1 ∈ event) =
      eventProb event :=
  prefix_event_probability_internal hn event

/-- Choosing a split and retaining its prefix gives the uniform average of a
possibly length-dependent family of prefix-event probabilities. -/
theorem split_prefix_event_probability {m : ℕ}
    (event : ∀ n, Finset (Fin n → Bool)) :
    uniformProbability
        (Finset.univ.filter fun seed : (Fin m) × (Fin m → Bool) =>
          (bitBlocks (Nat.le_of_lt seed.1.isLt) seed.2).1 ∈
            event seed.1.val) =
      (1 / (m : ℚ)) * ∑ n : Fin m, eventProb (event n.val) :=
  split_prefix_event_probability_internal event

/-- The joint seed event selecting binary length `n` and fixed prefix `x` has
probability exactly `1 / (m * 2^n)`. -/
theorem split_prefix_probability {m n : ℕ} (hn : n < m)
    (x : Fin n → Bool) :
    uniformProbability
        (Finset.univ.filter fun seed : AuxiliaryUnarySeed m =>
          seed.1.val = n ∧
            (bitBlocks (Nat.le_of_lt hn) seed.2).1 = x) =
      1 / ((m : ℚ) * (2 : ℚ) ^ n) :=
  split_prefix_probability_internal hn x

/-- A seed produces a specified canonical auxiliary-unary pair exactly when it
selects the pair's binary length and binary contents. -/
theorem sample_eq_pair_iff {m n : ℕ} (hn : n < m)
    (x : Fin n → Bool) (seed : AuxiliaryUnarySeed m) :
    seed.sample = pair (List.ofFn x) (List.replicate (m - n) true) ↔
      seed.1.val = n ∧
        (bitBlocks (Nat.le_of_lt hn) seed.2).1 = x :=
  sample_eq_pair_iff_internal hn x seed

end AuxiliaryUnarySeed

namespace FiniteEnsemble

/-- Exact mass of a fixed auxiliary-unary input. For `n < m`, every
`pair x 1^(m-n)` with `|x| = n` has probability `1 / (m * 2^n)`. -/
theorem mass_auxiliaryUnary_pair {m n : ℕ} (hn : n < m)
    (x : Fin n → Bool) :
    auxiliaryUnary.mass m
        (pair (List.ofFn x) (List.replicate (m - n) true)) =
      1 / ((m : ℚ) * (2 : ℚ) ^ n) :=
  mass_auxiliaryUnary_pair_internal hn x

end FiniteEnsemble

end Complexity
