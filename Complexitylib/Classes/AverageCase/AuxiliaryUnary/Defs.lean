/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.AverageCase.FiniteEnsemble.Defs
public import Complexitylib.Encoding.Pairing

/-!
# The auxiliary-unary distribution -- definitions

For a positive size parameter `m`, Hirahara's auxiliary-unary distribution
chooses a clock length `t` uniformly from `{1, ..., m}`, chooses a uniform
binary string `x` of length `m - t`, and outputs the canonical encoding of
`(x, 1^t)`.

We represent the same experiment by choosing the binary length
`n = m - t` uniformly from `{0, ..., m - 1}` and an independent uniform
`m`-bit string, whose first `n` bits are retained. The unused suffix makes all
split choices live in one uniform finite seed space. At `m = 0`, where the
paper's positive-length distribution is not specified, the totalized ensemble
uses the unique empty seed and outputs `pair [] []`. Here `m` is the sum of the
two component lengths; the self-delimiting binary encoding `pair x 1^t` has its
own codec overhead and need not itself have list length `m`.
-/


@[expose] public section

namespace Complexity

/-- Uniform seed for the `m`th auxiliary-unary slice. The first component is
the retained binary length; the second supplies both the retained prefix and
ignored random suffix. -/
abbrev AuxiliaryUnarySeed (m : ℕ) :=
  Fin (Nat.max 1 m) × (Fin m → Bool)

namespace AuxiliaryUnarySeed

/-- Length of the binary component selected by a seed. -/
def split {m : ℕ} (seed : AuxiliaryUnarySeed m) : ℕ :=
  seed.1.val

/-- Every selected binary length is at most the slice parameter, including the
totalized zero slice. -/
theorem splitLe {m : ℕ} (seed : AuxiliaryUnarySeed m) : seed.split ≤ m := by
  cases m with
  | zero =>
      have hsplit := seed.1.isLt
      simp [split] at hsplit ⊢
  | succ m =>
      have hsplit : seed.1.val < Nat.succ m := by
        simpa using seed.1.isLt
      simp only [split]
      omega

/-- Split an `m`-bit string into a prefix of length `n` and the remaining
suffix, for any certified `n ≤ m`. -/
def bitBlocks {m n : ℕ} (hn : n ≤ m) :
    (Fin m → Bool) ≃ (Fin n → Bool) × (Fin (m - n) → Bool) :=
  (Equiv.arrowCongr
      (finCongr (Nat.add_sub_of_le hn).symm) (Equiv.refl Bool)).trans
    (blockEquiv n (m - n))

/-- Retained random prefix selected by a seed. -/
def binaryBits {m : ℕ} (seed : AuxiliaryUnarySeed m) :
    Fin seed.split → Bool :=
  (bitBlocks seed.splitLe seed.2).1

/-- Retained binary component as a list in increasing index order. -/
def binary {m : ℕ} (seed : AuxiliaryUnarySeed m) : List Bool :=
  List.ofFn seed.binaryBits

/-- Nonempty unary clock at every positive slice. -/
def unary {m : ℕ} (seed : AuxiliaryUnarySeed m) : List Bool :=
  List.replicate (m - seed.split) true

/-- Canonically encoded auxiliary-unary sample. -/
def sample {m : ℕ} (seed : AuxiliaryUnarySeed m) : List Bool :=
  pair seed.binary seed.unary

end AuxiliaryUnarySeed

namespace FiniteEnsemble

/-- Hirahara's uniform distribution with an auxiliary unary input, totalized
at parameter zero. -/
def auxiliaryUnary : FiniteEnsemble (List Bool) where
  Seed := AuxiliaryUnarySeed
  seedFintype _ := inferInstance
  seedDecidableEq _ := inferInstance
  seedNonempty m :=
    ⟨(⟨0, lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 m)⟩,
      fun _ => false)⟩
  sample _ := AuxiliaryUnarySeed.sample

end FiniteEnsemble

end Complexity
