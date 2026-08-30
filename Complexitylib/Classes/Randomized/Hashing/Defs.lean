/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.EventProb
public import Complexitylib.Circuits.BitString

/-!
# Pairwise-independent hashing -- definitions

This module gives the exact finite interface used by Stockmeyer-style
approximate counting. A seed selects a fixed-width hash function. Each input
is uniformly distributed over the range, and the outputs on two distinct
inputs are jointly uniform.
-/


@[expose] public section

namespace Complexity

/-- A fixed-width family of exactly pairwise-independent hash functions,
represented by a uniformly random bit-string seed. -/
structure PairwiseIndependentHash
    (domainWidth rangeWidth seedWidth : ℕ) where
  /-- Evaluate the seeded hash function on one domain element. -/
  eval : BitString seedWidth → BitString domainWidth → BitString rangeWidth
  /-- Every fixed input hashes uniformly to every fixed range element. -/
  uniform : ∀ input output,
    eventProb (Finset.univ.filter fun seed => eval seed input = output) =
      1 / (2 : ℚ) ^ rangeWidth
  /-- Two distinct inputs have jointly uniform hash outputs. -/
  pairwise : ∀ {first second}, first ≠ second → ∀ firstOutput secondOutput,
    eventProb (Finset.univ.filter fun seed =>
      eval seed first = firstOutput ∧ eval seed second = secondOutput) =
        1 / (2 : ℚ) ^ (2 * rangeWidth)

namespace PairwiseIndependentHash

/-- Members of `set` that a seeded hash maps to one target cell. -/
def cell {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth)
    (seed : BitString seedWidth) : Finset (BitString domainWidth) :=
  set.filter fun input => hash.eval seed input = target

/-- Number of set members in one seeded target cell. -/
def cellSize {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth)
    (seed : BitString seedWidth) : ℕ :=
  (hash.cell set target seed).card

/-- Uniform rational average of the target-cell size over every seed. -/
def averageCellSize {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth) : ℚ :=
  (∑ seed : BitString seedWidth, (hash.cellSize set target seed : ℚ)) /
    (2 : ℚ) ^ seedWidth

end PairwiseIndependentHash

end Complexity
