/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.Hashing.Defs

/-!
# Pairwise-independent hashing -- proof internals
-/


public section

namespace Complexity

namespace PairwiseIndependentHash

/-- Internal double-counting identity for total target-cell mass. -/
private theorem sum_cellSize_eq_sum_fiberCard
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth) :
    ∑ seed : BitString seedWidth, (hash.cellSize set target seed : ℚ) =
      ∑ input ∈ set,
        ((Finset.univ.filter fun seed : BitString seedWidth =>
          hash.eval seed input = target).card : ℚ) := by
  classical
  simp only [cellSize, cell, Finset.card_filter]
  push_cast
  rw [Finset.sum_comm]

/-- Internal first-moment identity for one hash cell. -/
theorem averageCellSize_eq_internal
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth) :
    hash.averageCellSize set target =
      (set.card : ℚ) / (2 : ℚ) ^ rangeWidth := by
  classical
  rw [averageCellSize, sum_cellSize_eq_sum_fiberCard, Finset.sum_div]
  calc
    ∑ input ∈ set,
        (Finset.univ.filter fun seed : BitString seedWidth =>
          hash.eval seed input = target).card / (2 : ℚ) ^ seedWidth =
        ∑ _input ∈ set, 1 / (2 : ℚ) ^ rangeWidth := by
          apply Finset.sum_congr rfl
          intro input _
          exact hash.uniform input target
    _ = (set.card : ℚ) * (1 / (2 : ℚ) ^ rangeWidth) := by simp
    _ = (set.card : ℚ) / (2 : ℚ) ^ rangeWidth := by ring

end PairwiseIndependentHash

end Complexity
