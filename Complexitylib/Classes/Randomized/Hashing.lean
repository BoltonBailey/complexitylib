/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.Hashing.Defs
import Complexitylib.Classes.Randomized.Hashing.Internal

/-!
# Pairwise-independent hashing

This module exposes the first two exact finite moments behind Stockmeyer
counting. They imply the variance bound used by the hashing lemma.
-/


public section

namespace Complexity

namespace PairwiseIndependentHash

/-- The average size of a fixed target cell is exactly `|set| / 2^rangeWidth`. -/
theorem averageCellSize_eq
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth) :
    hash.averageCellSize set target =
      (set.card : ℚ) / (2 : ℚ) ^ rangeWidth :=
  hash.averageCellSize_eq_internal set target

/-- The average number of ordered distinct pairs in one target cell is
`(|set|² - |set|) / 2^(2 * rangeWidth)`. -/
theorem averageOrderedPairCellSize_eq
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth) :
    hash.averageOrderedPairCellSize set target =
      ((set.card * set.card - set.card : ℕ) : ℚ) /
        (2 : ℚ) ^ (2 * rangeWidth) :=
  hash.averageOrderedPairCellSize_eq_internal set target

/-- The ordered distinct-pair count in a cell is its size times one less than
its size. -/
theorem orderedPairCellSize_eq
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth)
    (seed : BitString seedWidth) :
    hash.orderedPairCellSize set target seed =
      hash.cellSize set target seed * hash.cellSize set target seed -
        hash.cellSize set target seed :=
  hash.orderedPairCellSize_eq_internal set target seed

/-- The second moment is the sum of the first and second factorial moments. -/
theorem averageCellSizeSquare_eq_add
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth) :
    hash.averageCellSizeSquare set target =
      hash.averageCellSize set target +
        hash.averageOrderedPairCellSize set target :=
  hash.averageCellSizeSquare_eq_add_internal set target

/-- Exact second moment of the size of one target cell. -/
theorem averageCellSizeSquare_eq
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth) :
    hash.averageCellSizeSquare set target =
      (set.card : ℚ) / (2 : ℚ) ^ rangeWidth +
        ((set.card * set.card - set.card : ℕ) : ℚ) /
          (2 : ℚ) ^ (2 * rangeWidth) :=
  hash.averageCellSizeSquare_eq_internal set target

end PairwiseIndependentHash

end Complexity
