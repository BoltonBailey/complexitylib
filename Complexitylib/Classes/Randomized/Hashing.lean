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

This module exposes the first exact finite moment behind Stockmeyer counting:
the average size of a fixed hash cell is the source-set size divided by the
hash range size.
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

end PairwiseIndependentHash

end Complexity
