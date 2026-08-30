/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.Hashing.Amplification.Defs
import Complexitylib.Classes.Randomized.Hashing.Internal

/-!
# Hash-cell occupancy amplification -- proof internals
-/


public section

namespace Complexity

namespace PairwiseIndependentHash

/-- Internal high-mean amplification theorem. -/
theorem one_sub_two_pow_le_eventProb_majorityNonemptyEvent_internal
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth)
    (errorBits : ℕ) (hmean : 8 ≤ hash.averageCellSize set target) :
    1 - 1 / (2 : ℚ) ^ errorBits ≤
      eventProb (hash.majorityNonemptyEvent set target errorBits) := by
  have hbase : 2 / 3 ≤ eventProb (hash.nonemptyCellEvent set target) :=
    le_trans (by norm_num)
      (hash.seven_eighths_le_eventProb_nonemptyCellEvent_internal
        set target hmean)
  exact eventProb_blockMajority_true_ge_one_sub_two_pow
    seedWidth errorBits (hash.nonemptyCellEvent set target) hbase

/-- Internal low-mean amplification theorem. -/
theorem eventProb_majorityNonemptyEvent_le_two_pow_internal
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth)
    (errorBits : ℕ) (hmean : hash.averageCellSize set target ≤ 1 / 8) :
    eventProb (hash.majorityNonemptyEvent set target errorBits) ≤
      1 / (2 : ℚ) ^ errorBits := by
  have hbase : eventProb (hash.nonemptyCellEvent set target) ≤ 1 / 3 :=
    le_trans
      (hash.eventProb_nonemptyCellEvent_le_one_eighth_internal set target hmean)
      (by norm_num)
  exact eventProb_blockMajority_true_le_two_pow
    seedWidth errorBits (hash.nonemptyCellEvent set target) hbase

end PairwiseIndependentHash

end Complexity
