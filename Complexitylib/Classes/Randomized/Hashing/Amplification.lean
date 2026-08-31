/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.Hashing.Amplification.Defs
import Complexitylib.Classes.Randomized.Hashing.Amplification.Internal

/-!
# Hash-cell occupancy amplification

This module transfers the constant one-hash occupancy gap to exponentially
small error using strict majority over independent affine-hash seeds.
-/


public section

namespace Complexity

namespace PairwiseIndependentHash

/-- A seed belongs to the amplified positive event exactly when the occupancy
test returns true. -/
theorem mem_majorityNonemptyEvent_iff
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth)
    (errorBits : ℕ) (seed : BitString (majoritySeedWidth seedWidth errorBits)) :
    seed ∈ hash.majorityNonemptyEvent set target errorBits ↔
      hash.majorityNonempty set target errorBits seed = true :=
  hash.mem_majorityNonemptyEvent_iff_internal set target errorBits seed

/-- A seed belongs to the amplified negative event exactly when the occupancy
test returns false. -/
theorem mem_majorityEmptyEvent_iff
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth)
    (errorBits : ℕ) (seed : BitString (majoritySeedWidth seedWidth errorBits)) :
    seed ∈ hash.majorityEmptyEvent set target errorBits ↔
      hash.majorityNonempty set target errorBits seed = false :=
  hash.mem_majorityEmptyEvent_iff_internal set target errorBits seed

/-- Seeds returning false are the complement of seeds returning true. -/
theorem majorityEmptyEvent_eq_compl_majorityNonemptyEvent
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth)
    (errorBits : ℕ) :
    hash.majorityEmptyEvent set target errorBits =
      (hash.majorityNonemptyEvent set target errorBits)ᶜ :=
  hash.majorityEmptyEvent_eq_compl_majorityNonemptyEvent_internal
    set target errorBits

/-- If the mean target-cell size is at least `8`, the amplified occupancy test
returns true with probability at least `1 - 2^-errorBits`. -/
theorem one_sub_two_pow_le_eventProb_majorityNonemptyEvent
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth)
    (errorBits : ℕ) (hmean : 8 ≤ hash.averageCellSize set target) :
    1 - 1 / (2 : ℚ) ^ errorBits ≤
      eventProb (hash.majorityNonemptyEvent set target errorBits) :=
  hash.one_sub_two_pow_le_eventProb_majorityNonemptyEvent_internal
    set target errorBits hmean

/-- If the mean target-cell size is at least `8`, the amplified occupancy test
returns false with probability at most `2^-errorBits`. -/
theorem eventProb_majorityEmptyEvent_le_two_pow
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth)
    (errorBits : ℕ) (hmean : 8 ≤ hash.averageCellSize set target) :
    eventProb (hash.majorityEmptyEvent set target errorBits) ≤
      1 / (2 : ℚ) ^ errorBits :=
  hash.eventProb_majorityEmptyEvent_le_two_pow_internal
    set target errorBits hmean

/-- If the mean target-cell size is at most `1/8`, the amplified occupancy test
returns true with probability at most `2^-errorBits`. -/
theorem eventProb_majorityNonemptyEvent_le_two_pow
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth)
    (errorBits : ℕ) (hmean : hash.averageCellSize set target ≤ 1 / 8) :
    eventProb (hash.majorityNonemptyEvent set target errorBits) ≤
      1 / (2 : ℚ) ^ errorBits :=
  hash.eventProb_majorityNonemptyEvent_le_two_pow_internal
    set target errorBits hmean

end PairwiseIndependentHash

end Complexity
