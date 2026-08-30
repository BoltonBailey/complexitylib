/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.Hashing.Defs

/-!
# Hash-cell occupancy amplification -- definitions

An amplified occupancy test draws an odd number of independent hash seeds and
returns the strict majority of the corresponding nonempty-cell answers.
-/


@[expose] public section

namespace Complexity

namespace PairwiseIndependentHash

/-- Number of random bits used to amplify one `seedWidth`-bit occupancy test to
error at most `2^-errorBits`. -/
def majoritySeedWidth (seedWidth errorBits : ℕ) : ℕ :=
  (12 * errorBits + 1) * seedWidth

/-- Strict majority of independent target-cell nonemptiness tests. -/
def majorityNonempty {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth)
    (errorBits : ℕ) (seed : BitString (majoritySeedWidth seedWidth errorBits)) : Bool :=
  blockMajority (hash.nonemptyCellEvent set target) seed

/-- Seeds on which the amplified target-cell occupancy test returns true. -/
def majorityNonemptyEvent {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth)
    (errorBits : ℕ) : Finset (BitString (majoritySeedWidth seedWidth errorBits)) :=
  Finset.univ.filter fun seed =>
    hash.majorityNonempty set target errorBits seed = true

end PairwiseIndependentHash

end Complexity
