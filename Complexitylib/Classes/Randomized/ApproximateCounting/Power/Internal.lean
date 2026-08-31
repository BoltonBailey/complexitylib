/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.ApproximateCounting.Power.Defs

/-!
# Cartesian powers for approximate counting -- proof internals
-/


public section

namespace Complexity

namespace ApproximateCounting

theorem mem_cartesianPower_iff_internal {domainWidth copies : ℕ}
    {set : Finset (BitString domainWidth)}
    {input : BitString (copies * domainWidth)} :
    input ∈ cartesianPower set copies ↔
      ∀ copy, blocksEquiv copies domainWidth input copy ∈ set := by
  classical
  simp [cartesianPower]

theorem card_cartesianPower_internal {domainWidth : ℕ}
    (set : Finset (BitString domainWidth)) (copies : ℕ) :
    (cartesianPower set copies).card = set.card ^ copies := by
  classical
  simp [cartesianPower]

end ApproximateCounting

end Complexity
