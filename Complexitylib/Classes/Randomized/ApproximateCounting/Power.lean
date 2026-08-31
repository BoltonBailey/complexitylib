/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.ApproximateCounting.Power.Defs
import Complexitylib.Classes.Randomized.ApproximateCounting.Power.Internal

/-!
# Cartesian powers for approximate counting

The row-major encoding preserves both membership and the exact power-law
cardinality required by Stockmeyer's accuracy amplification.
-/


public section

namespace Complexity

namespace ApproximateCounting

/-- A packed string belongs to the Cartesian power exactly when every decoded
block belongs to the original set. -/
theorem mem_cartesianPower_iff {domainWidth copies : ℕ}
    {set : Finset (BitString domainWidth)}
    {input : BitString (copies * domainWidth)} :
    input ∈ cartesianPower set copies ↔
      ∀ copy, blocksEquiv copies domainWidth input copy ∈ set :=
  mem_cartesianPower_iff_internal

/-- The `copies`-fold Cartesian power has cardinality `|set| ^ copies`. -/
theorem card_cartesianPower {domainWidth : ℕ}
    (set : Finset (BitString domainWidth)) (copies : ℕ) :
    (cartesianPower set copies).card = set.card ^ copies :=
  card_cartesianPower_internal set copies

end ApproximateCounting

end Complexity
