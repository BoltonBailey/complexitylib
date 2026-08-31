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

/-- Eight copies per precision unit separate the two endpoints of a
factor-`16` uncertainty interval after taking roots. -/
theorem relativeCopies_separates_sixteen (precision : ℕ)
    (hprecision : 0 < precision) :
    16 ^ 2 * precision ^ relativeCopies precision ≤
      (precision + 1) ^ relativeCopies precision :=
  relativeCopies_separates_sixteen_internal precision hprecision

/-- Scaling a factor estimate by that factor before taking a floor root gives
a relative estimate whenever the chosen power separates the endpoints. -/
theorem upperRootEstimate_isRelativeApproximation
    {factor copies precision actual weakEstimate : ℕ}
    (hcopies : 0 < copies) (hprecision : 0 < precision)
    (hseparation :
      factor ^ 2 * precision ^ copies ≤ (precision + 1) ^ copies)
    (hweak : IsFactorApproximation factor (actual ^ copies) weakEstimate) :
    IsRelativeApproximation precision actual
      (upperRootEstimate factor copies weakEstimate) :=
  upperRootEstimate_isRelativeApproximation_internal
    hcopies hprecision hseparation hweak

/-- A factor-`16` estimate of the prescribed power yields relative error at
most `1 / precision`, including exact preservation of zero. -/
theorem boostedEstimate_isRelativeApproximation
    {precision actual weakEstimate : ℕ} (hprecision : 0 < precision)
    (hweak : IsFactorApproximation 16
      (actual ^ relativeCopies precision) weakEstimate) :
    IsRelativeApproximation precision actual
      (boostedEstimate precision weakEstimate) :=
  boostedEstimate_isRelativeApproximation_internal hprecision hweak

/-- Applying the factor-to-relative conversion to a Cartesian power recovers
a relative estimate of the original set cardinality. -/
theorem boostedEstimate_cartesianPower_isRelativeApproximation
    {domainWidth precision weakEstimate : ℕ}
    (set : Finset (BitString domainWidth)) (hprecision : 0 < precision)
    (hweak : IsFactorApproximation 16
      (cartesianPower set (relativeCopies precision)).card weakEstimate) :
    IsRelativeApproximation precision set.card
      (boostedEstimate precision weakEstimate) :=
  boostedEstimate_cartesianPower_isRelativeApproximation_internal
    set hprecision hweak

end ApproximateCounting

end Complexity
