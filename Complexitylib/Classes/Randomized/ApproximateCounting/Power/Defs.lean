/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.ApproximateCounting.Defs
public import Complexitylib.Classes.FiniteCounting
public import Complexitylib.Circuits.BitString
public import Mathlib.Data.Nat.NthRoot.Defs

/-!
# Cartesian powers for approximate counting -- definitions

The accuracy boost in Stockmeyer's approximate counter applies a weak counter
to a Cartesian power of the original finite set. This module fixes the
row-major bit-string representation of that power.
-/


@[expose] public section

namespace Complexity

namespace ApproximateCounting

/-- The `copies`-fold Cartesian power of a set of fixed-width bit strings,
encoded as one row-major bit string. -/
def cartesianPower {domainWidth : ℕ}
    (set : Finset (BitString domainWidth)) (copies : ℕ) :
    Finset (BitString (copies * domainWidth)) :=
  (Fintype.piFinset fun _ : Fin copies => set).map
    (blocksEquiv copies domainWidth).symm.toEmbedding

/-- Number of Cartesian copies used to turn factor-`16` accuracy into relative
error `1 / precision`. -/
def relativeCopies (precision : ℕ) : ℕ :=
  8 * precision

/-- Integer recovery from a factor estimate of a power. Multiplying by the
factor before taking the floor root chooses the upper endpoint of the possible
count interval and therefore avoids downward rounding error. -/
def upperRootEstimate (factor copies weakEstimate : ℕ) : ℕ :=
  Nat.nthRoot copies (factor * weakEstimate)

/-- Relative estimate recovered from a factor-`16` estimate of the prescribed
Cartesian power. -/
def boostedEstimate (precision weakEstimate : ℕ) : ℕ :=
  upperRootEstimate 16 (relativeCopies precision) weakEstimate

end ApproximateCounting

end Complexity
