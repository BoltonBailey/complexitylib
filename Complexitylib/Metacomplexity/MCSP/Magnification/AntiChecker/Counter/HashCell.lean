/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.HashCell.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.HashCell.Circuit
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.HashCell.Internal

/-!
# Hashed anti-checker survivor cells

This module identifies the existential query used by every amplified
occupancy probe with the generic affine-hash cell semantics.
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- The anti-checker hash-cell predicate is exactly nonemptiness of the
corresponding generic affine zero cell. -/
theorem hashCellNonempty_iff_cellNonempty
    {count arity threshold precision rangeWidth : ℕ}
    (input : BitString (count * (arity + 1)))
    (seed : BitString (PairwiseIndependentHash.affineSeedWidth
      (survivorPowerWidth arity threshold precision) rangeWidth)) :
    HashCellNonempty arity threshold precision rangeWidth input seed ↔
      ((PairwiseIndependentHash.affine
          (survivorPowerWidth arity threshold precision) rangeWidth).cell
        (ApproximateCounting.cartesianPower
          (encodedSurvivorSet arity threshold input)
          (ApproximateCounting.relativeCopies precision))
        (fun _ => false) seed).Nonempty :=
  hashCellNonempty_iff_cellNonempty_internal input seed

/-- Equivalently, the generic affine zero-cell cardinality is positive. -/
theorem hashCellNonempty_iff_cellSize_pos
    {count arity threshold precision rangeWidth : ℕ}
    (input : BitString (count * (arity + 1)))
    (seed : BitString (PairwiseIndependentHash.affineSeedWidth
      (survivorPowerWidth arity threshold precision) rangeWidth)) :
    HashCellNonempty arity threshold precision rangeWidth input seed ↔
      0 < (PairwiseIndependentHash.affine
          (survivorPowerWidth arity threshold precision) rangeWidth).cellSize
        (ApproximateCounting.cartesianPower
          (encodedSurvivorSet arity threshold input)
          (ApproximateCounting.relativeCopies precision))
        (fun _ => false) seed :=
  hashCellNonempty_iff_cellSize_pos_internal input seed

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
