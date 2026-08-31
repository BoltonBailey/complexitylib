/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.HashCell.Circuit.Affine.Defs
import
Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.HashCell.Circuit.Affine.Internal

/-!
# Affine hash-cell circuit fragments

The specialized raw fragment reads affine coefficients and a powered-survivor
witness directly from the canonical hash-cell input layout, and accepts exactly
when the affine hash of that witness is zero.
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

namespace HashCellAffineCircuit

/-- The specialized affine-zero fragment has its advertised exact size. -/
@[simp] theorem length_compileRaw (beta : PositiveRationalScale)
    (arity prefixLength rangeWidth : ℕ) :
    (compileRaw beta arity prefixLength rangeWidth).length =
      gateCount beta arity rangeWidth :=
  length_compileRaw_internal beta arity prefixLength rangeWidth

/-- The last emitted gate carries the specialized affine-zero decision. -/
theorem outputWire_eq (beta : PositiveRationalScale)
    (arity prefixLength rangeWidth : ℕ) :
    outputWire beta arity prefixLength rangeWidth =
      hashCellPredicateInputWidth beta arity prefixLength rangeWidth +
        (compileRaw beta arity prefixLength rangeWidth).length - 1 :=
  outputWire_eq_internal beta arity prefixLength rangeWidth

/-- Every specialized affine-zero fragment is a valid raw circuit extension. -/
theorem compileRaw_wellFormed (beta : PositiveRationalScale)
    (arity prefixLength rangeWidth : ℕ) :
    CircuitCode.RawCircuit.WellFormed
      (hashCellPredicateInputWidth beta arity prefixLength rangeWidth)
      (compileRaw beta arity prefixLength rangeWidth) :=
  compileRaw_wellFormed_internal beta arity prefixLength rangeWidth

/-- The specialized fragment accepts exactly when the packed seed sends the
powered-survivor witness to zero. -/
theorem eval?_compileRaw (beta : PositiveRationalScale)
    {arity prefixLength rangeWidth : ℕ}
    (input : BitString (counterInputWidth arity prefixLength))
    (seed : BitString (PairwiseIndependentHash.affineSeedWidth
      (counterSurvivorPowerWidth beta arity) rangeWidth))
    (witness : BitString (counterSurvivorPowerWidth beta arity)) :
    CircuitCode.RawCircuit.eval? (compileRaw beta arity prefixLength rangeWidth)
        (BitString.toList
          (Fin.append (hashCellPublicInput beta input seed) witness)) =
      some (decide (PairwiseIndependentHash.affineEval seed witness =
        fun _ => false)) :=
  eval?_compileRaw_internal beta input seed witness

end HashCellAffineCircuit

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
