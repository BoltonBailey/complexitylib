/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.Hashing.Affine.Circuit.Defs
public import
  Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.HashCell.Circuit.Defs

/-!
# Affine hash-cell circuit fragments -- definitions

This module specializes the generic affine-zero compiler to the packed input
layout of anti-checker hash-cell predicates. The labeled samples precede the
row-major affine seed, and the powered-survivor witness occupies the final
primary-input block.
-/


@[expose] public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

namespace HashCellAffineCircuit

/-- First wire of the affine seed inside the public hash-cell prefix. -/
def seedBase (arity prefixLength : ℕ) : ℕ :=
  counterInputWidth arity prefixLength

/-- Primary-input wire carrying one row-major affine coefficient. -/
def coefficientRef (beta : PositiveRationalScale)
    (arity prefixLength rangeWidth : ℕ) (row : Fin rangeWidth)
    (coordinate : Fin (counterSurvivorPowerWidth beta arity + 1)) : ℕ :=
  seedBase arity prefixLength + (finProdFinEquiv (row, coordinate)).val

/-- First wire of the powered-survivor witness after the public prefix. -/
def witnessBase (beta : PositiveRationalScale)
    (arity prefixLength rangeWidth : ℕ) : ℕ :=
  hashCellPublicWidth beta arity prefixLength rangeWidth

/-- Primary-input wire carrying one powered-survivor coordinate. -/
def witnessRef (beta : PositiveRationalScale)
    (arity prefixLength rangeWidth : ℕ)
    (coordinate : Fin (counterSurvivorPowerWidth beta arity)) : ℕ :=
  witnessBase beta arity prefixLength rangeWidth + coordinate.val

/-- Raw affine-zero fragment over the packed hash-cell primary inputs. -/
def compileRaw (beta : PositiveRationalScale)
    (arity prefixLength rangeWidth : ℕ) : CircuitCode.RawCircuit :=
  PairwiseIndependentHash.AffineCircuit.compileZeroRaw
    (hashCellPredicateInputWidth beta arity prefixLength rangeWidth)
    (counterSurvivorPowerWidth beta arity) rangeWidth
    (coefficientRef beta arity prefixLength rangeWidth)
    (witnessRef beta arity prefixLength rangeWidth)

/-- Exact number of gates in the specialized affine-zero fragment. -/
def gateCount (beta : PositiveRationalScale) (arity rangeWidth : ℕ) : ℕ :=
  PairwiseIndependentHash.AffineCircuit.zeroGateCount
    (counterSurvivorPowerWidth beta arity) rangeWidth

/-- Absolute wire carrying the specialized affine-zero decision. -/
def outputWire (beta : PositiveRationalScale)
    (arity prefixLength rangeWidth : ℕ) : ℕ :=
  PairwiseIndependentHash.AffineCircuit.zeroOutputWire
    (hashCellPredicateInputWidth beta arity prefixLength rangeWidth)
    (counterSurvivorPowerWidth beta arity) rangeWidth

end HashCellAffineCircuit

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
