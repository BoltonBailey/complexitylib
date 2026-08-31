/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.HashCell.Circuit.Affine.Defs
import Complexitylib.Classes.Randomized.Hashing.Affine.Circuit

/-!
# Affine hash-cell circuit fragments -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

namespace HashCellAffineCircuit

theorem length_compileRaw_internal (beta : PositiveRationalScale)
    (arity prefixLength rangeWidth : ℕ) :
    (compileRaw beta arity prefixLength rangeWidth).length =
      gateCount beta arity rangeWidth := by
  simp [compileRaw, gateCount,
    PairwiseIndependentHash.AffineCircuit.length_compileZeroRaw]

theorem outputWire_eq_internal (beta : PositiveRationalScale)
    (arity prefixLength rangeWidth : ℕ) :
    outputWire beta arity prefixLength rangeWidth =
      hashCellPredicateInputWidth beta arity prefixLength rangeWidth +
        (compileRaw beta arity prefixLength rangeWidth).length - 1 := by
  exact PairwiseIndependentHash.AffineCircuit.zeroOutputWire_eq
    (hashCellPredicateInputWidth beta arity prefixLength rangeWidth)
    (counterSurvivorPowerWidth beta arity) rangeWidth
    (coefficientRef beta arity prefixLength rangeWidth)
    (witnessRef beta arity prefixLength rangeWidth)

private theorem coefficientRef_lt (beta : PositiveRationalScale)
    (arity prefixLength rangeWidth : ℕ) (row : Fin rangeWidth)
    (coordinate : Fin (counterSurvivorPowerWidth beta arity + 1)) :
    coefficientRef beta arity prefixLength rangeWidth row coordinate <
      hashCellPredicateInputWidth beta arity prefixLength rangeWidth := by
  have hcoordinate := (finProdFinEquiv (row, coordinate)).isLt
  simp only [coefficientRef, seedBase, hashCellPredicateInputWidth,
    hashCellPublicWidth, PairwiseIndependentHash.affineSeedWidth]
  omega

private theorem witnessRef_lt (beta : PositiveRationalScale)
    (arity prefixLength rangeWidth : ℕ)
    (coordinate : Fin (counterSurvivorPowerWidth beta arity)) :
    witnessRef beta arity prefixLength rangeWidth coordinate <
      hashCellPredicateInputWidth beta arity prefixLength rangeWidth := by
  simp only [witnessRef, witnessBase, hashCellPredicateInputWidth]
  omega

private theorem packed_coefficient
    (beta : PositiveRationalScale) {arity prefixLength rangeWidth : ℕ}
    (input : BitString (counterInputWidth arity prefixLength))
    (seed : BitString (PairwiseIndependentHash.affineSeedWidth
      (counterSurvivorPowerWidth beta arity) rangeWidth))
    (witness : BitString (counterSurvivorPowerWidth beta arity))
    (row : Fin rangeWidth)
    (coordinate : Fin (counterSurvivorPowerWidth beta arity + 1)) :
    (Fin.append (hashCellPublicInput beta input seed) witness)
        ⟨coefficientRef beta arity prefixLength rangeWidth row coordinate,
          coefficientRef_lt beta arity prefixLength rangeWidth row coordinate⟩ =
      PairwiseIndependentHash.affineRows seed row coordinate := by
  let flat : Fin (PairwiseIndependentHash.affineSeedWidth
      (counterSurvivorPowerWidth beta arity) rangeWidth) :=
    ⟨(finProdFinEquiv (row, coordinate)).val, by
      simpa only [PairwiseIndependentHash.affineSeedWidth] using
        (finProdFinEquiv (row, coordinate)).isLt⟩
  have hpublic :
      coefficientRef beta arity prefixLength rangeWidth row coordinate <
        hashCellPublicWidth beta arity prefixLength rangeWidth := by
    have hflat := flat.isLt
    simp only [coefficientRef, seedBase, hashCellPublicWidth,
      PairwiseIndependentHash.affineSeedWidth]
    omega
  change
    Fin.append (hashCellPublicInput beta input seed) witness
        (Fin.castAdd (counterSurvivorPowerWidth beta arity)
          ⟨coefficientRef beta arity prefixLength rangeWidth row coordinate,
            hpublic⟩) =
      PairwiseIndependentHash.affineRows seed row coordinate
  rw [Fin.append_left]
  have hinner :
      (⟨coefficientRef beta arity prefixLength rangeWidth row coordinate,
          hpublic⟩ :
        Fin (hashCellPublicWidth beta arity prefixLength rangeWidth)) =
      Fin.natAdd (counterInputWidth arity prefixLength) flat := by
    apply Fin.ext
    rfl
  rw [hashCellPublicInput, hinner, Fin.append_right]
  apply congrArg seed
  apply Fin.ext
  rfl

private theorem packed_witness
    (beta : PositiveRationalScale) {arity prefixLength rangeWidth : ℕ}
    (input : BitString (counterInputWidth arity prefixLength))
    (seed : BitString (PairwiseIndependentHash.affineSeedWidth
      (counterSurvivorPowerWidth beta arity) rangeWidth))
    (witness : BitString (counterSurvivorPowerWidth beta arity))
    (coordinate : Fin (counterSurvivorPowerWidth beta arity)) :
    (Fin.append (hashCellPublicInput beta input seed) witness)
        ⟨witnessRef beta arity prefixLength rangeWidth coordinate,
          witnessRef_lt beta arity prefixLength rangeWidth coordinate⟩ =
      witness coordinate := by
  change
    Fin.append (hashCellPublicInput beta input seed) witness
        (Fin.natAdd (hashCellPublicWidth beta arity prefixLength rangeWidth)
          coordinate) = witness coordinate
  rw [Fin.append_right]

theorem compileRaw_wellFormed_internal (beta : PositiveRationalScale)
    (arity prefixLength rangeWidth : ℕ) :
    CircuitCode.RawCircuit.WellFormed
      (hashCellPredicateInputWidth beta arity prefixLength rangeWidth)
      (compileRaw beta arity prefixLength rangeWidth) := by
  apply PairwiseIndependentHash.AffineCircuit.compileZeroRaw_wellFormed
  · exact coefficientRef_lt beta arity prefixLength rangeWidth
  · exact witnessRef_lt beta arity prefixLength rangeWidth

theorem eval?_compileRaw_internal (beta : PositiveRationalScale)
    {arity prefixLength rangeWidth : ℕ}
    (input : BitString (counterInputWidth arity prefixLength))
    (seed : BitString (PairwiseIndependentHash.affineSeedWidth
      (counterSurvivorPowerWidth beta arity) rangeWidth))
    (witness : BitString (counterSurvivorPowerWidth beta arity)) :
    CircuitCode.RawCircuit.eval? (compileRaw beta arity prefixLength rangeWidth)
        (BitString.toList
          (Fin.append (hashCellPublicInput beta input seed) witness)) =
      some (decide (PairwiseIndependentHash.affineEval seed witness =
        fun _ => false)) := by
  let packed : BitString
      (hashCellPredicateInputWidth beta arity prefixLength rangeWidth) :=
    Fin.append (hashCellPublicInput beta input seed) witness
  rw [compileRaw]
  change
    CircuitCode.RawCircuit.eval?
        (PairwiseIndependentHash.AffineCircuit.compileZeroRaw
          (hashCellPredicateInputWidth beta arity prefixLength rangeWidth)
          (counterSurvivorPowerWidth beta arity) rangeWidth
          (coefficientRef beta arity prefixLength rangeWidth)
          (witnessRef beta arity prefixLength rangeWidth)) packed.toList = _
  rw [PairwiseIndependentHash.AffineCircuit.eval?_compileZeroRaw
    (hashCellPredicateInputWidth beta arity prefixLength rangeWidth)
    (counterSurvivorPowerWidth beta arity) rangeWidth
    (coefficientRef beta arity prefixLength rangeWidth)
    (witnessRef beta arity prefixLength rangeWidth)
    (coefficientRef_lt beta arity prefixLength rangeWidth)
    (witnessRef_lt beta arity prefixLength rangeWidth) packed]
  apply congrArg some
  rw [← PairwiseIndependentHash.AffineCircuit.zeroValue_affineEval seed witness]
  apply congrArg PairwiseIndependentHash.AffineCircuit.zeroValue
  funext row
  have hcoefficients :
      (fun coordinate : Fin (counterSurvivorPowerWidth beta arity) =>
        packed
          ⟨coefficientRef beta arity prefixLength rangeWidth row
              coordinate.castSucc,
            coefficientRef_lt beta arity prefixLength rangeWidth row
              coordinate.castSucc⟩) =
        fun coordinate =>
          PairwiseIndependentHash.affineRows seed row coordinate.castSucc := by
    funext coordinate
    dsimp only [packed]
    exact packed_coefficient beta input seed witness row coordinate.castSucc
  have hinput :
      (fun coordinate : Fin (counterSurvivorPowerWidth beta arity) =>
        packed ⟨witnessRef beta arity prefixLength rangeWidth coordinate,
          witnessRef_lt beta arity prefixLength rangeWidth coordinate⟩) =
        witness := by
    funext coordinate
    dsimp only [packed]
    exact packed_witness beta input seed witness coordinate
  have hconstant :
      packed
          ⟨coefficientRef beta arity prefixLength rangeWidth row
              (Fin.last (counterSurvivorPowerWidth beta arity)),
            coefficientRef_lt beta arity prefixLength rangeWidth row
              (Fin.last (counterSurvivorPowerWidth beta arity))⟩ =
        PairwiseIndependentHash.affineRows seed row
          (Fin.last (counterSurvivorPowerWidth beta arity)) := by
    dsimp only [packed]
    exact packed_coefficient beta input seed witness row
      (Fin.last (counterSurvivorPowerWidth beta arity))
  rw [hcoefficients, hinput, hconstant]

end HashCellAffineCircuit

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
