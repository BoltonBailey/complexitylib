/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Defs
import Complexitylib.Metacomplexity.NisanWigderson.Hardwiring.Internal
import Complexitylib.Metacomplexity.NisanWigderson.Internal
import Complexitylib.Metacomplexity.StatisticalTest.HybridPrediction.Internal

/-!
# Nisan--Wigderson fixed-advice reconstruction -- proof internals
-/


public section

namespace Complexity

namespace NWDesign

private theorem blockAppend_natAdd_internal
    {seedLength outputLength : ℕ}
    (seed : Fin seedLength → Bool) (tail : Fin outputLength → Bool)
    (coordinate : Fin outputLength) :
    blockAppend seedLength outputLength seed tail
        (Fin.natAdd seedLength coordinate) = tail coordinate := by
  have happ := congrFun
    (blockSnd_append seedLength outputLength seed tail) coordinate
  rw [blockSnd_apply] at happ
  exact happ

theorem card_outsideCoordinates_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    (design.outsideCoordinates current).card = seedLength - inputLength := by
  rw [outsideCoordinates, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp [card_support_internal]

theorem card_laterCoordinates_internal {outputLength : ℕ}
    (current : Fin outputLength) :
    (laterCoordinates current).card = outputLength - (current.val + 1) := by
  simp [laterCoordinates]
  omega

theorem card_outsideAssignments_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    Fintype.card (design.outsideCoordinates current → Bool) =
      2 ^ (seedLength - inputLength) := by
  simp [card_outsideCoordinates_internal]

theorem card_laterAssignments_internal {outputLength : ℕ}
    (current : Fin outputLength) :
    Fintype.card (laterCoordinates current → Bool) =
      2 ^ (outputLength - (current.val + 1)) := by
  simp [card_laterCoordinates_internal]

theorem reconstructionSeed_apply_coordinates_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength)
    (outside : design.outsideCoordinates current → Bool)
    (challenge : Fin inputLength → Bool) (input : Fin inputLength) :
    design.reconstructionSeed current outside challenge
        (design.coordinates current input) =
      challenge input := by
  exact seedWithChallenge_apply_coordinates_internal design current
    (design.outsideSeed current outside) challenge input

theorem reconstructionSeed_apply_outside_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength)
    (outside : design.outsideCoordinates current → Bool)
    (challenge : Fin inputLength → Bool)
    (coordinate : design.outsideCoordinates current) :
    design.reconstructionSeed current outside challenge coordinate =
      outside coordinate := by
  have hcoordinate : coordinate.val ∉ design.support current := by
    exact (Finset.mem_sdiff.mp coordinate.property).2
  calc
    design.reconstructionSeed current outside challenge coordinate =
        design.outsideSeed current outside coordinate :=
      seedWithChallenge_apply_of_not_mem_support_internal design current
        (design.outsideSeed current outside) challenge coordinate hcoordinate
    _ = outside coordinate := by
      simp [outsideSeed, BooleanDependency.extendByFalse,
        coordinate.property]

theorem reconstructionSeed_restrict_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) (seed : Fin seedLength → Bool) :
    design.reconstructionSeed current
        (BooleanDependency.restrict
          (design.outsideCoordinates current) seed)
        (design.restrictSeed current seed) =
      seed := by
  funext coordinate
  by_cases hcoordinate : coordinate ∈ design.support current
  · obtain ⟨input, rfl⟩ :=
      (mem_support_iff_internal design current coordinate).mp hcoordinate
    simp [reconstructionSeed_apply_coordinates_internal, restrictSeed]
  · let outsideCoordinate : design.outsideCoordinates current :=
      ⟨coordinate, by simp [outsideCoordinates, hcoordinate]⟩
    simpa [outsideCoordinate, BooleanDependency.restrict] using
      reconstructionSeed_apply_outside_internal design current
        (BooleanDependency.restrict
          (design.outsideCoordinates current) seed)
        (design.restrictSeed current seed) outsideCoordinate

theorem reconstructionBackground_targetBit_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (current : Fin outputLength)
    (outside : design.outsideCoordinates current → Bool)
    (later : laterCoordinates current → Bool)
    (challenge : Fin inputLength → Bool) :
    (design.generator hardFunction).targetBit current
        (design.reconstructionBackground current outside later challenge) =
      hardFunction challenge := by
  simp only [BitGenerator.targetBit, generator, reconstructionBackground]
  apply congrArg hardFunction
  funext input
  exact reconstructionSeed_apply_coordinates_internal
    design current outside challenge input

theorem reconstructionQuery_eq_hybridOutput_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (current : Fin outputLength)
    (outside : design.outsideCoordinates current → Bool)
    (later : laterCoordinates current → Bool)
    (challenge : Fin inputLength → Bool) (candidate : Bool) :
    design.reconstructionQuery hardFunction current outside later
        challenge candidate =
      (design.generator hardFunction).hybridOutput current.val
        (BitGenerator.assembleCandidate
          (design.reconstructionBackground current outside later challenge)
          candidate) := by
  funext output
  by_cases hbefore : output.val < current.val
  · simp [reconstructionQuery, hbefore, BitGenerator.hybridOutput,
      BitGenerator.assembleCandidate, reconstructionBackground,
      reconstructionSeed, generator, challengedBlock,
      predecessorTable_restrict_internal]
  · simp [reconstructionQuery, hbefore, BitGenerator.hybridOutput,
      BitGenerator.assembleCandidate, reconstructionBackground,
      blockAppend_natAdd_internal]

theorem reconstructionTestAtCandidate_eq_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength)
    (outside : design.outsideCoordinates current → Bool)
    (later : laterCoordinates current → Bool)
    (challenge : Fin inputLength → Bool) (candidate : Bool) :
    design.reconstructionTestAtCandidate hardFunction test current outside
        later challenge candidate =
      (design.generator hardFunction).testAtCandidate test current
        (design.reconstructionBackground current outside later challenge)
        candidate := by
  simp only [reconstructionTestAtCandidate, BitGenerator.testAtCandidate]
  rw [reconstructionQuery_eq_hybridOutput_internal]

theorem reconstructionPredictor_eq_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength)
    (outside : design.outsideCoordinates current → Bool)
    (later : laterCoordinates current → Bool) (candidate : Bool)
    (challenge : Fin inputLength → Bool) :
    design.reconstructionPredictor hardFunction test current outside later
        candidate challenge =
      NextBitPrediction.predictFromTest
        ((design.generator hardFunction).testAtCandidate test current
          (design.reconstructionBackground current outside later challenge)
          candidate)
        candidate := by
  rw [reconstructionPredictor,
    reconstructionTestAtCandidate_eq_internal]

theorem reconstructionPredictor_agrees_iff_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength)
    (outside : design.outsideCoordinates current → Bool)
    (later : laterCoordinates current → Bool) (candidate : Bool)
    (challenge : Fin inputLength → Bool) :
    design.reconstructionPredictor hardFunction test current outside later
        candidate challenge = hardFunction challenge ↔
      NextBitPrediction.predictFromTest
          ((design.generator hardFunction).testAtCandidate test current
            (design.reconstructionBackground current outside later challenge)
            candidate)
          candidate =
        (design.generator hardFunction).targetBit current
          (design.reconstructionBackground current outside later challenge) := by
  rw [reconstructionPredictor_eq_internal,
    reconstructionBackground_targetBit_internal]

theorem reconstructionDataBitsAt_eq_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    design.reconstructionDataBitsAt current =
      design.overlapCostAt current + (seedLength - inputLength) + 1 := by
  rw [reconstructionDataBitsAt,
    overlapCostAt_eq_predecessorTableEntriesAt_add_internal,
    card_laterCoordinates_internal, card_outsideCoordinates_internal]

theorem reconstructionDataBitsAt_le_of_hasOverlapBudget_internal
    {outputLength inputLength seedLength budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (hbudget : design.HasOverlapBudget budget)
    (current : Fin outputLength) :
    design.reconstructionDataBitsAt current ≤
      budget + (seedLength - inputLength) + 1 := by
  rw [reconstructionDataBitsAt_eq_internal]
  exact Nat.add_le_add_right (Nat.add_le_add_right (hbudget current) _) _

end NWDesign

end Complexity
