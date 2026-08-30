/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Defs
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Internal

/-!
# Nisan--Wigderson fixed-advice reconstruction

This module turns the overlap tables into the exact query made by the Yao
next-bit predictor. It also removes irrelevant seed and tail coordinates from
the fixed advice and proves the resulting Boolean payload bound
`overlapCostAt + (d - ell) + 1`, before codec and parameter overhead.
-/


public section

namespace Complexity

namespace NWDesign

/-- There are exactly `d - ell` seed coordinates outside one design block. -/
@[simp] theorem card_outsideCoordinates
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    (design.outsideCoordinates current).card = seedLength - inputLength :=
  card_outsideCoordinates_internal design current

/-- There are exactly `m - (i + 1)` output coordinates after coordinate `i`. -/
@[simp] theorem card_laterCoordinates {outputLength : ℕ}
    (current : Fin outputLength) :
    (laterCoordinates current).card = outputLength - (current.val + 1) :=
  card_laterCoordinates_internal current

/-- Exact number of outside-seed assignments. -/
theorem card_outsideAssignments
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    Fintype.card (design.outsideCoordinates current → Bool) =
      2 ^ (seedLength - inputLength) :=
  card_outsideAssignments_internal design current

/-- Exact number of later-tail assignments. -/
theorem card_laterAssignments {outputLength : ℕ}
    (current : Fin outputLength) :
    Fintype.card (laterCoordinates current → Bool) =
      2 ^ (outputLength - (current.val + 1)) :=
  card_laterAssignments_internal current

/-- A reconstructed seed reads the supplied challenge on the current block. -/
@[simp] theorem reconstructionSeed_apply_coordinates
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength)
    (outside : design.outsideCoordinates current → Bool)
    (challenge : Fin inputLength → Bool) (input : Fin inputLength) :
    design.reconstructionSeed current outside challenge
        (design.coordinates current input) =
      challenge input :=
  reconstructionSeed_apply_coordinates_internal
    design current outside challenge input

/-- Restricting a seed to the outside and current-block coordinates and then
reconstructing it recovers the original seed exactly. -/
@[simp] theorem reconstructionSeed_restrict
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) (seed : Fin seedLength → Bool) :
    design.reconstructionSeed current
        (BooleanDependency.restrict
          (design.outsideCoordinates current) seed)
        (design.restrictSeed current seed) =
      seed :=
  reconstructionSeed_restrict_internal design current seed

/-- The target bit on a reconstruction background is the hard function applied
to the varying challenge. -/
@[simp] theorem reconstructionBackground_targetBit
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (current : Fin outputLength)
    (outside : design.outsideCoordinates current → Bool)
    (later : laterCoordinates current → Bool)
    (challenge : Fin inputLength → Bool) :
    (design.generator hardFunction).targetBit current
        (design.reconstructionBackground current outside later challenge) =
      hardFunction challenge :=
  reconstructionBackground_targetBit_internal
    design hardFunction current outside later challenge

/-- The table-based reconstruction query is exactly the hybrid query built
from the corresponding candidate background. -/
theorem reconstructionQuery_eq_hybridOutput
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
          candidate) :=
  reconstructionQuery_eq_hybridOutput_internal
    design hardFunction current outside later challenge candidate

/-- Evaluating the test on the reconstructed query agrees exactly with the
canonical next-bit experiment. -/
@[simp] theorem reconstructionTestAtCandidate_eq
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
        candidate :=
  reconstructionTestAtCandidate_eq_internal
    design hardFunction test current outside later challenge candidate

/-- Pointwise agreement of the fixed-advice reconstruction predictor with the
hard function is exactly the success event in the canonical experiment. -/
theorem reconstructionPredictor_agrees_iff
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
          (design.reconstructionBackground current outside later challenge) :=
  reconstructionPredictor_agrees_iff_internal
    design hardFunction test current outside later candidate challenge

/-- Exact reconstruction payload before encoding the test, design parameters,
coordinate, and polarity. -/
theorem reconstructionDataBitsAt_eq
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    design.reconstructionDataBitsAt current =
      design.overlapCostAt current + (seedLength - inputLength) + 1 :=
  reconstructionDataBitsAt_eq_internal design current

/-- A weak-design budget bounds the fixed predictor's non-codec payload by the
budget, the outside seed, and one candidate bit. -/
theorem reconstructionDataBitsAt_le_of_hasOverlapBudget
    {outputLength inputLength seedLength budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (hbudget : design.HasOverlapBudget budget)
    (current : Fin outputLength) :
    design.reconstructionDataBitsAt current ≤
      budget + (seedLength - inputLength) + 1 :=
  reconstructionDataBitsAt_le_of_hasOverlapBudget_internal hbudget current

end NWDesign

end Complexity
