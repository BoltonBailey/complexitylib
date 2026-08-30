/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Hardwiring.Defs
public import Complexitylib.Metacomplexity.StatisticalTest.HybridPrediction.Defs
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Nisan--Wigderson fixed-advice reconstruction -- definitions

The finite next-bit experiment initially samples a full NW seed and full output
tail. A reconstruction circuit instead fixes only seed coordinates outside the
challenge block and tail coordinates after the predicted bit. Earlier generator
values are supplied by the overlap-indexed predecessor tables.
-/


@[expose] public section

namespace Complexity

namespace NWDesign

/-- Seed coordinates outside the challenged design block. -/
def outsideCoordinates {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) : Finset (Fin seedLength) :=
  Finset.univ \ design.support current

/-- Output coordinates strictly after the predicted coordinate. -/
def laterCoordinates {outputLength : ℕ} (current : Fin outputLength) :
    Finset (Fin outputLength) :=
  Finset.Ioi current

/-- Extend an assignment to the outside seed coordinates by false before
inserting the challenge. -/
def outsideSeed {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength)
    (outside : design.outsideCoordinates current → Bool) :
    Fin seedLength → Bool :=
  BooleanDependency.extendByFalse (design.outsideCoordinates current) outside

/-- Assemble a full seed from an outside assignment and a challenge on the
current design block. -/
def reconstructionSeed {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength)
    (outside : design.outsideCoordinates current → Bool)
    (challenge : Fin inputLength → Bool) : Fin seedLength → Bool :=
  design.seedWithChallenge current (design.outsideSeed current outside) challenge

/-- Extend later output bits by false at and before the predicted coordinate. -/
def laterTail {outputLength : ℕ} (current : Fin outputLength)
    (later : laterCoordinates current → Bool) : Fin outputLength → Bool :=
  BooleanDependency.extendByFalse (laterCoordinates current) later

/-- Candidate background assembled from exactly the fixed outside-seed and
later-tail assignments, together with a varying challenge. -/
def reconstructionBackground {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength)
    (outside : design.outsideCoordinates current → Bool)
    (later : laterCoordinates current → Bool)
    (challenge : Fin inputLength → Bool) :
  BitGenerator.CandidateBackground seedLength outputLength current :=
  (design.reconstructionSeed current outside challenge,
    ⟨laterTail current later, by
      simp [laterTail, laterCoordinates,
        BooleanDependency.extendByFalse]⟩)

/-- Query assembled from hardwired predecessor tables, the independent
candidate, and fixed later bits. -/
def reconstructionQuery {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (current : Fin outputLength)
    (outside : design.outsideCoordinates current → Bool)
    (later : laterCoordinates current → Bool)
    (challenge : Fin inputLength → Bool) (candidate : Bool) :
    Fin outputLength → Bool :=
  fun output =>
    if output.val < current.val then
      design.predecessorTable current output
        (design.outsideSeed current outside) hardFunction
        (BooleanDependency.restrict
          (design.challengeOverlap current output) challenge)
    else
      Function.update (laterTail current later) current candidate output

/-- Test evaluation computed from the reconstruction query. -/
def reconstructionTestAtCandidate
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength)
    (outside : design.outsideCoordinates current → Bool)
    (later : laterCoordinates current → Bool)
    (challenge : Fin inputLength → Bool) (candidate : Bool) : Bool :=
  decide (design.reconstructionQuery hardFunction current outside later
    challenge candidate ∈ test)

/-- The fixed-advice next-bit predictor as a Boolean function of the challenge. -/
def reconstructionPredictor {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength)
    (outside : design.outsideCoordinates current → Bool)
    (later : laterCoordinates current → Bool) (candidate : Bool) :
    (Fin inputLength → Bool) → Bool :=
  fun challenge => NextBitPrediction.predictFromTest
    (design.reconstructionTestAtCandidate hardFunction test current outside
      later challenge candidate)
    candidate

/-- Exact non-codec Boolean payload of one fixed reconstruction predictor:
predecessor-table entries, later bits, outside seed bits, and the candidate. -/
def reconstructionDataBitsAt {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) : ℕ :=
  design.predecessorTableEntriesAt current +
    (laterCoordinates current).card +
    (design.outsideCoordinates current).card + 1

end NWDesign

end Complexity
