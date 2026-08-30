/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.RepeatedSampling.Defs

/-!
# Globally sampling NW reconstruction coordinates and advice -- definitions

A fixed-width reconstruction trial chooses a hybrid coordinate together with
full seed and output assignments and a candidate bit. Restricting the full
assignments produces the coordinate-dependent outside-seed and later-tail
advice. This realizes Hirahara's random tuple in one finite uniform sample
space without weighting coordinates by their varying advice-space sizes.
-/


@[expose] public section

namespace Complexity

namespace NWDesign

/-- Fixed-width raw advice from which every coordinate's reconstruction advice
is obtained by restriction. -/
abbrev RawReconstructionAdvice (outputLength seedLength : ℕ) :=
  (Fin seedLength → Bool) × ((Fin outputLength → Bool) × Bool)

/-- One globally sampled reconstruction coordinate and its fixed-width raw
advice. -/
abbrev ReconstructionTrial (outputLength seedLength : ℕ) :=
  Fin outputLength × RawReconstructionAdvice outputLength seedLength

/-- Restrict fixed-width raw advice to the outside-seed and later-tail
coordinates used at `current`. -/
def reconstructionAdviceOfRaw
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength)
    (raw : RawReconstructionAdvice outputLength seedLength) :
    design.ReconstructionAdvice current :=
  (BooleanDependency.restrict (design.outsideCoordinates current) raw.1,
    (BooleanDependency.restrict (laterCoordinates current) raw.2.1,
      raw.2.2))

/-- Coordinate-dependent reconstruction advice extracted from one global
trial. -/
def reconstructionAdviceOfTrial
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (trial : ReconstructionTrial outputLength seedLength) :
    design.ReconstructionAdvice trial.1 :=
  design.reconstructionAdviceOfRaw trial.1 trial.2

/-- Agreement probability of the predictor encoded by a global trial. -/
def reconstructionTrialAgreementProbability
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (trial : ReconstructionTrial outputLength seedLength) : ℚ :=
  design.reconstructionAgreementProbability hardFunction test trial.1
    (design.reconstructionAdviceOfTrial trial)

/-- Global trials whose reconstructed predictor attains an agreement
threshold. -/
def goodReconstructionTrialEvent
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (agreementThreshold : ℚ) :
    Finset (ReconstructionTrial outputLength seedLength) :=
  Finset.univ.filter fun trial =>
    agreementThreshold ≤
      design.reconstructionTrialAgreementProbability hardFunction test trial

/-- One-draw probability that a uniformly sampled coordinate and fixed-width
raw advice encode a predictor meeting the agreement threshold. -/
def goodReconstructionTrialProbability
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (agreementThreshold : ℚ) : ℚ :=
  uniformProbability <|
    design.goodReconstructionTrialEvent hardFunction test agreementThreshold

/-- Probability that at least one of several independent global trials encodes
a predictor meeting the agreement threshold. -/
def repeatedGoodReconstructionTrialProbability
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (agreementThreshold : ℚ) (trials : ℕ) : ℚ :=
  uniformAtLeastOneProbability
    (design.goodReconstructionTrialEvent hardFunction test agreementThreshold)
    trials

end NWDesign

end Complexity
