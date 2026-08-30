/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.AverageCase.FiniteEnsemble.Defs
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Defs

/-!
# Averaging NW reconstruction to fixed advice -- definitions

The advice choice retains precisely the outside seed assignment, later output
tail, and independent candidate bit. Its predictor is then a deterministic
Boolean function of the uniformly varying hard-function input.
-/


@[expose] public section

namespace Complexity

namespace NWDesign

/-- Fixed data chosen by averaging after a hybrid coordinate has been selected. -/
abbrev ReconstructionAdvice {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :=
  (design.outsideCoordinates current → Bool) ×
    ((laterCoordinates current → Bool) × Bool)

/-- Agreement probability of one fixed reconstruction predictor with the hard
function over a uniform challenge. -/
def reconstructionAgreementProbability
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength)
    (advice : design.ReconstructionAdvice current) : ℚ :=
  uniformProbability <| Finset.univ.filter fun challenge : Fin inputLength → Bool =>
    design.reconstructionPredictor hardFunction test current advice.1
      advice.2.1 advice.2.2 challenge = hardFunction challenge

/-- Joint agreement probability before fixing the reconstruction advice. -/
def averageReconstructionAgreement
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength) : ℚ :=
  uniformProbability <| Finset.univ.filter fun sample :
      design.ReconstructionAdvice current × (Fin inputLength → Bool) =>
    design.reconstructionPredictor hardFunction test current sample.1.1
      sample.1.2.1 sample.1.2.2 sample.2 = hardFunction sample.2

/-- Probability that a uniformly sampled advice choice attains a requested
agreement threshold. -/
def goodReconstructionAdviceProbability
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength) (agreementThreshold : ℚ) : ℚ :=
  uniformProbability <| Finset.univ.filter fun advice :
      design.ReconstructionAdvice current =>
    agreementThreshold ≤
      design.reconstructionAgreementProbability hardFunction test current advice

end NWDesign

end Complexity
