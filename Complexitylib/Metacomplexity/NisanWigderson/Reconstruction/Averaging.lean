/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Averaging.Defs
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Averaging.Internal

/-!
# Averaging NW reconstruction to fixed advice

Uniform NW seeds split bijectively into the challenge block and outside seed
coordinates, while a normalized hybrid tail splits into irrelevant earlier bits
and the later bits used by reconstruction. Consequently the global next-bit
success probability is exactly the joint fixed-advice agreement probability,
and averaging fixes one advice choice with no loss in agreement.
-/


public section

namespace Complexity

namespace NWDesign

/-- The canonical next-bit success probability is exactly average agreement of
the reconstructed fixed-advice predictors with the hard function. -/
theorem predictionSuccessProbability_eq_averageReconstructionAgreement
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength) :
    NextBitPrediction.successProbability
        ((design.generator hardFunction).targetBit current)
        ((design.generator hardFunction).testAtCandidate test current) =
      design.averageReconstructionAgreement hardFunction test current :=
  predictionSuccessProbability_eq_averageReconstructionAgreement_internal
    design hardFunction test current

/-- Some fixed outside seed, later tail, and candidate preserve at least the
global next-bit success probability over uniform challenges. -/
theorem exists_reconstructionAdvice_agreement_ge
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength) :
    ∃ advice : design.ReconstructionAdvice current,
      NextBitPrediction.successProbability
          ((design.generator hardFunction).targetBit current)
          ((design.generator hardFunction).testAtCandidate test current) ≤
        design.reconstructionAgreementProbability hardFunction test current
          advice :=
  exists_reconstructionAdvice_agreement_ge_internal
    design hardFunction test current

/-- End-to-end finite NW reconstruction: a dense random test and weak-design
budget yield one fixed predictor with the hybrid agreement advantage and an
exact non-codec payload bound. -/
theorem exists_fixed_reconstruction_of_randomTest
    {outputLength inputLength seedLength tapes time threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {hardFunction : (Fin inputLength → Bool) → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hlow : (design.generator hardFunction).HasLowTimeBoundedComplexity
      machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    ∃ (complement : Bool) (current : Fin outputLength)
        (advice : design.ReconstructionAdvice current),
      1 / 2 + density / (outputLength : ℚ) ≤
          design.reconstructionAgreementProbability hardFunction
            (BitGenerator.orientTest test complement) current advice ∧
        design.reconstructionDataBitsAt current ≤
          budget + (seedLength - inputLength) + 1 :=
  exists_fixed_reconstruction_of_randomTest_internal
    houtputLength hlow hrandom hdense hbudget

/-- The same fixed-predictor theorem with generator low complexity discharged
by direct descriptions shorter than the randomness threshold. -/
theorem exists_fixed_reconstruction_of_seedDescriptions
    {outputLength inputLength seedLength tapes time threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {hardFunction : (Fin inputLength → Bool) → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (design.generator hardFunction seed)) time)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    ∃ (complement : Bool) (current : Fin outputLength)
        (advice : design.ReconstructionAdvice current),
      1 / 2 + density / (outputLength : ℚ) ≤
          design.reconstructionAgreementProbability hardFunction
            (BitGenerator.orientTest test complement) current advice ∧
        design.reconstructionDataBitsAt current ≤
          budget + (seedLength - inputLength) + 1 :=
  exists_fixed_reconstruction_of_seedDescriptions_internal
    houtputLength hseedLength hproduces hrandom hdense hbudget

end NWDesign

end Complexity
