/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Averaging.Defs
import Complexitylib.Classes.AverageCase.FiniteEnsemble.Internal
import Complexitylib.Metacomplexity.NisanWigderson.Hardwiring.Internal
import Complexitylib.Metacomplexity.NisanWigderson.Internal
import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Internal
import Complexitylib.Metacomplexity.StatisticalTest.Internal

/-!
# Averaging NW reconstruction to fixed advice -- proof internals
-/


public section

namespace Complexity

namespace NWDesign

private abbrev EarlierAssignment {outputLength : ℕ}
    (current : Fin outputLength) :=
  Finset.Iio current → Bool

private def assembleNormalizedTail {outputLength : ℕ}
    (current : Fin outputLength) (earlier : EarlierAssignment current)
    (later : laterCoordinates current → Bool) :
    {tail : Fin outputLength → Bool // tail current = false} :=
  ⟨fun output =>
      if hbefore : output ∈ Finset.Iio current then
        earlier ⟨output, hbefore⟩
      else if hafter : output ∈ laterCoordinates current then
        later ⟨output, hafter⟩
      else
        false,
    by simp [laterCoordinates]⟩

private def splitNormalizedTail {outputLength : ℕ}
    (current : Fin outputLength)
    (tail : {tail : Fin outputLength → Bool // tail current = false}) :
    EarlierAssignment current × (laterCoordinates current → Bool) :=
  (BooleanDependency.restrict (Finset.Iio current) tail.val,
    BooleanDependency.restrict (laterCoordinates current) tail.val)

private theorem splitNormalizedTail_assembleNormalizedTail
    {outputLength : ℕ} (current : Fin outputLength)
    (sample : EarlierAssignment current ×
      (laterCoordinates current → Bool)) :
    splitNormalizedTail current
        (assembleNormalizedTail current sample.1 sample.2) = sample := by
  apply Prod.ext
  · funext coordinate
    have hbefore : coordinate.val < current :=
      Finset.mem_Iio.mp coordinate.property
    simp [splitNormalizedTail, assembleNormalizedTail,
      BooleanDependency.restrict, hbefore]
  · funext coordinate
    have hafter : current < coordinate.val :=
      Finset.mem_Ioi.mp coordinate.property
    have hnotbefore : ¬coordinate.val < current := by omega
    simp [splitNormalizedTail, assembleNormalizedTail,
      BooleanDependency.restrict, hnotbefore,
      coordinate.property]

private theorem assembleNormalizedTail_splitNormalizedTail
    {outputLength : ℕ} (current : Fin outputLength)
    (tail : {tail : Fin outputLength → Bool // tail current = false}) :
    assembleNormalizedTail current
        (splitNormalizedTail current tail).1
        (splitNormalizedTail current tail).2 = tail := by
  apply Subtype.ext
  funext output
  rcases lt_trichotomy output current with hbefore | hequal | hafter
  · simp [assembleNormalizedTail, splitNormalizedTail,
      BooleanDependency.restrict, hbefore]
  · subst output
    simp [assembleNormalizedTail, laterCoordinates, tail.property]
  · have hnotbefore : ¬output < current := by omega
    simp [assembleNormalizedTail, splitNormalizedTail,
      BooleanDependency.restrict, laterCoordinates, hafter,
      hnotbefore]

private def normalizedTailEquiv {outputLength : ℕ}
    (current : Fin outputLength) :
    (EarlierAssignment current × (laterCoordinates current → Bool)) ≃
      {tail : Fin outputLength → Bool // tail current = false} where
  toFun sample := assembleNormalizedTail current sample.1 sample.2
  invFun := splitNormalizedTail current
  left_inv := splitNormalizedTail_assembleNormalizedTail current
  right_inv := assembleNormalizedTail_splitNormalizedTail current

private def reconstructionSeedEquiv
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    ((design.outsideCoordinates current → Bool) ×
        (Fin inputLength → Bool)) ≃
      (Fin seedLength → Bool) where
  toFun sample := design.reconstructionSeed current sample.1 sample.2
  invFun seed :=
    (BooleanDependency.restrict (design.outsideCoordinates current) seed,
      design.restrictSeed current seed)
  left_inv := by
    rintro ⟨outside, challenge⟩
    apply Prod.ext
    · funext coordinate
      exact reconstructionSeed_apply_outside_internal
        design current outside challenge coordinate
    · funext input
      exact reconstructionSeed_apply_coordinates_internal
        design current outside challenge input
  right_inv := reconstructionSeed_restrict_internal design current

private def reconstructionSampleEquiv
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    (EarlierAssignment current ×
        (design.ReconstructionAdvice current ×
          (Fin inputLength → Bool))) ≃
      (BitGenerator.CandidateBackground seedLength outputLength current × Bool) where
  toFun sample :=
    let earlier := sample.1
    let advice := sample.2.1
    let challenge := sample.2.2
    ((reconstructionSeedEquiv design current (advice.1, challenge),
        normalizedTailEquiv current (earlier, advice.2.1)),
      advice.2.2)
  invFun sample :=
    let seedParts := (reconstructionSeedEquiv design current).symm sample.1.1
    let tailParts := (normalizedTailEquiv current).symm sample.1.2
    (tailParts.1,
      ((seedParts.1, (tailParts.2, sample.2)), seedParts.2))
  left_inv := by
    rintro ⟨earlier, ⟨⟨outside, ⟨later, candidate⟩⟩, challenge⟩⟩
    simp
  right_inv := by
    rintro ⟨⟨seed, tail⟩, candidate⟩
    simp

private theorem blockAppend_natAdd_averaging
    {seedLength outputLength : ℕ}
    (seed : Fin seedLength → Bool) (tail : Fin outputLength → Bool)
    (coordinate : Fin outputLength) :
    blockAppend seedLength outputLength seed tail
        (Fin.natAdd seedLength coordinate) = tail coordinate := by
  have happ := congrFun
    (blockSnd_append seedLength outputLength seed tail) coordinate
  rw [blockSnd_apply] at happ
  exact happ

private theorem reconstructionQuery_eq_splitHybridOutput
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (current : Fin outputLength)
    (earlier : EarlierAssignment current)
    (advice : design.ReconstructionAdvice current)
    (challenge : Fin inputLength → Bool) :
    design.reconstructionQuery hardFunction current advice.1 advice.2.1
        challenge advice.2.2 =
      (design.generator hardFunction).hybridOutput current.val
        (BitGenerator.assembleCandidate
          ((design.reconstructionSeed current advice.1 challenge,
              assembleNormalizedTail current earlier advice.2.1) :
            BitGenerator.CandidateBackground seedLength outputLength current)
          advice.2.2) := by
  funext output
  by_cases hbefore : output.val < current.val
  · simp [reconstructionQuery, hbefore, BitGenerator.hybridOutput,
      BitGenerator.assembleCandidate, generator, reconstructionSeed,
      challengedBlock, predecessorTable_restrict_internal]
  · by_cases hequal : output = current
    · subst output
      simp [reconstructionQuery, BitGenerator.hybridOutput,
        BitGenerator.assembleCandidate, blockAppend_natAdd_averaging]
    · have hafter : current < output := by omega
      simp [reconstructionQuery, hbefore, BitGenerator.hybridOutput,
        BitGenerator.assembleCandidate, blockAppend_natAdd_averaging,
        laterTail, assembleNormalizedTail, laterCoordinates,
        BooleanDependency.extendByFalse, hafter, hequal]
      intro himpossible
      omega

private theorem reconstructionSample_success_iff
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength)
    (sample : EarlierAssignment current ×
      (design.ReconstructionAdvice current ×
        (Fin inputLength → Bool))) :
    NextBitPrediction.predictFromTest
          ((design.generator hardFunction).testAtCandidate test current
            (reconstructionSampleEquiv design current sample).1
            (reconstructionSampleEquiv design current sample).2)
          (reconstructionSampleEquiv design current sample).2 =
        (design.generator hardFunction).targetBit current
          (reconstructionSampleEquiv design current sample).1 ↔
      design.reconstructionPredictor hardFunction test current sample.2.1.1
          sample.2.1.2.1 sample.2.1.2.2 sample.2.2 =
        hardFunction sample.2.2 := by
  rcases sample with ⟨earlier, advice, challenge⟩
  change NextBitPrediction.predictFromTest
        ((design.generator hardFunction).testAtCandidate test current
          ((design.reconstructionSeed current advice.1 challenge,
              assembleNormalizedTail current earlier advice.2.1) :
            BitGenerator.CandidateBackground seedLength outputLength current)
          advice.2.2)
        advice.2.2 =
      (design.generator hardFunction).targetBit current
        ((design.reconstructionSeed current advice.1 challenge,
            assembleNormalizedTail current earlier advice.2.1) :
          BitGenerator.CandidateBackground seedLength outputLength current) ↔
    design.reconstructionPredictor hardFunction test current advice.1
      advice.2.1 advice.2.2 challenge = hardFunction challenge
  have hquery := reconstructionQuery_eq_splitHybridOutput
    design hardFunction current earlier advice challenge
  simp only [BitGenerator.testAtCandidate, reconstructionPredictor,
    reconstructionTestAtCandidate]
  rw [← hquery]
  have htarget :
      (design.generator hardFunction).targetBit current
          ((design.reconstructionSeed current advice.1 challenge,
              assembleNormalizedTail current earlier advice.2.1) :
            BitGenerator.CandidateBackground seedLength outputLength current) =
        hardFunction challenge := by
    simp only [BitGenerator.targetBit, generator]
    apply congrArg hardFunction
    funext input
    exact reconstructionSeed_apply_coordinates_internal
      design current advice.1 challenge input
  rw [htarget]

theorem predictionSuccessProbability_eq_averageReconstructionAgreement_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength) :
    NextBitPrediction.successProbability
        ((design.generator hardFunction).targetBit current)
        ((design.generator hardFunction).testAtCandidate test current) =
      design.averageReconstructionAgreement hardFunction test current := by
  classical
  let success :
      BitGenerator.CandidateBackground seedLength outputLength current × Bool → Prop :=
    fun sample => NextBitPrediction.predictFromTest
        ((design.generator hardFunction).testAtCandidate test current
          sample.1 sample.2)
        sample.2 = (design.generator hardFunction).targetBit current sample.1
  have htransport := uniformProbability_equiv_internal
    (reconstructionSampleEquiv design current) success
  rw [show NextBitPrediction.successProbability
      ((design.generator hardFunction).targetBit current)
      ((design.generator hardFunction).testAtCandidate test current) =
        uniformProbability (Finset.univ.filter success) by rfl]
  rw [← htransport]
  have hevent :
      (Finset.univ.filter fun sample : EarlierAssignment current ×
          (design.ReconstructionAdvice current ×
            (Fin inputLength → Bool)) =>
        success (reconstructionSampleEquiv design current sample)) =
        Finset.univ.filter fun sample : EarlierAssignment current ×
          (design.ReconstructionAdvice current ×
            (Fin inputLength → Bool)) =>
          design.reconstructionPredictor hardFunction test current
              sample.2.1.1 sample.2.1.2.1 sample.2.1.2.2 sample.2.2 =
            hardFunction sample.2.2 := by
    ext sample
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact reconstructionSample_success_iff
      design hardFunction test current sample
  rw [hevent]
  have hproduct := uniformProbability_product_internal
    (fun _earlier : EarlierAssignment current => True)
    (fun sample : design.ReconstructionAdvice current ×
        (Fin inputLength → Bool) =>
      design.reconstructionPredictor hardFunction test current sample.1.1
          sample.1.2.1 sample.1.2.2 sample.2 = hardFunction sample.2)
  simpa [averageReconstructionAgreement,
    uniformProbability_univ_internal] using hproduct

theorem exists_reconstructionAdvice_agreement_ge_internal
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
          advice := by
  rw [predictionSuccessProbability_eq_averageReconstructionAgreement_internal]
  have haverage := exists_fiber_uniformProbability_ge_internal
    (advice := design.ReconstructionAdvice current)
    (challenge := Fin inputLength → Bool)
    (fun advice challenge =>
      design.reconstructionPredictor hardFunction test current advice.1
        advice.2.1 advice.2.2 challenge = hardFunction challenge)
  simpa [averageReconstructionAgreement,
    reconstructionAgreementProbability] using haverage

theorem averageReconstructionAgreement_eq_uniformMean_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength) :
    design.averageReconstructionAgreement hardFunction test current =
      uniformMean (fun advice : design.ReconstructionAdvice current =>
        design.reconstructionAgreementProbability hardFunction test current
          advice) := by
  have haverage := uniformProbability_product_eq_average_fibers_internal
    (fun (advice : design.ReconstructionAdvice current)
        (challenge : Fin inputLength → Bool) =>
      design.reconstructionPredictor hardFunction test current advice.1
        advice.2.1 advice.2.2 challenge = hardFunction challenge)
  simpa [averageReconstructionAgreement, reconstructionAgreementProbability,
    uniformMean] using haverage

theorem average_sub_div_le_goodReconstructionAdviceProbability_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength) (agreementThreshold : ℚ)
    (hthreshold : agreementThreshold < 1) :
    (design.averageReconstructionAgreement hardFunction test current -
        agreementThreshold) / (1 - agreementThreshold) ≤
      design.goodReconstructionAdviceProbability hardFunction test current
        agreementThreshold := by
  rw [averageReconstructionAgreement_eq_uniformMean_internal]
  exact uniformMean_sub_div_le_probability_ge_internal
    (fun advice : design.ReconstructionAdvice current =>
      design.reconstructionAgreementProbability hardFunction test current advice)
    _ agreementThreshold
    (fun _advice => uniformProbability_le_one_internal _)
    le_rfl hthreshold

theorem half_advantage_le_goodReconstructionAdviceProbability_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength) (advantage : ℚ)
    (hadvantage : 0 ≤ advantage)
    (haverage : 1 / 2 + advantage ≤
      design.averageReconstructionAgreement hardFunction test current) :
    advantage / 2 ≤
      design.goodReconstructionAdviceProbability hardFunction test current
        (1 / 2 + advantage / 2) := by
  rw [averageReconstructionAgreement_eq_uniformMean_internal] at haverage
  exact half_epsilon_le_probability_ge_of_le_uniformMean_internal
    (fun advice : design.ReconstructionAdvice current =>
      design.reconstructionAgreementProbability hardFunction test current advice)
    advantage hadvantage
    (fun _advice => uniformProbability_le_one_internal _) haverage

theorem exists_fixed_reconstruction_of_randomTest_internal
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
          budget + (seedLength - inputLength) + 1 := by
  obtain ⟨complement, current, hsuccess⟩ :=
    exists_predictionSuccess_ge_half_add_density_div_internal
      houtputLength hlow hrandom hdense
  obtain ⟨advice, hadvice⟩ :=
    exists_reconstructionAdvice_agreement_ge_internal design hardFunction
      (BitGenerator.orientTest test complement) current
  exact ⟨complement, current, advice, hsuccess.trans hadvice,
    reconstructionDataBitsAt_le_of_hasOverlapBudget_internal hbudget current⟩

theorem exists_fixed_reconstruction_of_seedDescriptions_internal
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
          budget + (seedLength - inputLength) + 1 := by
  apply exists_fixed_reconstruction_of_randomTest_internal
    houtputLength (hrandom := hrandom) (hdense := hdense)
    (hbudget := hbudget)
  exact BitGenerator.hasLowTimeBoundedComplexity_of_seedDescriptions_internal
    hseedLength hproduces

theorem exists_goodAdviceProbability_ge_of_randomTest_internal
    {outputLength inputLength seedLength tapes time threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {hardFunction : (Fin inputLength → Bool) → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 ≤ density)
    (hlow : (design.generator hardFunction).HasLowTimeBoundedComplexity
      machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    ∃ (complement : Bool) (current : Fin outputLength),
      (density / (outputLength : ℚ)) / 2 ≤
          design.goodReconstructionAdviceProbability hardFunction
            (BitGenerator.orientTest test complement) current
            (1 / 2 + (density / (outputLength : ℚ)) / 2) ∧
        design.reconstructionDataBitsAt current ≤
          budget + (seedLength - inputLength) + 1 := by
  obtain ⟨complement, current, hsuccess⟩ :=
    exists_predictionSuccess_ge_half_add_density_div_internal
      houtputLength hlow hrandom hdense
  rw [predictionSuccessProbability_eq_averageReconstructionAgreement_internal]
    at hsuccess
  have hadvantage : 0 ≤ density / (outputLength : ℚ) := by positivity
  exact ⟨complement, current,
    half_advantage_le_goodReconstructionAdviceProbability_internal
      design hardFunction (BitGenerator.orientTest test complement) current
      (density / (outputLength : ℚ)) hadvantage hsuccess,
    reconstructionDataBitsAt_le_of_hasOverlapBudget_internal hbudget current⟩

theorem exists_goodAdviceProbability_ge_of_seedDescriptions_internal
    {outputLength inputLength seedLength tapes time threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {hardFunction : (Fin inputLength → Bool) → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 ≤ density) (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (design.generator hardFunction seed)) time)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    ∃ (complement : Bool) (current : Fin outputLength),
      (density / (outputLength : ℚ)) / 2 ≤
          design.goodReconstructionAdviceProbability hardFunction
            (BitGenerator.orientTest test complement) current
            (1 / 2 + (density / (outputLength : ℚ)) / 2) ∧
        design.reconstructionDataBitsAt current ≤
          budget + (seedLength - inputLength) + 1 := by
  apply exists_goodAdviceProbability_ge_of_randomTest_internal
    houtputLength hdensity (hrandom := hrandom) (hdense := hdense)
    (hbudget := hbudget)
  exact BitGenerator.hasLowTimeBoundedComplexity_of_seedDescriptions_internal
    hseedLength hproduces

end NWDesign

end Complexity
