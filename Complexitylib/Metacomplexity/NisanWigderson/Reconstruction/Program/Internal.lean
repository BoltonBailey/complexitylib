/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.Defs
import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.CertificateSearch.Internal
import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Internal

/-!
# Explicit NW reconstruction programs -- proof internals
-/


public section

namespace Complexity

namespace NWDesign

theorem materializeReconstructionProgram_query_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (complement : Bool) (current : Fin outputLength)
    (advice : design.ReconstructionAdvice current)
    (challenge : Fin inputLength → Bool) :
    (design.materializeReconstructionProgram hardFunction complement current
        advice).query challenge =
      design.reconstructionQuery hardFunction current advice.1 advice.2.1
        challenge advice.2.2 := by
  funext output
  by_cases houtput : output.val < current.val
  · have hmem : output ∈ Finset.Iio current := by
      simpa using houtput
    simp [ReconstructionProgram.query, materializeReconstructionProgram,
      reconstructionQuery, hmem, houtput]
  · have hmem : output ∉ Finset.Iio current := by
      simpa using houtput
    simp [ReconstructionProgram.query, materializeReconstructionProgram,
      reconstructionQuery, hmem, houtput]

theorem materializeReconstructionProgram_predictor_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (complement : Bool) (current : Fin outputLength)
    (advice : design.ReconstructionAdvice current) :
    (design.materializeReconstructionProgram hardFunction complement current
        advice).predictor test =
      design.reconstructionPredictor hardFunction
        (BitGenerator.orientTest test complement) current advice.1
        advice.2.1 advice.2.2 := by
  funext challenge
  change NextBitPrediction.predictFromTest
      (decide ((design.materializeReconstructionProgram hardFunction
        complement current advice).query challenge ∈
          BitGenerator.orientTest test complement)) advice.2.2 =
    NextBitPrediction.predictFromTest
      (decide (design.reconstructionQuery hardFunction current advice.1
        advice.2.1 challenge advice.2.2 ∈
          BitGenerator.orientTest test complement)) advice.2.2
  rw [materializeReconstructionProgram_query_internal]

theorem materializeReconstructionProgram_agreementProbability_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (complement : Bool) (current : Fin outputLength)
    (advice : design.ReconstructionAdvice current) :
    (design.materializeReconstructionProgram hardFunction complement current
        advice).agreementProbability hardFunction test =
      design.reconstructionAgreementProbability hardFunction
        (BitGenerator.orientTest test complement) current advice := by
  unfold ReconstructionProgram.agreementProbability
  unfold reconstructionAgreementProbability
  rw [materializeReconstructionProgram_predictor_internal]

theorem reconstructionCertificate_toProgram_agreementProbability_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (certificate : ReconstructionCertificate outputLength seedLength) :
    (certificate.toProgram design hardFunction).agreementProbability
        hardFunction test =
      design.reconstructionTrialAgreementProbability hardFunction
        (BitGenerator.orientTest test certificate.complement)
        certificate.trial := by
  unfold ReconstructionCertificate.toProgram
  unfold reconstructionTrialAgreementProbability
  exact materializeReconstructionProgram_agreementProbability_internal
    design hardFunction test certificate.complement certificate.trial.1
      (design.reconstructionAdviceOfTrial certificate.trial)

theorem ReconstructionProgram.booleanPayloadSize_eq_internal
    {outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram) :
    program.booleanPayloadSize =
      design.reconstructionDataBitsAt program.current := by
  simp [ReconstructionProgram.booleanPayloadSize,
    reconstructionDataBitsAt, predecessorTableEntriesAt]
  have hsum := Finset.sum_attach (Finset.Iio program.current)
    (fun previous =>
      2 ^ (design.challengeOverlap program.current previous).card)
  rw [hsum]
  omega

theorem findGoodReconstructionCertificate_program_sound_internal
    {outputLength inputLength seedLength trials budget : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (agreementThreshold : ℚ)
    (hbudget : design.HasOverlapBudget budget)
    (batch : Fin trials → ReconstructionTrial outputLength seedLength)
    (certificate : ReconstructionCertificate outputLength seedLength)
    (hfind : design.findGoodReconstructionCertificate? hardFunction test
      agreementThreshold batch = some certificate) :
    agreementThreshold ≤
        (certificate.toProgram design hardFunction).agreementProbability
          hardFunction test ∧
      (certificate.toProgram design hardFunction).booleanPayloadSize ≤
        budget + (seedLength - inputLength) + 1 := by
  obtain ⟨hgood, _index⟩ :=
    findGoodReconstructionCertificate_sound_internal design hardFunction test
      agreementThreshold batch certificate hfind
  constructor
  · rw [reconstructionCertificate_toProgram_agreementProbability_internal]
    exact hgood
  · rw [ReconstructionProgram.booleanPayloadSize_eq_internal]
    exact reconstructionDataBitsAt_le_of_hasOverlapBudget_internal
      hbudget certificate.trial.1

theorem half_le_materializedReconstructionProgram_of_randomTest_internal
    {outputLength inputLength seedLength tapes time threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {hardFunction : (Fin inputLength → Bool) → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 < density)
    (hlow : (design.generator hardFunction).HasLowTimeBoundedComplexity
      machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability hardFunction test
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength density) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate? hardFunction test
            (1 / 2 + (density / (outputLength : ℚ)) / 2) batch =
          some certificate →
        1 / 2 + (density / (outputLength : ℚ)) / 2 ≤
            (certificate.toProgram design hardFunction).agreementProbability
              hardFunction test ∧
          (certificate.toProgram design hardFunction).booleanPayloadSize ≤
            budget + (seedLength - inputLength) + 1 := by
  obtain ⟨hhalf, _hselected⟩ :=
    half_le_checkedReconstructionBatch_of_randomTest_internal
      houtputLength hdensity hlow hrandom hdense hbudget
  refine ⟨hhalf, ?_⟩
  intro batch certificate hfind
  exact findGoodReconstructionCertificate_program_sound_internal design
    hardFunction test
      (1 / 2 + (density / (outputLength : ℚ)) / 2) hbudget batch
      certificate hfind

theorem half_le_materializedReconstructionProgram_of_seedDescriptions_internal
    {outputLength inputLength seedLength tapes time threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {hardFunction : (Fin inputLength → Bool) → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 < density) (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (design.generator hardFunction seed)) time)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability hardFunction test
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength density) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate? hardFunction test
            (1 / 2 + (density / (outputLength : ℚ)) / 2) batch =
          some certificate →
        1 / 2 + (density / (outputLength : ℚ)) / 2 ≤
            (certificate.toProgram design hardFunction).agreementProbability
              hardFunction test ∧
          (certificate.toProgram design hardFunction).booleanPayloadSize ≤
            budget + (seedLength - inputLength) + 1 := by
  obtain ⟨hhalf, _hselected⟩ :=
    half_le_checkedReconstructionBatch_of_seedDescriptions_internal
      houtputLength hdensity hseedLength hproduces hrandom hdense hbudget
  refine ⟨hhalf, ?_⟩
  intro batch certificate hfind
  exact findGoodReconstructionCertificate_program_sound_internal design
    hardFunction test
      (1 / 2 + (density / (outputLength : ℚ)) / 2) hbudget batch
      certificate hfind

end NWDesign

end Complexity
