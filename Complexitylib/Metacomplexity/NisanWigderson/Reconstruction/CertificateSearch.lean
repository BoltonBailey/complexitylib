/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.CertificateSearch.Defs
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.CertificateSearch.Internal

/-!
# Executable NW reconstruction certificate search

The finite search checks exact truth-table agreement, tries both orientations
of the supplied statistical test, and returns the first successful global
coordinate/advice trial. Its success probability dominates the favorable
orientation supplied by the NW hybrid argument.
-/


public section

namespace Complexity

namespace NWDesign

/-- The executable certificate checker accepts exactly the certificates whose
induced predictor meets the agreement threshold. -/
@[simp] theorem reconstructionCertificatePasses_eq_true_iff
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (agreementThreshold : ℚ)
    (certificate : ReconstructionCertificate outputLength seedLength) :
    design.reconstructionCertificatePasses hardFunction test
        agreementThreshold certificate = true ↔
      design.IsGoodReconstructionCertificate hardFunction test
        agreementThreshold certificate :=
  reconstructionCertificatePasses_eq_true_iff_internal
    design hardFunction test agreementThreshold certificate

/-- Trying both polarities for one trial succeeds exactly when one orientation
meets the agreement threshold. -/
theorem checkReconstructionTrial_isSome_iff
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (agreementThreshold : ℚ)
    (trial : ReconstructionTrial outputLength seedLength) :
    (design.checkReconstructionTrial? hardFunction test agreementThreshold
        trial).isSome ↔
      ∃ complement : Bool,
        design.IsGoodReconstructionCertificate hardFunction test
          agreementThreshold ⟨complement, trial⟩ :=
  checkReconstructionTrial_isSome_iff_internal
    design hardFunction test agreementThreshold trial

/-- Every certificate returned from one trial is good and contains exactly that
sampled trial. -/
theorem checkReconstructionTrial_sound
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (agreementThreshold : ℚ)
    (trial : ReconstructionTrial outputLength seedLength)
    (certificate : ReconstructionCertificate outputLength seedLength)
    (hcheck : design.checkReconstructionTrial? hardFunction test
      agreementThreshold trial = some certificate) :
    design.IsGoodReconstructionCertificate hardFunction test
        agreementThreshold certificate ∧
      certificate.trial = trial :=
  checkReconstructionTrial_sound_internal design hardFunction test
    agreementThreshold trial certificate hcheck

/-- Batch search succeeds exactly when some sampled trial meets the threshold
under one of the two test orientations. -/
theorem findGoodReconstructionCertificate_isSome_iff
    {outputLength inputLength seedLength trials : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (agreementThreshold : ℚ)
    (batch : Fin trials → ReconstructionTrial outputLength seedLength) :
    (design.findGoodReconstructionCertificate? hardFunction test
        agreementThreshold batch).isSome ↔
      ∃ index complement,
        design.IsGoodReconstructionCertificate hardFunction test
          agreementThreshold ⟨complement, batch index⟩ :=
  findGoodReconstructionCertificate_isSome_iff_internal
    design hardFunction test agreementThreshold batch

/-- Every result returned by batch search meets the agreement threshold and
comes from one of the supplied samples. -/
theorem findGoodReconstructionCertificate_sound
    {outputLength inputLength seedLength trials : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (agreementThreshold : ℚ)
    (batch : Fin trials → ReconstructionTrial outputLength seedLength)
    (certificate : ReconstructionCertificate outputLength seedLength)
    (hfind : design.findGoodReconstructionCertificate? hardFunction test
      agreementThreshold batch = some certificate) :
    design.IsGoodReconstructionCertificate hardFunction test
        agreementThreshold certificate ∧
      ∃ index, certificate.trial = batch index :=
  findGoodReconstructionCertificate_sound_internal design hardFunction test
    agreementThreshold batch certificate hfind

/-- Checking both orientations can only improve on repeated sampling for any
one fixed orientation. -/
theorem repeatedGoodReconstructionTrialProbability_le_checked
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (complement : Bool) (agreementThreshold : ℚ) (trials : ℕ) :
    design.repeatedGoodReconstructionTrialProbability hardFunction
        (BitGenerator.orientTest test complement) agreementThreshold trials ≤
      design.checkedReconstructionBatchSuccessProbability hardFunction test
        agreementThreshold trials :=
  repeatedGoodReconstructionTrialProbability_le_checked_internal
    design hardFunction test complement agreementThreshold trials

/-- End-to-end executable finite selection: exact checking of
`ceil(2m / δ)` global samples finds an agreement-`1/2 + δ/(2m)`
certificate with probability at least one half. Every returned certificate
retains the weak-design payload bound. -/
theorem half_le_checkedReconstructionBatch_of_randomTest
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
        design.reconstructionDataBitsAt certificate.trial.1 ≤
          budget + (seedLength - inputLength) + 1 :=
  half_le_checkedReconstructionBatch_of_randomTest_internal
    houtputLength hdensity hlow hrandom hdense hbudget

/-- The executable finite selection theorem with low generator complexity
discharged by direct short-seed descriptions. -/
theorem half_le_checkedReconstructionBatch_of_seedDescriptions
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
        design.reconstructionDataBitsAt certificate.trial.1 ≤
          budget + (seedLength - inputLength) + 1 :=
  half_le_checkedReconstructionBatch_of_seedDescriptions_internal
    houtputLength hdensity hseedLength hproduces hrandom hdense hbudget

end NWDesign

end Complexity
