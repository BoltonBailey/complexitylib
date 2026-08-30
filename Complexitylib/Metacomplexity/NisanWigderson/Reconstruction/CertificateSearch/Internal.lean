/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.CertificateSearch.Defs
import Batteries.Data.Fin.Lemmas
import Complexitylib.Classes.AverageCase.FiniteEnsemble.Internal
import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.GlobalSampling.Internal

/-!
# Executable NW reconstruction certificate search -- proof internals
-/


public section

namespace Complexity

namespace NWDesign

theorem reconstructionCertificatePasses_eq_true_iff_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (agreementThreshold : ℚ)
    (certificate : ReconstructionCertificate outputLength seedLength) :
    design.reconstructionCertificatePasses hardFunction test
        agreementThreshold certificate = true ↔
      design.IsGoodReconstructionCertificate hardFunction test
        agreementThreshold certificate := by
  simp [reconstructionCertificatePasses, IsGoodReconstructionCertificate]

theorem checkReconstructionTrial_isSome_iff_internal
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
          agreementThreshold ⟨complement, trial⟩ := by
  by_cases hdirect : agreementThreshold ≤
      design.reconstructionTrialAgreementProbability hardFunction
        (BitGenerator.orientTest test false) trial
  · simp [checkReconstructionTrial?, reconstructionCertificatePasses,
      IsGoodReconstructionCertificate, hdirect]
  · by_cases hcomplemented : agreementThreshold ≤
        design.reconstructionTrialAgreementProbability hardFunction
          (BitGenerator.orientTest test true) trial
    · simp [checkReconstructionTrial?, reconstructionCertificatePasses,
        IsGoodReconstructionCertificate, hdirect, hcomplemented]
    · simp [checkReconstructionTrial?, reconstructionCertificatePasses,
        IsGoodReconstructionCertificate, hdirect, hcomplemented]

theorem findGoodReconstructionCertificate_isSome_iff_internal
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
          agreementThreshold ⟨complement, batch index⟩ := by
  simp only [findGoodReconstructionCertificate?, Fin.isSome_findSome?_iff,
    checkReconstructionTrial_isSome_iff_internal]

theorem checkReconstructionTrial_sound_internal
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
      certificate.trial = trial := by
  unfold checkReconstructionTrial? at hcheck
  dsimp only at hcheck
  split at hcheck
  next hdirect =>
    simp only [Option.some.injEq] at hcheck
    subst certificate
    exact ⟨(reconstructionCertificatePasses_eq_true_iff_internal
      design hardFunction test agreementThreshold ⟨false, trial⟩).mp
        hdirect, rfl⟩
  next hnotDirect =>
    split at hcheck
    next hcomplemented =>
      simp only [Option.some.injEq] at hcheck
      subst certificate
      exact ⟨(reconstructionCertificatePasses_eq_true_iff_internal
        design hardFunction test agreementThreshold ⟨true, trial⟩).mp
          hcomplemented, rfl⟩
    next hnotComplemented =>
      simp at hcheck

theorem findGoodReconstructionCertificate_sound_internal
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
      ∃ index, certificate.trial = batch index := by
  obtain ⟨index, hcheck⟩ :=
    Fin.exists_eq_some_of_findSome?_eq_some hfind
  obtain ⟨hgood, htrial⟩ := checkReconstructionTrial_sound_internal
    design hardFunction test agreementThreshold (batch index) certificate hcheck
  exact ⟨hgood, index, htrial⟩

theorem repeatedGoodReconstructionTrialProbability_le_checked_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (complement : Bool) (agreementThreshold : ℚ) (trials : ℕ) :
    design.repeatedGoodReconstructionTrialProbability hardFunction
        (BitGenerator.orientTest test complement) agreementThreshold trials ≤
      design.checkedReconstructionBatchSuccessProbability hardFunction test
        agreementThreshold trials := by
  unfold repeatedGoodReconstructionTrialProbability
  unfold uniformAtLeastOneProbability
  unfold checkedReconstructionBatchSuccessProbability
  unfold uniformProbability
  gcongr
  intro batch hbatch
  simp only [uniformAtLeastOneEvent, Finset.mem_filter, Finset.mem_univ,
    true_and] at hbatch
  obtain ⟨index, hgood⟩ := hbatch
  simp only [checkedReconstructionBatchEvent, Finset.mem_filter,
    Finset.mem_univ, true_and]
  apply (findGoodReconstructionCertificate_isSome_iff_internal
    design hardFunction test agreementThreshold batch).2
  refine ⟨index, complement, ?_⟩
  simpa [goodReconstructionTrialEvent,
    IsGoodReconstructionCertificate] using hgood

theorem half_le_checkedReconstructionBatch_of_randomTest_internal
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
          budget + (seedLength - inputLength) + 1 := by
  obtain ⟨complement, hrepeat, hdata⟩ :=
    exists_half_le_canonicalRepeatedGoodTrial_of_randomTest_internal
      houtputLength hdensity hlow hrandom hdense hbudget
  constructor
  · exact hrepeat.trans
      (repeatedGoodReconstructionTrialProbability_le_checked_internal
        design hardFunction test complement
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density))
  · intro batch certificate hfind
    obtain ⟨_good, index, htrial⟩ :=
      findGoodReconstructionCertificate_sound_internal design hardFunction
        test (1 / 2 + (density / (outputLength : ℚ)) / 2) batch
        certificate hfind
    simpa [htrial] using hdata (batch index)

theorem half_le_checkedReconstructionBatch_of_seedDescriptions_internal
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
          budget + (seedLength - inputLength) + 1 := by
  obtain ⟨complement, hrepeat, hdata⟩ :=
    exists_half_le_canonicalRepeatedGoodTrial_of_seedDescriptions_internal
      houtputLength hdensity hseedLength hproduces hrandom hdense hbudget
  constructor
  · exact hrepeat.trans
      (repeatedGoodReconstructionTrialProbability_le_checked_internal
        design hardFunction test complement
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density))
  · intro batch certificate hfind
    obtain ⟨_good, index, htrial⟩ :=
      findGoodReconstructionCertificate_sound_internal design hardFunction
        test (1 / 2 + (density / (outputLength : ℚ)) / 2) batch
        certificate hfind
    simpa [htrial] using hdata (batch index)

end NWDesign

end Complexity
