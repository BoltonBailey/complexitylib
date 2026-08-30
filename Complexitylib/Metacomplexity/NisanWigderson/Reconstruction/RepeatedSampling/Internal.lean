/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.RepeatedSampling.Defs
import Complexitylib.Classes.AverageCase.FiniteEnsemble.Internal
import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Averaging.Internal
import Complexitylib.Metacomplexity.StatisticalTest.Internal

/-!
# Repeated sampling of NW reconstruction advice -- proof internals

The exact finite repetition law and its quantitative reciprocal bound are
specialized to the advice event produced by NW reconstruction averaging.
-/


public section

namespace Complexity

namespace NWDesign

theorem repeatedGoodReconstructionAdviceProbability_eq_one_sub_pow_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength) (agreementThreshold : ℚ)
    (trials : ℕ) :
    design.repeatedGoodReconstructionAdviceProbability hardFunction test
        current agreementThreshold trials =
      1 - (1 - design.goodReconstructionAdviceProbability hardFunction test
        current agreementThreshold) ^ trials := by
  simpa [repeatedGoodReconstructionAdviceProbability,
    goodReconstructionAdviceEvent, goodReconstructionAdviceProbability] using
    uniformAtLeastOneProbability_eq_one_sub_pow_internal
      (design.goodReconstructionAdviceEvent hardFunction test current
        agreementThreshold)
      trials

theorem one_sub_pow_le_repeatedGoodReconstructionAdviceProbability_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength) (agreementThreshold : ℚ)
    (trials : ℕ) (singleDrawLower : ℚ)
    (hlower : singleDrawLower ≤
      design.goodReconstructionAdviceProbability hardFunction test current
        agreementThreshold) :
    1 - (1 - singleDrawLower) ^ trials ≤
      design.repeatedGoodReconstructionAdviceProbability hardFunction test
        current agreementThreshold trials := by
  exact one_sub_pow_le_uniformAtLeastOneProbability_internal
    (design.goodReconstructionAdviceEvent hardFunction test current
      agreementThreshold)
    trials singleDrawLower (by
      simpa [goodReconstructionAdviceEvent,
        goodReconstructionAdviceProbability] using hlower)

theorem half_le_repeatedGoodReconstructionAdviceProbability_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength) (agreementThreshold : ℚ)
    (trials : ℕ) (singleDrawLower : ℚ)
    (hlower : singleDrawLower ≤
      design.goodReconstructionAdviceProbability hardFunction test current
        agreementThreshold)
    (htrials : 1 ≤ (trials : ℚ) * singleDrawLower) :
    1 / 2 ≤
      design.repeatedGoodReconstructionAdviceProbability hardFunction test
        current agreementThreshold trials := by
  exact half_le_uniformAtLeastOneProbability_of_singleDrawLower_internal
    (design.goodReconstructionAdviceEvent hardFunction test current
      agreementThreshold)
    trials singleDrawLower (by
      simpa [goodReconstructionAdviceEvent,
        goodReconstructionAdviceProbability] using hlower)
    htrials

theorem exists_repeatedGoodAdviceProbability_ge_of_randomTest_internal
    {outputLength inputLength seedLength tapes time threshold budget trials : ℕ}
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
      1 - (1 - (density / (outputLength : ℚ)) / 2) ^ trials ≤
          design.repeatedGoodReconstructionAdviceProbability hardFunction
            (BitGenerator.orientTest test complement) current
            (1 / 2 + (density / (outputLength : ℚ)) / 2) trials ∧
        design.reconstructionDataBitsAt current ≤
          budget + (seedLength - inputLength) + 1 := by
  obtain ⟨complement, current, hsingle, hdata⟩ :=
    exists_goodAdviceProbability_ge_of_randomTest_internal
      houtputLength hdensity hlow hrandom hdense hbudget
  exact ⟨complement, current,
    one_sub_pow_le_repeatedGoodReconstructionAdviceProbability_internal
      design hardFunction (BitGenerator.orientTest test complement) current
      (1 / 2 + (density / (outputLength : ℚ)) / 2) trials
      ((density / (outputLength : ℚ)) / 2) hsingle,
    hdata⟩

theorem exists_half_le_repeatedGoodAdviceProbability_of_randomTest_internal
    {outputLength inputLength seedLength tapes time threshold budget trials : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {hardFunction : (Fin inputLength → Bool) → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 ≤ density)
    (htrials : 1 ≤ (trials : ℚ) *
      ((density / (outputLength : ℚ)) / 2))
    (hlow : (design.generator hardFunction).HasLowTimeBoundedComplexity
      machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    ∃ (complement : Bool) (current : Fin outputLength),
      1 / 2 ≤
          design.repeatedGoodReconstructionAdviceProbability hardFunction
            (BitGenerator.orientTest test complement) current
            (1 / 2 + (density / (outputLength : ℚ)) / 2) trials ∧
        design.reconstructionDataBitsAt current ≤
          budget + (seedLength - inputLength) + 1 := by
  obtain ⟨complement, current, hsingle, hdata⟩ :=
    exists_goodAdviceProbability_ge_of_randomTest_internal
      houtputLength hdensity hlow hrandom hdense hbudget
  exact ⟨complement, current,
    half_le_repeatedGoodReconstructionAdviceProbability_internal
      design hardFunction (BitGenerator.orientTest test complement) current
      (1 / 2 + (density / (outputLength : ℚ)) / 2) trials
      ((density / (outputLength : ℚ)) / 2) hsingle htrials,
    hdata⟩

theorem exists_repeatedGoodAdviceProbability_ge_of_seedDescriptions_internal
    {outputLength inputLength seedLength tapes time threshold budget trials : ℕ}
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
      1 - (1 - (density / (outputLength : ℚ)) / 2) ^ trials ≤
          design.repeatedGoodReconstructionAdviceProbability hardFunction
            (BitGenerator.orientTest test complement) current
            (1 / 2 + (density / (outputLength : ℚ)) / 2) trials ∧
        design.reconstructionDataBitsAt current ≤
          budget + (seedLength - inputLength) + 1 := by
  apply exists_repeatedGoodAdviceProbability_ge_of_randomTest_internal
    houtputLength hdensity (hrandom := hrandom) (hdense := hdense)
    (hbudget := hbudget)
  exact BitGenerator.hasLowTimeBoundedComplexity_of_seedDescriptions_internal
    hseedLength hproduces

theorem exists_half_le_repeatedGoodAdviceProbability_of_seedDescriptions_internal
    {outputLength inputLength seedLength tapes time threshold budget trials : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {hardFunction : (Fin inputLength → Bool) → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 ≤ density)
    (htrials : 1 ≤ (trials : ℚ) *
      ((density / (outputLength : ℚ)) / 2))
    (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (design.generator hardFunction seed)) time)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    ∃ (complement : Bool) (current : Fin outputLength),
      1 / 2 ≤
          design.repeatedGoodReconstructionAdviceProbability hardFunction
            (BitGenerator.orientTest test complement) current
            (1 / 2 + (density / (outputLength : ℚ)) / 2) trials ∧
        design.reconstructionDataBitsAt current ≤
          budget + (seedLength - inputLength) + 1 := by
  apply exists_half_le_repeatedGoodAdviceProbability_of_randomTest_internal
    houtputLength hdensity htrials (hrandom := hrandom) (hdense := hdense)
    (hbudget := hbudget)
  exact BitGenerator.hasLowTimeBoundedComplexity_of_seedDescriptions_internal
    hseedLength hproduces

end NWDesign

end Complexity
