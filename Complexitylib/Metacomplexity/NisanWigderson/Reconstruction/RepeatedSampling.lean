/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.RepeatedSampling.Defs
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.RepeatedSampling.Internal

/-!
# Repeated sampling of NW reconstruction advice

The probability of finding at least one good reconstruction advice choice in
`k` independent trials is exactly `1 - (1 - p)^k`, where `p` is the one-draw
success probability. In particular, `k * p ≥ 1` gives success probability at
least one half. Combined with the NW averaging bound `p ≥ δ / (2m)`, this is a
finite, explicit form of Hirahara's `O(m / δ)` randomized advice search.
-/


public section

namespace Complexity

namespace NWDesign

/-- Exact independent-repetition law for sampling good reconstruction advice. -/
theorem repeatedGoodReconstructionAdviceProbability_eq_one_sub_pow
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength) (agreementThreshold : ℚ)
    (trials : ℕ) :
    design.repeatedGoodReconstructionAdviceProbability hardFunction test
        current agreementThreshold trials =
      1 - (1 - design.goodReconstructionAdviceProbability hardFunction test
        current agreementThreshold) ^ trials :=
  repeatedGoodReconstructionAdviceProbability_eq_one_sub_pow_internal
    design hardFunction test current agreementThreshold trials

/-- Any certified one-draw success lower bound lifts to the exact independent
repetition lower bound. -/
theorem one_sub_pow_le_repeatedGoodReconstructionAdviceProbability
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
        current agreementThreshold trials :=
  one_sub_pow_le_repeatedGoodReconstructionAdviceProbability_internal
    design hardFunction test current agreementThreshold trials
      singleDrawLower hlower

/-- If `trials` times a one-draw success lower bound is at least one, repeated
advice sampling finds a good predictor with probability at least one half. -/
theorem half_le_repeatedGoodReconstructionAdviceProbability
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
        current agreementThreshold trials :=
  half_le_repeatedGoodReconstructionAdviceProbability_internal
    design hardFunction test current agreementThreshold trials
      singleDrawLower hlower htrials

/-- End-to-end repeated advice search from a dense random test, with the exact
geometric success lower bound and the fixed predictor payload bound. -/
theorem exists_repeatedGoodAdviceProbability_ge_of_randomTest
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
          budget + (seedLength - inputLength) + 1 :=
  exists_repeatedGoodAdviceProbability_ge_of_randomTest_internal
    houtputLength hdensity hlow hrandom hdense hbudget

/-- Hirahara's `O(m / δ)` advice-search step in explicit finite form: when
`trials * (δ / (2m)) ≥ 1`, repeated sampling finds a predictor with agreement
`1/2 + δ / (2m)` with probability at least one half. -/
theorem exists_half_le_repeatedGoodAdviceProbability_of_randomTest
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
          budget + (seedLength - inputLength) + 1 :=
  exists_half_le_repeatedGoodAdviceProbability_of_randomTest_internal
    houtputLength hdensity htrials hlow hrandom hdense hbudget

/-- Exact repeated advice-search bound when generator complexity is discharged
by direct short-seed descriptions. -/
theorem exists_repeatedGoodAdviceProbability_ge_of_seedDescriptions
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
          budget + (seedLength - inputLength) + 1 :=
  exists_repeatedGoodAdviceProbability_ge_of_seedDescriptions_internal
    houtputLength hdensity hseedLength hproduces hrandom hdense hbudget

/-- Half-success repeated advice search with low complexity discharged by
direct short-seed descriptions. -/
theorem exists_half_le_repeatedGoodAdviceProbability_of_seedDescriptions
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
          budget + (seedLength - inputLength) + 1 :=
  exists_half_le_repeatedGoodAdviceProbability_of_seedDescriptions_internal
    houtputLength hdensity htrials hseedLength hproduces hrandom hdense hbudget

end NWDesign

end Complexity
