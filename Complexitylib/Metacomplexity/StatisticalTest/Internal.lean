/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.StatisticalTest.Defs
import Complexitylib.Metacomplexity.Kolmogorov.Internal
import Complexitylib.Metacomplexity.Kolmogorov.Incompressibility.Internal

/-!
# Finite statistical tests for binary generators -- proof internals

The central fact is disjointness: a test containing only strings of complexity
at least `threshold` cannot accept an output whose complexity is strictly below
`threshold`. Exact zero generated mass and the density-to-advantage bound then
follow by finite counting.
-/


public section

namespace Complexity

namespace BitGenerator

theorem isTimeBoundedRandomTest_iff_subset_internal
    {outputLength tapes time threshold : ℕ}
    {test : Finset (Fin outputLength → Bool)} {machine : TM tapes} :
    IsTimeBoundedRandomTest test machine time threshold ↔
      test ⊆ machine.timeBoundedRandomStrings
        outputLength time threshold := by
  constructor
  · intro hrandom output hmember
    apply (TM.mem_timeBoundedRandomStrings_iff_internal
      machine outputLength time threshold output).mpr
    exact hrandom output hmember
  · intro hsubset output hmember
    apply (TM.mem_timeBoundedRandomStrings_iff_internal
      machine outputLength time threshold output).mp
    exact hsubset hmember

theorem timeBoundedRandomStrings_isRandomTest_internal
    {tapes : ℕ} (machine : TM tapes) (outputLength time threshold : ℕ) :
    IsTimeBoundedRandomTest
      (machine.timeBoundedRandomStrings outputLength time threshold)
      machine time threshold := by
  apply isTimeBoundedRandomTest_iff_subset_internal.mpr
  exact Finset.Subset.rfl

theorem timeBoundedRandomStrings_isDenseTest_internal
    {tapes : ℕ} (machine : TM tapes) (outputLength time threshold : ℕ) :
    IsDenseTest
      (machine.timeBoundedRandomStrings outputLength time threshold)
      (1 - ((2 ^ threshold - 1 : ℕ) : ℚ) /
        (2 : ℚ) ^ outputLength) :=
  TM.eventProb_timeBoundedRandomStrings_ge_internal
    machine outputLength time threshold

theorem hasLowTimeBoundedComplexity_of_seedDescriptions_internal
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (generator seed)) time) :
    generator.HasLowTimeBoundedComplexity machine time threshold := by
  intro seed
  apply (TM.timeBoundedKolmogorovComplexity_lt_coe_iff_internal
    machine (List.ofFn (generator seed)) time threshold).mpr
  exact ⟨List.ofFn seed, by simpa using hseedLength, hproduces seed⟩

theorem output_not_mem_of_randomTest_internal
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    {test : Finset (Fin outputLength → Bool)}
    (hlow : generator.HasLowTimeBoundedComplexity machine time threshold)
    (hrandom : IsTimeBoundedRandomTest test machine time threshold)
    (seed : Fin seedLength → Bool) :
    generator seed ∉ test := by
  intro hmember
  exact (not_lt_of_ge (hrandom (generator seed) hmember)) (hlow seed)

theorem acceptedSeeds_eq_empty_of_randomTest_internal
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    {test : Finset (Fin outputLength → Bool)}
    (hlow : generator.HasLowTimeBoundedComplexity machine time threshold)
    (hrandom : IsTimeBoundedRandomTest test machine time threshold) :
    generator.acceptedSeeds test = ∅ := by
  ext seed
  simp [acceptedSeeds,
    output_not_mem_of_randomTest_internal hlow hrandom seed]

theorem generatedAcceptanceProbability_eq_zero_of_randomTest_internal
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    {test : Finset (Fin outputLength → Bool)}
    (hlow : generator.HasLowTimeBoundedComplexity machine time threshold)
    (hrandom : IsTimeBoundedRandomTest test machine time threshold) :
    generator.generatedAcceptanceProbability test = 0 := by
  rw [generatedAcceptanceProbability,
    acceptedSeeds_eq_empty_of_randomTest_internal hlow hrandom,
    eventProb_empty]

theorem distinguishingAdvantage_eq_uniform_of_randomTest_internal
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    {test : Finset (Fin outputLength → Bool)}
    (hlow : generator.HasLowTimeBoundedComplexity machine time threshold)
    (hrandom : IsTimeBoundedRandomTest test machine time threshold) :
    generator.distinguishingAdvantage test =
      uniformAcceptanceProbability test := by
  rw [distinguishingAdvantage,
    generatedAcceptanceProbability_eq_zero_of_randomTest_internal hlow hrandom,
    sub_zero, abs_of_nonneg]
  exact eventProb_nonneg test

theorem density_le_distinguishingAdvantage_of_randomTest_internal
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    {test : Finset (Fin outputLength → Bool)} {density : ℚ}
    (hlow : generator.HasLowTimeBoundedComplexity machine time threshold)
    (hrandom : IsTimeBoundedRandomTest test machine time threshold)
    (hdense : IsDenseTest test density) :
    density ≤ generator.distinguishingAdvantage test := by
  rw [distinguishingAdvantage_eq_uniform_of_randomTest_internal hlow hrandom]
  exact hdense

theorem density_le_distinguishingAdvantage_of_seedDescriptions_internal
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    {test : Finset (Fin outputLength → Bool)} {density : ℚ}
    (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (generator seed)) time)
    (hrandom : IsTimeBoundedRandomTest test machine time threshold)
    (hdense : IsDenseTest test density) :
    density ≤ generator.distinguishingAdvantage test := by
  apply density_le_distinguishingAdvantage_of_randomTest_internal
    (hrandom := hrandom) (hdense := hdense)
  exact hasLowTimeBoundedComplexity_of_seedDescriptions_internal
    hseedLength hproduces

theorem incompressibilityBound_le_distinguishingAdvantage_internal
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    (hlow : generator.HasLowTimeBoundedComplexity machine time threshold) :
    1 - ((2 ^ threshold - 1 : ℕ) : ℚ) / (2 : ℚ) ^ outputLength ≤
      generator.distinguishingAdvantage
        (machine.timeBoundedRandomStrings outputLength time threshold) := by
  exact density_le_distinguishingAdvantage_of_randomTest_internal
    hlow
    (timeBoundedRandomStrings_isRandomTest_internal
      machine outputLength time threshold)
    (timeBoundedRandomStrings_isDenseTest_internal
      machine outputLength time threshold)

theorem incompressibilityBound_le_distinguishingAdvantage_of_seedDescriptions_internal
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (generator seed)) time) :
    1 - ((2 ^ threshold - 1 : ℕ) : ℚ) / (2 : ℚ) ^ outputLength ≤
      generator.distinguishingAdvantage
        (machine.timeBoundedRandomStrings outputLength time threshold) := by
  apply incompressibilityBound_le_distinguishingAdvantage_internal
  exact hasLowTimeBoundedComplexity_of_seedDescriptions_internal
    hseedLength hproduces

end BitGenerator

end Complexity
