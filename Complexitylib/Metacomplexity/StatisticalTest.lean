/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.StatisticalTest.Defs
public import Complexitylib.Metacomplexity.StatisticalTest.Internal

/-!
# Finite statistical tests for binary generators

This module formalizes the first finite step in Hirahara's 2018
Nisan--Wigderson reconstruction argument. A dense set of strings that are
random for a time-bounded Kolmogorov threshold is a statistical test against
any generator whose outputs all lie strictly below that threshold.

In particular, if the machine directly produces each generated output from
its seed within the clock and the seed length is strictly below the randomness
threshold, the test has zero acceptance probability on generated outputs. Its
distinguishing advantage therefore equals its uniform density exactly.
-/


public section

namespace Complexity

namespace BitGenerator

/-- Being a time-bounded random-string test is exactly finite-set inclusion in
the canonical set of strings at or above the chosen complexity threshold. -/
theorem isTimeBoundedRandomTest_iff_subset
    {outputLength tapes time threshold : ℕ}
    {test : Finset (Fin outputLength → Bool)} {machine : TM tapes} :
    IsTimeBoundedRandomTest test machine time threshold ↔
      test ⊆ machine.timeBoundedRandomStrings
        outputLength time threshold :=
  isTimeBoundedRandomTest_iff_subset_internal

/-- The full canonical set of threshold-random strings is a random-string
test. -/
theorem timeBoundedRandomStrings_isRandomTest
    {tapes : ℕ} (machine : TM tapes) (outputLength time threshold : ℕ) :
    IsTimeBoundedRandomTest
      (machine.timeBoundedRandomStrings outputLength time threshold)
      machine time threshold :=
  timeBoundedRandomStrings_isRandomTest_internal
    machine outputLength time threshold

/-- The full random-string test has the quantitative uniform density supplied
by strict finite incompressibility. -/
theorem timeBoundedRandomStrings_isDenseTest
    {tapes : ℕ} (machine : TM tapes) (outputLength time threshold : ℕ) :
    IsDenseTest
      (machine.timeBoundedRandomStrings outputLength time threshold)
      (1 - ((2 ^ threshold - 1 : ℕ) : ℚ) /
        (2 : ℚ) ^ outputLength) :=
  timeBoundedRandomStrings_isDenseTest_internal
    machine outputLength time threshold

/-- If the machine produces every generated output directly from its seed and
the seed is shorter than the threshold, every output has complexity below the
threshold. This is the finite description step used for efficiently computable
short-seed generators. -/
theorem hasLowTimeBoundedComplexity_of_seedDescriptions
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (generator seed)) time) :
    generator.HasLowTimeBoundedComplexity machine time threshold :=
  hasLowTimeBoundedComplexity_of_seedDescriptions_internal
    hseedLength hproduces

/-- A low-complexity generator output cannot belong to a test containing only
strings at or above the same complexity threshold. -/
theorem output_not_mem_of_randomTest
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    {test : Finset (Fin outputLength → Bool)}
    (hlow : generator.HasLowTimeBoundedComplexity machine time threshold)
    (hrandom : IsTimeBoundedRandomTest test machine time threshold)
    (seed : Fin seedLength → Bool) :
    generator seed ∉ test :=
  output_not_mem_of_randomTest_internal hlow hrandom seed

/-- The test accepts no seed of a low-complexity generator. -/
theorem acceptedSeeds_eq_empty_of_randomTest
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    {test : Finset (Fin outputLength → Bool)}
    (hlow : generator.HasLowTimeBoundedComplexity machine time threshold)
    (hrandom : IsTimeBoundedRandomTest test machine time threshold) :
    generator.acceptedSeeds test = ∅ :=
  acceptedSeeds_eq_empty_of_randomTest_internal hlow hrandom

/-- A random-string test has exactly zero acceptance probability under any
generator whose outputs are all below its complexity threshold. -/
theorem generatedAcceptanceProbability_eq_zero_of_randomTest
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    {test : Finset (Fin outputLength → Bool)}
    (hlow : generator.HasLowTimeBoundedComplexity machine time threshold)
    (hrandom : IsTimeBoundedRandomTest test machine time threshold) :
    generator.generatedAcceptanceProbability test = 0 :=
  generatedAcceptanceProbability_eq_zero_of_randomTest_internal hlow hrandom

/-- For a random-string test against a low-complexity generator, the absolute
distinguishing advantage is exactly the test's uniform acceptance probability. -/
theorem distinguishingAdvantage_eq_uniform_of_randomTest
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    {test : Finset (Fin outputLength → Bool)}
    (hlow : generator.HasLowTimeBoundedComplexity machine time threshold)
    (hrandom : IsTimeBoundedRandomTest test machine time threshold) :
    generator.distinguishingAdvantage test =
      uniformAcceptanceProbability test :=
  distinguishingAdvantage_eq_uniform_of_randomTest_internal hlow hrandom

/-- A `density`-dense random-string test distinguishes every low-complexity
generator with advantage at least `density`. -/
theorem density_le_distinguishingAdvantage_of_randomTest
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    {test : Finset (Fin outputLength → Bool)} {density : ℚ}
    (hlow : generator.HasLowTimeBoundedComplexity machine time threshold)
    (hrandom : IsTimeBoundedRandomTest test machine time threshold)
    (hdense : IsDenseTest test density) :
    density ≤ generator.distinguishingAdvantage test :=
  density_le_distinguishingAdvantage_of_randomTest_internal
    hlow hrandom hdense

/-- Hirahara's finite statistical-test step: a dense random-string test has
advantage at least its density against a generator whose short seeds directly
describe its outputs within the chosen clock. -/
theorem density_le_distinguishingAdvantage_of_seedDescriptions
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    {test : Finset (Fin outputLength → Bool)} {density : ℚ}
    (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (generator seed)) time)
    (hrandom : IsTimeBoundedRandomTest test machine time threshold)
    (hdense : IsDenseTest test density) :
    density ≤ generator.distinguishingAdvantage test :=
  density_le_distinguishingAdvantage_of_seedDescriptions_internal
    hseedLength hproduces hrandom hdense

/-- The canonical random-string test distinguishes every generator whose
outputs are below the threshold by the full strict-incompressibility lower
bound. No computability property of the test is asserted here. -/
theorem incompressibilityBound_le_distinguishingAdvantage
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    (hlow : generator.HasLowTimeBoundedComplexity machine time threshold) :
    1 - ((2 ^ threshold - 1 : ℕ) : ℚ) / (2 : ℚ) ^ outputLength ≤
      generator.distinguishingAdvantage
        (machine.timeBoundedRandomStrings outputLength time threshold) :=
  incompressibilityBound_le_distinguishingAdvantage_internal hlow

/-- A directly seed-described generator is distinguished by the canonical
random-string test with the explicit strict-incompressibility advantage. -/
theorem incompressibilityBound_le_distinguishingAdvantage_of_seedDescriptions
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (generator seed)) time) :
    1 - ((2 ^ threshold - 1 : ℕ) : ℚ) / (2 : ℚ) ^ outputLength ≤
      generator.distinguishingAdvantage
        (machine.timeBoundedRandomStrings outputLength time threshold) :=
  incompressibilityBound_le_distinguishingAdvantage_of_seedDescriptions_internal
    hseedLength hproduces

end BitGenerator

end Complexity
