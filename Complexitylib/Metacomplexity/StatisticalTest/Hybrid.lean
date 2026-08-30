/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.StatisticalTest.Hybrid.Defs
public import Complexitylib.Metacomplexity.StatisticalTest.Hybrid.Internal

/-!
# Hybrid distributions for finite binary generators

This module gives the exact finite hybrid argument used at the start of the
Nisan--Wigderson reconstruction. The zero hybrid is uniform, the final hybrid
is the generator distribution, and the adjacent gaps telescope. Consequently,
any positive absolute distinguishing advantage can be oriented by optionally
complementing the test, after which one adjacent hybrid gap is at least the
advantage divided by the output length.
-/


public section

namespace Complexity

namespace BitGenerator

@[simp] theorem orientTest_false {outputLength : ℕ}
    (test : Finset (Fin outputLength → Bool)) :
    orientTest test false = test :=
  orientTest_false_internal test

@[simp] theorem orientTest_true {outputLength : ℕ}
    (test : Finset (Fin outputLength → Bool)) :
    orientTest test true = testᶜ :=
  orientTest_true_internal test

/-- Accepted seeds for the complementary test are exactly the complement of
the accepted-seed event. -/
theorem acceptedSeeds_compl {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) :
    generator.acceptedSeeds testᶜ = (generator.acceptedSeeds test)ᶜ :=
  acceptedSeeds_compl_internal generator test

/-- Complementing a test complements its uniform acceptance probability. -/
theorem uniformAcceptanceProbability_compl {outputLength : ℕ}
    (test : Finset (Fin outputLength → Bool)) :
    uniformAcceptanceProbability testᶜ =
      1 - uniformAcceptanceProbability test :=
  uniformAcceptanceProbability_compl_internal test

/-- Complementing a test complements its generated acceptance probability. -/
theorem generatedAcceptanceProbability_compl
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) :
    generator.generatedAcceptanceProbability testᶜ =
      1 - generator.generatedAcceptanceProbability test :=
  generatedAcceptanceProbability_compl_internal generator test

/-- One polarity of a test realizes its absolute distinguishing advantage as
an oriented generated-minus-uniform gap. -/
theorem exists_orientation_of_distinguishingAdvantage
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) {advantage : ℚ}
    (hadvantage : advantage ≤ generator.distinguishingAdvantage test) :
    ∃ complement : Bool,
      advantage ≤
        generator.generatedAcceptanceProbability
            (orientTest test complement) -
          uniformAcceptanceProbability (orientTest test complement) :=
  exists_orientation_of_distinguishingAdvantage_internal
    generator test hadvantage

/-- The zero hybrid is exactly the independent uniform-output block. -/
theorem hybridOutput_zero {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (randomness : Fin (seedLength + outputLength) → Bool) :
    generator.hybridOutput 0 randomness =
      blockSnd seedLength outputLength randomness :=
  hybridOutput_zero_internal generator randomness

/-- The final hybrid is exactly the generator output. -/
theorem hybridOutput_outputLength {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (randomness : Fin (seedLength + outputLength) → Bool) :
    generator.hybridOutput outputLength randomness =
      generator (blockFst seedLength outputLength randomness) :=
  hybridOutput_outputLength_internal generator randomness

/-- Test acceptance on the zero hybrid is its uniform acceptance probability. -/
theorem hybridAcceptanceProbability_zero
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) :
    generator.hybridAcceptanceProbability test 0 =
      uniformAcceptanceProbability test :=
  hybridAcceptanceProbability_zero_internal generator test

/-- Test acceptance on the final hybrid is its generated acceptance
probability. -/
theorem hybridAcceptanceProbability_outputLength
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) :
    generator.hybridAcceptanceProbability test outputLength =
      generator.generatedAcceptanceProbability test :=
  hybridAcceptanceProbability_outputLength_internal generator test

/-- Adjacent hybrid gaps telescope exactly to the oriented distinguishing
gap between generated and uniform outputs. -/
theorem sum_hybridGap {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) :
    ∑ step ∈ Finset.range outputLength, generator.hybridGap test step =
      generator.generatedAcceptanceProbability test -
        uniformAcceptanceProbability test :=
  sum_hybridGap_internal generator test

/-- If the oriented distinguishing gap is at least `advantage`, one adjacent
hybrid gap is at least `advantage / outputLength`. -/
theorem exists_hybridGap_ge_average
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) {advantage : ℚ}
    (houtputLength : 0 < outputLength)
    (hadvantage : advantage ≤
      generator.generatedAcceptanceProbability test -
        uniformAcceptanceProbability test) :
    ∃ step < outputLength,
      advantage / (outputLength : ℚ) ≤ generator.hybridGap test step :=
  exists_hybridGap_ge_average_internal
    generator test houtputLength hadvantage

/-- Finite Yao hybrid step: every absolute distinguishing advantage admits a
polarity and an adjacent hybrid whose gap is at least the average advantage. -/
theorem exists_oriented_hybridGap_ge_average
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) {advantage : ℚ}
    (houtputLength : 0 < outputLength)
    (hadvantage : advantage ≤ generator.distinguishingAdvantage test) :
    ∃ (complement : Bool) (step : ℕ),
      step < outputLength ∧
        advantage / (outputLength : ℚ) ≤
          generator.hybridGap (orientTest test complement) step :=
  exists_oriented_hybridGap_ge_average_internal
    generator test houtputLength hadvantage

end BitGenerator

end Complexity
