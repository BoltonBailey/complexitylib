/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.StatisticalTest.Hybrid.Defs

/-!
# Hybrid distributions for finite binary generators -- proof internals
-/


public section

namespace Complexity

namespace BitGenerator

theorem orientTest_false_internal {outputLength : ℕ}
    (test : Finset (Fin outputLength → Bool)) :
    orientTest test false = test := by
  rfl

theorem orientTest_true_internal {outputLength : ℕ}
    (test : Finset (Fin outputLength → Bool)) :
    orientTest test true = testᶜ := by
  rfl

theorem acceptedSeeds_compl_internal {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) :
    generator.acceptedSeeds testᶜ = (generator.acceptedSeeds test)ᶜ := by
  ext seed
  simp [acceptedSeeds]

theorem uniformAcceptanceProbability_compl_internal {outputLength : ℕ}
    (test : Finset (Fin outputLength → Bool)) :
    uniformAcceptanceProbability testᶜ =
      1 - uniformAcceptanceProbability test := by
  exact eventProb_compl test

theorem generatedAcceptanceProbability_compl_internal
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) :
    generator.generatedAcceptanceProbability testᶜ =
      1 - generator.generatedAcceptanceProbability test := by
  change eventProb (generator.acceptedSeeds testᶜ) =
    1 - eventProb (generator.acceptedSeeds test)
  rw [acceptedSeeds_compl_internal, eventProb_compl]

theorem exists_orientation_of_distinguishingAdvantage_internal
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) {advantage : ℚ}
    (hadvantage : advantage ≤ generator.distinguishingAdvantage test) :
    ∃ complement : Bool,
      advantage ≤
        generator.generatedAcceptanceProbability
            (orientTest test complement) -
          uniformAcceptanceProbability (orientTest test complement) := by
  by_cases hnonnegative :
      0 ≤ uniformAcceptanceProbability test -
        generator.generatedAcceptanceProbability test
  · refine ⟨true, ?_⟩
    rw [orientTest_true_internal,
      generatedAcceptanceProbability_compl_internal,
      uniformAcceptanceProbability_compl_internal]
    rw [distinguishingAdvantage,
      abs_of_nonneg hnonnegative] at hadvantage
    linarith
  · refine ⟨false, ?_⟩
    rw [orientTest_false_internal]
    have hnegative :
        uniformAcceptanceProbability test -
            generator.generatedAcceptanceProbability test < 0 :=
      lt_of_not_ge hnonnegative
    rw [distinguishingAdvantage, abs_of_neg hnegative] at hadvantage
    linarith

theorem hybridOutput_zero_internal {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (randomness : Fin (seedLength + outputLength) → Bool) :
    generator.hybridOutput 0 randomness =
      blockSnd seedLength outputLength randomness := by
  funext coordinate
  simp [hybridOutput]

theorem hybridOutput_outputLength_internal {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (randomness : Fin (seedLength + outputLength) → Bool) :
    generator.hybridOutput outputLength randomness =
      generator (blockFst seedLength outputLength randomness) := by
  funext coordinate
  simp [hybridOutput, coordinate.isLt]

theorem hybridAcceptanceProbability_zero_internal
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) :
    generator.hybridAcceptanceProbability test 0 =
      uniformAcceptanceProbability test := by
  change eventProb (generator.hybridAcceptedRandomness test 0) =
    uniformAcceptanceProbability test
  have hevent :
      generator.hybridAcceptedRandomness test 0 =
        Finset.univ.filter fun randomness :
            Fin (seedLength + outputLength) → Bool =>
          True ∧ blockSnd seedLength outputLength randomness ∈ test := by
    ext randomness
    simp [hybridAcceptedRandomness, hybridOutput_zero_internal]
  rw [hevent]
  calc
    eventProb (Finset.univ.filter fun randomness :
          Fin (seedLength + outputLength) → Bool =>
        True ∧ blockSnd seedLength outputLength randomness ∈ test) =
        eventProb (Finset.univ.filter
          (fun _seed : Fin seedLength → Bool => True)) *
        eventProb (Finset.univ.filter
          (fun output : Fin outputLength → Bool => output ∈ test)) := by
      simpa only using eventProb_block
        (fun _seed : Fin seedLength → Bool => True)
        (fun output : Fin outputLength → Bool => output ∈ test)
    _ = uniformAcceptanceProbability test := by
      simp [uniformAcceptanceProbability]

theorem hybridAcceptanceProbability_outputLength_internal
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) :
    generator.hybridAcceptanceProbability test outputLength =
      generator.generatedAcceptanceProbability test := by
  change eventProb
      (generator.hybridAcceptedRandomness test outputLength) =
    generator.generatedAcceptanceProbability test
  have hevent :
      generator.hybridAcceptedRandomness test outputLength =
        Finset.univ.filter fun randomness :
            Fin (seedLength + outputLength) → Bool =>
          generator (blockFst seedLength outputLength randomness) ∈ test ∧
            True := by
    ext randomness
    simp [hybridAcceptedRandomness,
      hybridOutput_outputLength_internal]
  rw [hevent]
  calc
    eventProb (Finset.univ.filter fun randomness :
          Fin (seedLength + outputLength) → Bool =>
        generator (blockFst seedLength outputLength randomness) ∈ test ∧
          True) =
        eventProb (Finset.univ.filter
          (fun seed : Fin seedLength → Bool => generator seed ∈ test)) *
        eventProb (Finset.univ.filter
          (fun _output : Fin outputLength → Bool => True)) := by
      simpa only using eventProb_block
        (fun seed : Fin seedLength → Bool => generator seed ∈ test)
        (fun _output : Fin outputLength → Bool => True)
    _ = generator.generatedAcceptanceProbability test := by
      simp [generatedAcceptanceProbability, acceptedSeeds]

theorem sum_hybridGap_internal {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) :
    ∑ step ∈ Finset.range outputLength, generator.hybridGap test step =
      generator.generatedAcceptanceProbability test -
        uniformAcceptanceProbability test := by
  change
    ∑ step ∈ Finset.range outputLength,
        (generator.hybridAcceptanceProbability test (step + 1) -
          generator.hybridAcceptanceProbability test step) = _
  rw [Finset.sum_range_sub,
    hybridAcceptanceProbability_outputLength_internal,
    hybridAcceptanceProbability_zero_internal]

theorem exists_hybridGap_ge_average_internal
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) {advantage : ℚ}
    (houtputLength : 0 < outputLength)
    (hadvantage : advantage ≤
      generator.generatedAcceptanceProbability test -
        uniformAcceptanceProbability test) :
    ∃ step < outputLength,
      advantage / (outputLength : ℚ) ≤ generator.hybridGap test step := by
  have hsum :
      advantage ≤
        ∑ step ∈ Finset.range outputLength,
          generator.hybridGap test step := by
    rw [sum_hybridGap_internal]
    exact hadvantage
  have hnonzero : (outputLength : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt houtputLength)
  have hconstant :
      ∑ _step ∈ Finset.range outputLength,
          advantage / (outputLength : ℚ) = advantage := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have hle :
      ∑ _step ∈ Finset.range outputLength,
          advantage / (outputLength : ℚ) ≤
        ∑ step ∈ Finset.range outputLength,
          generator.hybridGap test step := by
    rw [hconstant]
    exact hsum
  obtain ⟨step, hstep, hgap⟩ :=
    Finset.exists_le_of_sum_le
      (⟨0, Finset.mem_range.mpr houtputLength⟩ :
        (Finset.range outputLength).Nonempty) hle
  exact ⟨step, Finset.mem_range.mp hstep, hgap⟩

theorem exists_oriented_hybridGap_ge_average_internal
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) {advantage : ℚ}
    (houtputLength : 0 < outputLength)
    (hadvantage : advantage ≤ generator.distinguishingAdvantage test) :
    ∃ (complement : Bool) (step : ℕ),
      step < outputLength ∧
        advantage / (outputLength : ℚ) ≤
          generator.hybridGap (orientTest test complement) step := by
  obtain ⟨complement, horiented⟩ :=
    exists_orientation_of_distinguishingAdvantage_internal
      generator test hadvantage
  obtain ⟨step, hstep, hgap⟩ :=
    exists_hybridGap_ge_average_internal generator
      (orientTest test complement) houtputLength horiented
  exact ⟨complement, step, hstep, hgap⟩

end BitGenerator

end Complexity
