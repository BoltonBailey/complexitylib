/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Defs
import Complexitylib.Metacomplexity.StatisticalTest.Internal
import Complexitylib.Metacomplexity.StatisticalTest.Hybrid.Internal

/-!
# Nisan--Wigderson set systems and generators -- proof internals
-/


public section

namespace Complexity

namespace NWDesign

theorem card_support_internal {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (output : Fin outputLength) :
    (design.support output).card = inputLength := by
  simp [support]

theorem mem_support_iff_internal {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (output : Fin outputLength) (coordinate : Fin seedLength) :
    coordinate ∈ design.support output ↔
      ∃ input : Fin inputLength,
        design.coordinates output input = coordinate := by
  simp [support]

theorem overlap_comm_internal {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (first second : Fin outputLength) :
    design.overlap first second = design.overlap second first := by
  simp [overlap, Finset.inter_comm]

theorem overlap_self_internal {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (output : Fin outputLength) :
    design.overlap output output = inputLength := by
  simp [overlap, card_support_internal]

theorem overlap_le_inputLength_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (first second : Fin outputLength) :
    design.overlap first second ≤ inputLength := by
  calc
    design.overlap first second ≤ (design.support first).card := by
      exact Finset.card_le_card Finset.inter_subset_left
    _ = inputLength := card_support_internal design first

theorem hasOverlapBudget_mono_internal
    {outputLength inputLength seedLength first second : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (hbudget : design.HasOverlapBudget first) (hle : first ≤ second) :
    design.HasOverlapBudget second := by
  intro output
  exact (hbudget output).trans hle

theorem restrictSeed_apply_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (output : Fin outputLength) (seed : Fin seedLength → Bool)
    (input : Fin inputLength) :
    design.restrictSeed output seed input =
      seed (design.coordinates output input) := by
  rfl

theorem generator_apply_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (seed : Fin seedLength → Bool) (output : Fin outputLength) :
    design.generator hardFunction seed output =
      hardFunction (design.restrictSeed output seed) := by
  rfl

theorem exists_oriented_hybridGap_of_randomTest_internal
    {outputLength inputLength seedLength tapes time threshold : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {hardFunction : (Fin inputLength → Bool) → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hlow : (design.generator hardFunction).HasLowTimeBoundedComplexity
      machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density) :
    ∃ (complement : Bool) (step : ℕ),
      step < outputLength ∧
        density / (outputLength : ℚ) ≤
          (design.generator hardFunction).hybridGap
            (BitGenerator.orientTest test complement) step := by
  have hdistinguishes :
      density ≤
        (design.generator hardFunction).distinguishingAdvantage test :=
    BitGenerator.density_le_distinguishingAdvantage_of_randomTest_internal
      hlow hrandom hdense
  exact BitGenerator.exists_oriented_hybridGap_ge_average_internal
    (design.generator hardFunction) test houtputLength hdistinguishes

theorem exists_oriented_hybridGap_of_seedDescriptions_internal
    {outputLength inputLength seedLength tapes time threshold : ℕ}
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
    (hdense : BitGenerator.IsDenseTest test density) :
    ∃ (complement : Bool) (step : ℕ),
      step < outputLength ∧
        density / (outputLength : ℚ) ≤
          (design.generator hardFunction).hybridGap
            (BitGenerator.orientTest test complement) step := by
  apply exists_oriented_hybridGap_of_randomTest_internal
    houtputLength (hrandom := hrandom) (hdense := hdense)
  exact BitGenerator.hasLowTimeBoundedComplexity_of_seedDescriptions_internal
    hseedLength hproduces

end NWDesign

end Complexity
