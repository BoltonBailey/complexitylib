/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Defs
public import Complexitylib.Metacomplexity.NisanWigderson.Internal

/-!
# Nisan--Wigderson set systems and generators

This module exposes an exact finite interface for the set systems and generator
used in the metacomplexity reconstruction. Blocks are injectively enumerated,
their intersection costs are finite natural numbers, and the associated NW
generator is definitionally a `BitGenerator`.

Combining the random-string statistical-test theorem with the finite hybrid
lemma shows that every dense random test against a low-complexity NW generator
has an oriented adjacent hybrid gap of at least its density divided by the
output length. The next-bit predictor and weak-design size accounting remain
separate subsequent layers.
-/


public section

namespace Complexity

namespace NWDesign

/-- Every block support has exactly the hard function's input length. -/
@[simp] theorem card_support {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (output : Fin outputLength) :
    (design.support output).card = inputLength :=
  card_support_internal design output

/-- A seed coordinate lies in a block support exactly when it is named by the
block's injective enumeration. -/
theorem mem_support_iff {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (output : Fin outputLength) (coordinate : Fin seedLength) :
    coordinate ∈ design.support output ↔
      ∃ input : Fin inputLength,
        design.coordinates output input = coordinate :=
  mem_support_iff_internal design output coordinate

/-- Design-block overlap is symmetric. -/
theorem overlap_comm {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (first second : Fin outputLength) :
    design.overlap first second = design.overlap second first :=
  overlap_comm_internal design first second

/-- A block overlaps itself in exactly all `inputLength` coordinates. -/
@[simp] theorem overlap_self {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (output : Fin outputLength) :
    design.overlap output output = inputLength :=
  overlap_self_internal design output

/-- No pair of blocks overlaps in more than `inputLength` coordinates. -/
theorem overlap_le_inputLength
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (first second : Fin outputLength) :
    design.overlap first second ≤ inputLength :=
  overlap_le_inputLength_internal design first second

/-- Enlarging the overlap budget preserves the weak-design property. -/
theorem HasOverlapBudget.mono
    {outputLength inputLength seedLength first second : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (hbudget : design.HasOverlapBudget first) (hle : first ≤ second) :
    design.HasOverlapBudget second :=
  hasOverlapBudget_mono_internal hbudget hle

/-- Seed restriction is evaluation along the block's coordinate embedding. -/
@[simp] theorem restrictSeed_apply
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (output : Fin outputLength) (seed : Fin seedLength → Bool)
    (input : Fin inputLength) :
    design.restrictSeed output seed input =
      seed (design.coordinates output input) :=
  restrictSeed_apply_internal design output seed input

/-- Each NW output bit evaluates the hard function on the corresponding
restricted seed. -/
@[simp] theorem generator_apply
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (seed : Fin seedLength → Bool) (output : Fin outputLength) :
    design.generator hardFunction seed output =
      hardFunction (design.restrictSeed output seed) :=
  generator_apply_internal design hardFunction seed output

/-- A dense random-string test against a low-complexity NW generator yields an
oriented adjacent hybrid gap of at least `density / outputLength`. -/
theorem exists_oriented_hybridGap_of_randomTest
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
            (BitGenerator.orientTest test complement) step :=
  exists_oriented_hybridGap_of_randomTest_internal
    houtputLength hlow hrandom hdense

/-- Hirahara's finite NW hybrid bridge with the low-complexity premise
discharged by direct short-seed descriptions. -/
theorem exists_oriented_hybridGap_of_seedDescriptions
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
            (BitGenerator.orientTest test complement) step :=
  exists_oriented_hybridGap_of_seedDescriptions_internal
    houtputLength hseedLength hproduces hrandom hdense

end NWDesign

end Complexity
