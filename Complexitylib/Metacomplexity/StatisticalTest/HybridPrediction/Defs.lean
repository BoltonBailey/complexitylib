/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.StatisticalTest.Hybrid.Defs
public import Complexitylib.Metacomplexity.StatisticalTest.Prediction.Defs

/-!
# Splitting one hybrid coordinate into a next-bit experiment -- definitions

The background retains a generator seed and a uniform output tail whose
distinguished candidate coordinate is normalized to `false`. Replacing that
coordinate by an explicit Boolean candidate recovers the full hybrid random
space bijectively, without choosing an indexing of the remaining coordinates.
-/


@[expose] public section

namespace Complexity

namespace BitGenerator

/-- All randomness in a hybrid experiment except the distinguished candidate
bit. The output tail is normalized to `false` at that coordinate. -/
abbrev CandidateBackground (seedLength outputLength : ℕ)
    (step : Fin outputLength) :=
  (Fin seedLength → Bool) ×
    {tail : Fin outputLength → Bool // tail step = false}

/-- The all-false seed and tail witness that every candidate-background space
is nonempty. -/
instance candidateBackgroundNonempty (seedLength outputLength : ℕ)
    (step : Fin outputLength) :
    Nonempty (CandidateBackground seedLength outputLength step) :=
  ⟨(fun _ => false), ⟨(fun _ => false), rfl⟩⟩

/-- Reinsert a candidate bit and concatenate the generator seed with the
completed random output tail. -/
def assembleCandidate {seedLength outputLength : ℕ}
    {step : Fin outputLength}
    (background : CandidateBackground seedLength outputLength step)
    (candidate : Bool) : Fin (seedLength + outputLength) → Bool :=
  blockAppend seedLength outputLength background.1
    (Function.update background.2.val step candidate)

/-- The generator bit to be predicted from the background state. -/
def targetBit {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (step : Fin outputLength)
    (background : CandidateBackground seedLength outputLength step) : Bool :=
  generator background.1 step

/-- Test result when the distinguished bit in the `step`-th hybrid is filled
with `candidate`. -/
def testAtCandidate {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool))
    (step : Fin outputLength)
    (background : CandidateBackground seedLength outputLength step)
    (candidate : Bool) : Bool :=
  decide (generator.hybridOutput step.val
    (assembleCandidate background candidate) ∈ test)

end BitGenerator

end Complexity
