/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.StatisticalTest.Defs

/-!
# Hybrid distributions for finite binary generators -- definitions

The `cut`-th hybrid uses generator output in coordinates strictly below `cut`
and independent uniform bits in the remaining coordinates. Both sources of
randomness are packed into one Boolean string, so every probability remains an
exact `eventProb` over a finite dyadic sample space.

Complementing a test records the one-bit polarity choice used to orient an
absolute distinguishing advantage before applying the hybrid argument.
-/


@[expose] public section

namespace Complexity

namespace BitGenerator

/-- Optionally complement a finite test. The Boolean parameter is the polarity
bit used to orient an absolute distinguishing gap. -/
def orientTest {outputLength : ℕ}
    (test : Finset (Fin outputLength → Bool)) (complement : Bool) :
    Finset (Fin outputLength → Bool) :=
  if complement then testᶜ else test

/-- The `cut`-th hybrid between uniform output bits and the generator output.
Coordinates below `cut` come from the generator; all later coordinates are
independent uniform bits. -/
def hybridOutput {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength) (cut : ℕ)
    (randomness : Fin (seedLength + outputLength) → Bool) :
    Fin outputLength → Bool :=
  fun coordinate =>
    if coordinate.val < cut then
      generator (blockFst seedLength outputLength randomness) coordinate
    else
      blockSnd seedLength outputLength randomness coordinate

/-- Combined random strings whose `cut`-th hybrid output is accepted. -/
def hybridAcceptedRandomness {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) (cut : ℕ) :
    Finset (Fin (seedLength + outputLength) → Bool) :=
  Finset.univ.filter fun randomness => generator.hybridOutput cut randomness ∈ test

/-- Acceptance probability of a test under the `cut`-th hybrid. -/
def hybridAcceptanceProbability {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) (cut : ℕ) : ℚ :=
  eventProb (generator.hybridAcceptedRandomness test cut)

/-- Change in test acceptance when one more output coordinate is switched from
uniform to generated. -/
def hybridGap {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) (step : ℕ) : ℚ :=
  generator.hybridAcceptanceProbability test (step + 1) -
    generator.hybridAcceptanceProbability test step

end BitGenerator

end Complexity
