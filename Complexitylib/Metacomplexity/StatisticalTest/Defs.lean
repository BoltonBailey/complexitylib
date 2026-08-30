/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Kolmogorov.Incompressibility.Defs

/-!
# Finite statistical tests for binary generators -- definitions

This layer fixes exact finite conventions for the first step of the
Nisan--Wigderson reconstruction used in metacomplexity. A generator maps a
uniform fixed-length Boolean seed to a fixed-length Boolean output. A test's
acceptance probability is measured both under uniform output bits and under
the generator, and its distinguishing advantage is the absolute difference.

The complexity predicates remain relative to an arbitrary deterministic
machine and primitive clock. Universality and efficient computability of a
particular generator are separate hypotheses.
-/


@[expose] public section

namespace Complexity

/-- A deterministic binary generator from `seedLength` bits to `outputLength`
bits. No expansion or computability condition is built into the type. -/
abbrev BitGenerator (seedLength outputLength : ℕ) :=
  (Fin seedLength → Bool) → (Fin outputLength → Bool)

namespace BitGenerator

/-- The seeds whose generated outputs are accepted by a finite test. -/
def acceptedSeeds {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) :
    Finset (Fin seedLength → Bool) :=
  Finset.univ.filter fun seed => generator seed ∈ test

/-- Acceptance probability of a test under a uniform generator seed. -/
def generatedAcceptanceProbability {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) : ℚ :=
  eventProb (generator.acceptedSeeds test)

/-- Acceptance probability of a test under uniform output bits. -/
def uniformAcceptanceProbability {outputLength : ℕ}
    (test : Finset (Fin outputLength → Bool)) : ℚ :=
  eventProb test

/-- Absolute distinguishing advantage of a test between uniform output bits
and the output of a generator on a uniform seed. -/
def distinguishingAdvantage {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) : ℚ :=
  |uniformAcceptanceProbability test -
    generator.generatedAcceptanceProbability test|

/-- A test is `density`-dense when it accepts at least that much uniform
output mass. -/
def IsDenseTest {outputLength : ℕ}
    (test : Finset (Fin outputLength → Bool)) (density : ℚ) : Prop :=
  density ≤ uniformAcceptanceProbability test

/-- Every generated output has time-bounded complexity strictly below the
specified threshold. -/
def HasLowTimeBoundedComplexity {seedLength outputLength tapes : ℕ}
    (generator : BitGenerator seedLength outputLength) (machine : TM tapes)
    (time threshold : ℕ) : Prop :=
  ∀ seed,
    machine.timeBoundedKolmogorovComplexity
        (List.ofFn (generator seed)) time <
      (threshold : WithTop ℕ)

/-- Every output accepted by the test is random at the specified threshold
and clock. Equivalently, the test is a subset of the corresponding finite set
of time-bounded random strings. -/
def IsTimeBoundedRandomTest {outputLength tapes : ℕ}
    (test : Finset (Fin outputLength → Bool)) (machine : TM tapes)
    (time threshold : ℕ) : Prop :=
  ∀ output, output ∈ test →
    (threshold : WithTop ℕ) ≤
      machine.timeBoundedKolmogorovComplexity (List.ofFn output) time

end BitGenerator

end Complexity
