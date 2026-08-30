/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.GoodString.Defs
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.GoodString.Internal
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.GoodString.Tail

/-!
# Good-string combinatorics

This module formalizes the finite counting core of the good-string argument.
Surviving circuit codes form a finite type. An input catches a tuple of
survivors when at most half of the tuple agrees with the target there, and the
number of caught tuples is an exact weighted binomial tail.

If every survivor tuple is caught somewhere, a max-fiber averaging argument
finds one input catching at least a `2^-arity` share of all tuples, stated by
cross-multiplication. The remaining quantitative step is to bound the binomial
tail when too few individual survivors disagree. The tail layer does this using
ordered tuples with repetition and obtains the required `1/(2n)` shrink. The
remaining circuit-theoretic step is to obtain every-tuple coverage from target
hardness via majority composition.
-/


public section

namespace Complexity

namespace AntiChecker

/-- The finite type of canonical survivor codes has cardinality equal to the
canonical survivor count. -/
theorem card_survivorCode {arity : ℕ}
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity)) :
    Fintype.card (SurvivorCode target threshold inputs) =
      candidateSurvivorCount target threshold inputs :=
  card_survivorCode_internal target threshold inputs

/-- Catching a survivor tuple is exactly the statement that at most half of
its entries agree with the target at that input. -/
theorem isSurvivorTupleCaughtAt_iff_agreementCount_le
    {arity : ℕ} (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity)) (input : BitString arity)
    (tuple : Fin arity → SurvivorCode target threshold inputs) :
    IsSurvivorTupleCaughtAt target threshold inputs input tuple ↔
      survivorTupleAgreementCount target threshold inputs input tuple ≤
        arity / 2 :=
  isSurvivorTupleCaughtAt_iff_agreementCount_le_internal
    target threshold inputs input tuple

/-- Exact weighted-binomial count of survivor tuples caught at one input. -/
theorem card_caughtSurvivorTuples {arity : ℕ}
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity)) (input : BitString arity) :
    (caughtSurvivorTuples target threshold inputs input).card =
      ∑ disagreements ∈ Finset.Icc (arity - arity / 2) arity,
        arity.choose disagreements *
          (disagreeingSurvivors target threshold inputs input).card ^
            disagreements *
          (candidateSurvivorCount target threshold inputs -
              (disagreeingSurvivors target threshold inputs input).card) ^
            (arity - disagreements) :=
  card_caughtSurvivorTuples_internal target threshold inputs input

/-- Disagreeing survivors and survivors after adding the input partition the
current survivor set exactly. -/
theorem card_disagreeingSurvivors_add_next {arity : ℕ}
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity)) (input : BitString arity) :
    (disagreeingSurvivors target threshold inputs input).card +
        candidateSurvivorCount target threshold (input :: inputs) =
      candidateSurvivorCount target threshold inputs :=
  card_disagreeingSurvivors_add_next_internal
    target threshold inputs input

/-- A one-input extension shrinks by `1 / denominator` exactly when at least a
`1 / denominator` share of current survivors disagree there. -/
theorem isShrinkExtension_iff_survivorCount_le_mul_disagreements
    {arity denominator threshold : ℕ} (hdenominator : 0 < denominator)
    (target : BitString arity → Bool)
    (inputs : List (BitString arity)) (input : BitString arity) :
    IsShrinkExtension denominator target threshold inputs input ↔
      candidateSurvivorCount target threshold inputs ≤
        denominator *
          (disagreeingSurvivors target threshold inputs input).card :=
  isShrinkExtension_iff_survivorCount_le_mul_disagreements_internal
    hdenominator target inputs input

/-- If every survivor tuple is caught, some input catches at least a
`2^-arity` share of all survivor tuples, in exact cross-multiplied form. -/
theorem exists_input_many_caughtSurvivorTuples {arity : ℕ}
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity))
    (hall : EverySurvivorTupleCaught target threshold inputs) :
    ∃ input : BitString arity,
      candidateSurvivorCount target threshold inputs ^ arity ≤
        2 ^ arity *
          (caughtSurvivorTuples target threshold inputs input).card :=
  exists_input_many_caughtSurvivorTuples_internal
    target threshold inputs hall

end AntiChecker

end Complexity
