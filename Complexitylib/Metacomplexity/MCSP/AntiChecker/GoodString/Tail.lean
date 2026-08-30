/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.GoodString.Tail.Defs
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.GoodString.Tail.Internal

/-!
# Good-string binomial-tail bound

This module bounds the number of survivor tuples caught at one input. If `d`
of `r` survivors disagree, the caught ordered tuples are bounded by
`2^n * d^ceil(n/2) * r^floor(n/2)`.

Using ordered tuples with repetition gives a shorter formal route than the
distinct-subset estimate: finite averaging and the tail bound force some input
to have at least a `1/16` disagreement share. Consequently, at arity at least
eight, every-tuple coverage supplies the `1/(2n)` shrink required by the
Anti-Checker Lemma's approximate-selection round.
-/


public section

namespace Complexity

namespace AntiChecker

/-- Elementary weighted-binomial upper bound on the survivor tuples caught at
one input. -/
theorem card_caughtSurvivorTuples_le_upperBound {arity : ℕ}
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity)) (input : BitString arity) :
    (caughtSurvivorTuples target threshold inputs input).card ≤
      caughtTupleUpperBound arity
        (candidateSurvivorCount target threshold inputs)
        (disagreeingSurvivors target threshold inputs input).card :=
  card_caughtSurvivorTuples_le_upperBound_internal
    target threshold inputs input

/-- Every-tuple coverage forces some input to have at least a `1/16`
disagreement share among current survivors. -/
theorem exists_input_survivorCount_le_sixteen_mul_disagreements
    {arity : ℕ} (harity : 0 < arity)
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity))
    (hall : EverySurvivorTupleCaught target threshold inputs) :
    ∃ input : BitString arity,
      candidateSurvivorCount target threshold inputs ≤
        16 * (disagreeingSurvivors target threshold inputs input).card :=
  exists_input_survivorCount_le_sixteen_mul_disagreements_internal
    harity target threshold inputs hall

/-- At arity at least eight, every-tuple coverage gives a one-input survivor
shrink by the Anti-Checker Lemma's factor `1/(2n)`. -/
theorem hasShrinkExtension_two_mul_arity
    {arity : ℕ} (harity : 8 ≤ arity)
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity))
    (hall : EverySurvivorTupleCaught target threshold inputs) :
    HasShrinkExtension (2 * arity) target threshold inputs :=
  hasShrinkExtension_two_mul_arity_internal
    harity target threshold inputs hall

end AntiChecker

end Complexity
