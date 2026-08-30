/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINKT.Gap.Logarithmic.Defs

/-!
# Efficient threshold search for logarithmic-gap MINKT -- definitions

This module gives the reverse direction of Fact 3.4 an explicit string
algorithm. On a canonical MINKT code `(x,1^t)`, it scans the thresholds
`0,...,t`, remembers the first one accepted by the supplied gap decider, and
returns that threshold in unary.

The loop state is the canonical nested tuple

`(base, counter, found, best)`.

The counter grows by one unary mark per iteration. Once `found` becomes true,
`best` is frozen. The loop runs `t+1` times, so threshold `t` is included.
-/


@[expose] public section

namespace Complexity

namespace GapMINKT

namespace Logarithmic

namespace Efficient

/-- Select between two strings using the first bit of a selector. An empty
selector yields the empty string. -/
def chooseHead (selector whenTrue whenFalse : List Bool) : List Bool :=
  if selector.head? = some true then whenTrue
  else if selector.head? = some false then whenFalse else []

/-- Initial threshold-sweep state `(base,0,false,clock)`. The clock is the
total fallback returned when no threshold is accepted. -/
def sweepInit (base : List Bool) : List Bool :=
  pair base (pair [] (pair [false] (pairSnd base)))

/-- One more than the unary clock length, so the sweep checks thresholds from
zero through the clock inclusively. -/
def sweepRuler (base : List Bool) : List Bool :=
  false :: pairSnd base

/-- A linear-width envelope for every threshold-sweep state. -/
def sweepWidth (base : List Bool) : List Bool :=
  pair (true :: true :: base)
    (pair (true :: pairSnd base) (true :: pairSnd base))

/-- One ascending threshold-search step.

The input state is `(base,counter,found,best)`. The decider is queried on the
canonical raw pair `(base,counter)`, `best` is set exactly at the first accepted
counter, and the counter then grows by one unary mark. -/
def sweepStep (decide : List Bool → Bool) (state : List Bool) : List Bool :=
  let base := pairFst state
  let counter := pairFst (pairSnd state)
  let found := pairFst (pairSnd (pairSnd state))
  let best := pairSnd (pairSnd (pairSnd state))
  let accepted := [decide (pair base counter)]
  let nextBest := chooseHead found best (chooseHead accepted counter best)
  let nextFound := chooseHead found [true] accepted
  pair base (pair (true :: counter) (pair nextFound nextBest))

/-- Unary output of the complete threshold sweep on an arbitrary base code. -/
def encodedTimeSearchEstimator (decide : List Bool → Bool)
    (base : List Bool) : List Bool :=
  let final :=
    (sweepStep decide)^[(sweepRuler base).length] (sweepInit base)
  pairSnd (pairSnd (pairSnd final))

/-- The numerical estimator represented by the unary sweep output on canonical
MINKT codes. -/
def executableEstimator (decide : List Bool → Bool) : Estimator :=
  fun inst => (encodedTimeSearchEstimator decide inst.encode).length

end Efficient

end Logarithmic

end GapMINKT

end Complexity
