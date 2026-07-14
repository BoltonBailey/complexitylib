/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Control.Defs

/-!
# Pointwise envelopes for binary-loop space bounds -- definitions

`BinaryRoutine.binaryForSpace` stores an input-dependent maximum over every
loop iteration. To prove an asymptotic bound, clients should not expand or
sum that recurrence: it is enough to exhibit one pointwise envelope covering
the comparison scan, the initial configuration, and both phases of every
reachable iteration.
-/

namespace Complexity

namespace BinaryRoutine

/-- A single pointwise upper bound for every component of one binary
count-up loop's advertised auxiliary-space budget. -/
structure BinaryForSpaceEnvelope (body : BinaryRoutine n)
    (counterIdx limitIdx : Fin n) (initialSpace : ℕ)
    (initial : BinaryValues n) (bound : ℕ) : Prop where
  /-- The full-width counter/limit comparison fits in the envelope. -/
  compareSpace :
    initialSpace + TM.binaryForCompareTime (initial limitIdx) ≤ bound
  /-- The zero-iteration base case fits in the envelope. -/
  initialSpace_le : initialSpace ≤ bound
  /-- Every reachable body invocation fits in the envelope. -/
  bodySpace : ∀ count,
    count < binaryForCount counterIdx limitIdx initial →
      body.spaceBound initialSpace
        (binaryForValues body counterIdx initial count) ≤ bound
  /-- Every reachable controller successor fits in the envelope. -/
  successorSpace : ∀ count,
    count < binaryForCount counterIdx limitIdx initial →
      let current := binaryForValues body counterIdx initial count
      initialSpace + TM.binarySuccTime (current counterIdx) ≤ bound

end BinaryRoutine

end Complexity
