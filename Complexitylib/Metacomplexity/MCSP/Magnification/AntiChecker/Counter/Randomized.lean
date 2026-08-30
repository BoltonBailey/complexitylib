/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Randomized.Defs
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Randomized.Internal

/-!
# Randomized anti-checker counters

This module exposes the exact derandomization step for the anti-checker
counter interface. A randomized multi-output counter with sufficiently small
pointwise failure probability yields a deterministic correct counter of
identical size by selecting and hardwiring one seed.
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

namespace RandomizedApproximateCounterCircuit

/-- A randomized counter satisfying the strict pointwise failure bound yields
a deterministic counter accurate on every fixed-width input. The construction
preserves exact circuit size. -/
theorem exists_correct_counter
    {overhead arity prefixLength seedWidth : ℕ}
    {beta : PositiveRationalScale}
    (randomized : RandomizedApproximateCounterCircuit overhead beta arity
      prefixLength seedWidth)
    (hcorrect : randomized.IsCorrect) :
    ∃ counter : ApproximateCounterCircuit overhead beta arity prefixLength,
      counter.IsCorrect ∧
        counter.circuit.size = randomized.circuit.size :=
  randomized.exists_correct_counter_internal hcorrect

end RandomizedApproximateCounterCircuit

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
