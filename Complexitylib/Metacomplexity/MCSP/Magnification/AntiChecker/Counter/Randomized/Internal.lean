/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Randomized.Defs

/-!
# Randomized anti-checker counters -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

namespace RandomizedApproximateCounterCircuit

theorem exists_correct_counter_internal
    {overhead arity prefixLength seedWidth : ℕ}
    {beta : PositiveRationalScale}
    (randomized : RandomizedApproximateCounterCircuit overhead beta arity
      prefixLength seedWidth)
    (hcorrect : randomized.IsCorrect) :
    ∃ counter : ApproximateCounterCircuit overhead beta arity prefixLength,
      counter.IsCorrect ∧
        counter.circuit.size = randomized.circuit.size := by
  have hfailure : ∀ input,
      eventProb (Circuit.badSeedEvent randomized.circuit
        (CounterOutputIsAccurate beta) input) ≤
          1 / (2 : ℚ) ^
            (((prefixLength + 1) * (arity + 1)) + 1) := by
    simpa only [IsCorrect, failureEvent] using hcorrect
  obtain ⟨fixed, hfixed, hsize⟩ :=
    Circuit.exists_hardwired_correct_circuit randomized.circuit
      (CounterOutputIsAccurate beta) hfailure
  let counter : ApproximateCounterCircuit overhead beta arity prefixLength :=
    { internalGates := randomized.internalGates
      circuit := fixed
      size_le := by
        rw [hsize]
        exact randomized.size_le }
  refine ⟨counter, ?_, ?_⟩
  · intro input
    simpa only [ApproximateCounterCircuit.estimate,
      CounterOutputIsAccurate, counter] using hfixed input
  · simpa only [counter] using hsize

end RandomizedApproximateCounterCircuit

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
