/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.CircuitHardwiring
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Circuit.Defs

/-!
# Randomized anti-checker counters -- definitions

A randomized approximate counter circuit receives a random seed before the
fixed-width labeled-sample input and prints a little-endian count estimate. Its
correctness contract bounds, separately for every input, the uniform
probability that the estimate violates the existing relative-error predicate.

The failure exponent includes one bit of strict union-bound slack. This is the
exact finite contract needed to select one seed that is accurate on every
fixed-width input simultaneously.
-/


@[expose] public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- A counter output relatively approximates the labeled survivor count for
one fixed-width input. -/
def CounterOutputIsAccurate {arity prefixLength : ℕ}
    (beta : PositiveRationalScale)
    (input : BitString ((prefixLength + 1) * (arity + 1)))
    (output : BitString (counterOutputWidth beta arity)) : Prop :=
  AntiChecker.IsRelativeApproximation (roundPrecision arity)
    (candidateLabeledSurvivorCount arity (smallThreshold beta arity)
      (unpackLabeledSamples input))
    (counterValue output)

instance {arity prefixLength : ℕ} (beta : PositiveRationalScale)
    (input : BitString ((prefixLength + 1) * (arity + 1)))
    (output : BitString (counterOutputWidth beta arity)) :
    Decidable (CounterOutputIsAccurate beta input output) := by
  unfold CounterOutputIsAccurate AntiChecker.IsRelativeApproximation
  exact inferInstance

/-- A size-bounded randomized counter with random bits placed before its
labeled-sample input. Correctness is kept as the separate `IsCorrect`
predicate below, mirroring `ApproximateCounterCircuit`. -/
structure RandomizedApproximateCounterCircuit (overhead : ℕ)
    (beta : PositiveRationalScale) (arity prefixLength seedWidth : ℕ) where
  /-- Number of internal gates in the randomized counter circuit. -/
  internalGates : ℕ
  /-- Seed-prefix circuit that prints a little-endian count estimate. -/
  circuit : Circuit Basis.andOr2
    (seedWidth + (prefixLength + 1) * (arity + 1))
    (counterOutputWidth beta arity) internalGates
  /-- The same conditional size bound used by deterministic counters. -/
  size_le : circuit.size ≤ counterSizeBound overhead beta arity

namespace RandomizedApproximateCounterCircuit

/-- Seeds on which the randomized counter violates relative accuracy at one
fixed input. -/
def failureEvent {overhead arity prefixLength seedWidth : ℕ}
    {beta : PositiveRationalScale}
    (counter : RandomizedApproximateCounterCircuit overhead beta arity
      prefixLength seedWidth)
    (input : BitString ((prefixLength + 1) * (arity + 1))) :
    Finset (BitString seedWidth) :=
  Circuit.badSeedEvent counter.circuit
    (CounterOutputIsAccurate beta) input

/-- Every fixed input has failure probability at most one over
`2^(inputWidth + 1)`, leaving strict slack for a union bound over all inputs. -/
def IsCorrect {overhead arity prefixLength seedWidth : ℕ}
    {beta : PositiveRationalScale}
    (counter : RandomizedApproximateCounterCircuit overhead beta arity
      prefixLength seedWidth) : Prop :=
  ∀ input, eventProb (counter.failureEvent input) ≤
    1 / (2 : ℚ) ^ (((prefixLength + 1) * (arity + 1)) + 1)

end RandomizedApproximateCounterCircuit

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
