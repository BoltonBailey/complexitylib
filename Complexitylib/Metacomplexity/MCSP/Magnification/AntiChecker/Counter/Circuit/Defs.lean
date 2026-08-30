/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Relation.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Rounds.Defs
public import Complexitylib.Metacomplexity.ScaledExponent.Defs

/-!
# Conditional anti-checker counter circuits -- definitions

For each sample-prefix length, an approximate counter circuit maps the
fixed-width labeled-sample encoding to a little-endian estimate of the number
of surviving canonical small-circuit codes. The circuit family and its size
bound are an explicit conditional interface: this file does not assert that
`NP ⊆ P/poly` supplies such families.
-/


@[expose] public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- Number of output bits allocated to one approximate survivor count. -/
def counterOutputWidth (beta : PositiveRationalScale) (arity : ℕ) : ℕ :=
  roundBlockCount beta arity + 1

instance (beta : PositiveRationalScale) (arity : ℕ) :
    NeZero (counterOutputWidth beta arity) :=
  ⟨by simp [counterOutputWidth]⟩

/-- Ceiling-rounded `2^(k*beta*n)` size bound for one counter circuit. -/
def counterSizeBound (overhead : ℕ) (beta : PositiveRationalScale)
    (arity : ℕ) : ℕ :=
  beta.powCeil (overhead * arity)

/-- One size-bounded approximate counter circuit for prefixes of length
`prefixLength + 1`. -/
structure ApproximateCounterCircuit (overhead : ℕ)
    (beta : PositiveRationalScale) (arity prefixLength : ℕ) where
  /-- Number of internal gates in the counter circuit. -/
  internalGates : ℕ
  /-- Circuit from packed labeled samples to a little-endian count estimate. -/
  circuit : Circuit Basis.andOr2
    ((prefixLength + 1) * (arity + 1))
    (counterOutputWidth beta arity) internalGates
  /-- Conditional per-counter circuit size bound. -/
  size_le : circuit.size ≤ counterSizeBound overhead beta arity

namespace ApproximateCounterCircuit

/-- Natural estimate printed by a counter circuit on one packed sample
vector. -/
def estimate {overhead arity prefixLength : ℕ}
    {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength)
    (input : BitString ((prefixLength + 1) * (arity + 1))) : ℕ :=
  counterValue (counter.circuit.eval input)

/-- A counter circuit relatively approximates the labeled survivor count on
every fixed-width input. -/
def IsCorrect {overhead arity prefixLength : ℕ}
    {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength) :
    Prop :=
  ∀ input,
    AntiChecker.IsRelativeApproximation (roundPrecision arity)
      (candidateLabeledSurvivorCount arity (smallThreshold beta arity)
        (unpackLabeledSamples input))
      (counter.estimate input)

end ApproximateCounterCircuit

/-- One approximate counter circuit for every prefix length used by the
anti-checker construction. -/
structure ApproximateCounterFamily (overhead : ℕ)
    (beta : PositiveRationalScale) (arity : ℕ) where
  /-- Counter for the next extension of a prefix of the indexed length. -/
  counter : (prefixLength : Fin (requiredRoundCount beta arity)) →
    ApproximateCounterCircuit overhead beta arity prefixLength.val

namespace ApproximateCounterFamily

/-- Every counter in the finite family satisfies its approximation contract. -/
def IsCorrect {overhead arity : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity) : Prop :=
  ∀ prefixLength, (family.counter prefixLength).IsCorrect

end ApproximateCounterFamily

/-- A correct bounded counter family exists at one arity. -/
def ExistsCorrectCounterFamilyAt (overhead : ℕ)
    (beta : PositiveRationalScale) (arity : ℕ) : Prop :=
  ∃ family : ApproximateCounterFamily overhead beta arity,
    family.IsCorrect

/-- Quantifier structure of the conditional approximate-counter conclusion:
one overhead works for every positive rational scale at all sufficiently large
arities. This proposition is defined but not proved here. -/
def HasApproximateCounterFamilies : Prop :=
  ∃ overhead : ℕ, ∀ beta : PositiveRationalScale,
    ∀ᶠ arity in Filter.atTop,
      ExistsCorrectCounterFamilyAt overhead beta arity

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
