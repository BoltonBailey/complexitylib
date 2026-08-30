/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Circuit.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Circuit.Internal

/-!
# Conditional anti-checker counter circuits

This module exposes the exact bounded circuit-family contract used by the
Anti-Checker Lemma construction. `HasApproximateCounterFamilies` is only the
conditional conclusion to be obtained from a future `NP ⊆ P/poly` bridge; no
such implication is asserted here.
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- Counter output width is always positive. -/
theorem counterOutputWidth_pos
    (beta : PositiveRationalScale) (arity : ℕ) :
    0 < counterOutputWidth beta arity :=
  counterOutputWidth_pos_internal beta arity

/-- The conditional counter size bound is always positive. -/
theorem counterSizeBound_pos (overhead : ℕ)
    (beta : PositiveRationalScale) (arity : ℕ) :
    0 < counterSizeBound overhead beta arity :=
  counterSizeBound_pos_internal overhead beta arity

namespace ApproximateCounterCircuit

/-- Every fixed-width counter output denotes a value below its width bound. -/
theorem estimate_lt_two_pow
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength)
    (input : BitString ((prefixLength + 1) * (arity + 1))) :
    counter.estimate input < 2 ^ counterOutputWidth beta arity :=
  estimate_lt_two_pow_internal counter input

/-- Merely printing the count bits forces the output width below the stated
counter size bound. -/
theorem outputWidth_le_sizeBound
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength) :
    counterOutputWidth beta arity ≤
      counterSizeBound overhead beta arity :=
  outputWidth_le_sizeBound_internal counter

/-- Pointwise form of a counter circuit's correctness contract. -/
theorem approximates
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    {counter : ApproximateCounterCircuit overhead beta arity prefixLength}
    (hcorrect : counter.IsCorrect)
    (input : BitString ((prefixLength + 1) * (arity + 1))) :
    AntiChecker.IsRelativeApproximation (roundPrecision arity)
      (candidateLabeledSurvivorCount arity (smallThreshold beta arity)
        (unpackLabeledSamples input))
      (counter.estimate input) :=
  approximates_internal hcorrect input

end ApproximateCounterCircuit

namespace ApproximateCounterFamily

/-- Correctness of a family specializes to every indexed prefix length. -/
theorem counter_isCorrect {overhead arity : ℕ}
    {beta : PositiveRationalScale}
    {family : ApproximateCounterFamily overhead beta arity}
    (hcorrect : family.IsCorrect)
    (prefixLength : Fin (requiredRoundCount beta arity)) :
    (family.counter prefixLength).IsCorrect :=
  counter_isCorrect_internal hcorrect prefixLength

end ApproximateCounterFamily

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
