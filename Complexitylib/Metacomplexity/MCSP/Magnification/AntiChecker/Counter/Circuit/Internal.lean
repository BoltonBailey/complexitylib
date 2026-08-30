/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Circuit.Defs
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Encoding.Internal
import Complexitylib.Metacomplexity.ScaledExponent

/-!
# Conditional anti-checker counter circuits -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

theorem counterOutputWidth_pos_internal
    (beta : PositiveRationalScale) (arity : ℕ) :
    0 < counterOutputWidth beta arity := by
  unfold counterOutputWidth
  omega

theorem counterSizeBound_pos_internal (overhead : ℕ)
    (beta : PositiveRationalScale) (arity : ℕ) :
    0 < counterSizeBound overhead beta arity := by
  exact PositiveRationalScale.powCeil_pos beta (overhead * arity)

namespace ApproximateCounterCircuit

theorem estimate_lt_two_pow_internal
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength)
    (input : BitString ((prefixLength + 1) * (arity + 1))) :
    counter.estimate input < 2 ^ counterOutputWidth beta arity :=
  counterValue_lt_two_pow_internal (counter.circuit.eval input)

theorem outputWidth_le_sizeBound_internal
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength) :
    counterOutputWidth beta arity ≤
      counterSizeBound overhead beta arity := by
  apply le_trans _ counter.size_le
  simp [Circuit.size]

theorem approximates_internal
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    {counter : ApproximateCounterCircuit overhead beta arity prefixLength}
    (hcorrect : counter.IsCorrect)
    (input : BitString ((prefixLength + 1) * (arity + 1))) :
    AntiChecker.IsRelativeApproximation (roundPrecision arity)
      (candidateLabeledSurvivorCount arity (smallThreshold beta arity)
        (unpackLabeledSamples input))
      (counter.estimate input) :=
  hcorrect input

end ApproximateCounterCircuit

namespace ApproximateCounterFamily

theorem counter_isCorrect_internal {overhead arity : ℕ}
    {beta : PositiveRationalScale}
    {family : ApproximateCounterFamily overhead beta arity}
    (hcorrect : family.IsCorrect)
    (prefixLength : Fin (requiredRoundCount beta arity)) :
    (family.counter prefixLength).IsCorrect :=
  hcorrect prefixLength

end ApproximateCounterFamily

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
