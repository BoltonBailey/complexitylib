/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Iterated.Defs

/-!
# Explicit slack amplification for the conditional MinKT reduction

The literal fourfold clock identifies the final gap slack with
`log_2(p^4(t + |x| + |y|))`, while the reduction must pay three logarithmic
losses, the SoI additive constant, and the pair compiler. This module defines a
larger final clock whose logarithm pays those terms by construction.

The enlargement remains a finite product of fixed polynomial clocks. Its
polynomial-growth proof is kept separate from the finite loss accounting.
-/


@[expose] public section

namespace Complexity

namespace GapMINCKT

namespace DifferenceEstimator

namespace Unconditional

namespace Iterated

namespace Slack

/-- The total source parameter `t + |x| + |y|`. -/
def totalTime (outputLength conditionLength time : ℕ) : ℕ :=
  time + outputLength + conditionLength

/-- Exponent containing every logarithmic loss that the conditional estimator
must pay. The `+ 1` terms make the clock total even at time zero. -/
def slackExponent (clock : ℕ → ℕ) (additive compilerLoss : ℕ)
    (outputLength conditionLength time : ℕ) : ℕ :=
  let total := totalTime outputLength conditionLength time
  Nat.log 2 (clockIterate clock 2 total + 1) +
      Nat.log 2 (clockIterate clock 3 total + 1) +
    Nat.log 2 (clockIterate clock 4 total + 1) + additive + compilerLoss

/-- Slack-amplified final clock.

The power of two makes its logarithm at least `slackExponent`. The remaining
factors ensure that it dominates both the fourfold query clock and the source
time, including degenerate zero inputs. -/
def finalClock (clock : ℕ → ℕ) (additive compilerLoss : ℕ)
    (outputLength conditionLength time : ℕ) : ℕ :=
  let total := totalTime outputLength conditionLength time
  2 ^ slackExponent clock additive compilerLoss outputLength conditionLength time *
    ((clockIterate clock 4 total + 1) * (total + 1))

/-- Conditional gap parameters using the slack-amplified final clock. -/
def parameters (clock : ℕ → ℕ) (additive compilerLoss : ℕ) :
    GapMINCKT.Parameters where
  clock := finalClock clock additive compilerLoss

/-- The centering correction pays the condition-estimator loss and the fixed
pair compiler loss exactly. -/
def correction (clock : ℕ → ℕ) (compilerLoss : ℕ)
    (inst : MINCKT.Instance) : ℕ :=
  Nat.log 2 (clockIterate clock 4 (paddedTime inst)) + compilerLoss

/-- Exact two-query plan with constant pair compiler loss and constructive
centering correction. -/
def plan (clock : ℕ → ℕ) (compilerLoss : ℕ) : Plan :=
  Iterated.plan clock (fun _inst => compilerLoss) (correction clock compilerLoss)

end Slack

end Iterated

end Unconditional

end DifferenceEstimator

end GapMINCKT

end Complexity
