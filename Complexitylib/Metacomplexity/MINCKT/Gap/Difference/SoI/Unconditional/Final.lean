/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Slack
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Growth
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Final.Internal

/-!
# Polynomial growth of the slack-amplified final clock

The power-of-two slack factor is bounded by the product of the three iterated
clocks appearing under its logarithms. Consequently the explicit slack
amplification remains polynomial and yields admissible conditional-gap
parameters.
-/


public section

namespace Complexity

namespace GapMINCKT

namespace DifferenceEstimator

namespace Unconditional

namespace Iterated

namespace Slack

/-- Adding one to a fixed polynomially bounded clock iterate preserves an
explicit polynomial bound. -/
theorem clockIterate_add_one_polynomiallyBounded
    {clock : ℕ → ℕ}
    (hclock : ∃ coefficient exponent, ∀ time,
      clock time ≤ coefficient * (time + 1) ^ exponent)
    (iterations : ℕ) :
    ∃ coefficient exponent, ∀ time,
      clockIterate clock iterations time + 1 ≤
        coefficient * (time + 1) ^ exponent :=
  clockIterate_add_one_polynomiallyBounded_internal hclock iterations

/-- The power-of-two slack factor is controlled by a product of the three
iterated query clocks and the two fixed losses. -/
theorem pow_slackExponent_le_product
    (clock : ℕ → ℕ) (additive compilerLoss : ℕ)
    (outputLength conditionLength time : ℕ) :
    2 ^ slackExponent clock additive compilerLoss
          outputLength conditionLength time ≤
      (clockIterate clock 2
            (totalTime outputLength conditionLength time) + 1) *
        (clockIterate clock 3
            (totalTime outputLength conditionLength time) + 1) *
        (clockIterate clock 4
            (totalTime outputLength conditionLength time) + 1) *
        2 ^ additive * 2 ^ compilerLoss :=
  pow_slackExponent_le_product_internal clock additive compilerLoss
    outputLength conditionLength time

/-- Polynomial growth of the primitive clock implies polynomial growth of the
slack-amplified final clock. -/
theorem finalClock_polynomiallyBounded
    {clock : ℕ → ℕ} (additive compilerLoss : ℕ)
    (hclock : ∃ coefficient exponent, ∀ time,
      clock time ≤ coefficient * (time + 1) ^ exponent) :
    ∃ coefficient exponent, ∀ outputLength conditionLength time,
      finalClock clock additive compilerLoss outputLength conditionLength time ≤
        coefficient * (outputLength + conditionLength + time + 1) ^ exponent :=
  finalClock_polynomiallyBounded_internal additive compilerLoss hclock

/-- An admissible primitive clock induces admissible slack-amplified
conditional-gap parameters. -/
theorem IsAdmissibleClock.parameters_admissible
    {clock : ℕ → ℕ} (hclock : IsAdmissibleClock clock)
    (additive compilerLoss : ℕ) :
    (parameters clock additive compilerLoss).IsAdmissible :=
  Slack.IsAdmissibleClock.parameters_admissible_internal hclock additive
    compilerLoss

end Slack

end Iterated

end Unconditional

end DifferenceEstimator

end GapMINCKT

end Complexity
