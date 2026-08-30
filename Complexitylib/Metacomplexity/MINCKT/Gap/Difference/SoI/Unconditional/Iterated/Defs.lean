/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Defs

/-!
# The iterated-clock schedule in the conditional MinKT reduction

This definitions layer records the exact clock schedule in Proposition 6.2 of
Hirahara's *Symmetry of Information from Meta-Complexity*. For
`t' = max {t, |x| + |y|}`, the two ordinary estimator queries use source clocks
`p(t')` and `p^3(t')`, symmetry of information is invoked at `p^2(t')`, and the
final conditional gap clock is `p^4(t + |x| + |y|)`.

The logarithmic losses are not hidden in asymptotic notation. `LossBudget`
states exactly what the correction must absorb and what must fit inside the
final logarithmic slack.
-/


@[expose] public section

namespace Complexity

namespace GapMINCKT

namespace DifferenceEstimator

namespace Unconditional

namespace Iterated

/-- Repeated application of a primitive clock. `clockIterate clock k time` is
the paper's `p^(k)(t)`. -/
def clockIterate (clock : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, time => time
  | iterations + 1, time => clock (clockIterate clock iterations time)

/-- The SoI base input `t' = max {t, |x| + |y|}`. -/
def paddedTime (inst : MINCKT.Instance) : ℕ :=
  max (inst.output.length + inst.condition.length) inst.time

/-- The ordinary gap estimator advances its source clock by one application
of `clock`; the output length is deliberately irrelevant. -/
def ordinaryParameters (clock : ℕ → ℕ) :
    GapMINKT.Logarithmic.Parameters where
  clock := fun _outputLength time => clock time

/-- The final conditional clock `p^4(t + |x| + |y|)`. -/
def conditionalParameters (clock : ℕ → ℕ) : GapMINCKT.Parameters where
  clock := fun outputLength conditionLength time =>
    clockIterate clock 4 (time + outputLength + conditionLength)

/-- The logarithmic SoI loss `log_2(p(t)) + additive`. -/
def logarithmicSoILoss (clock : ℕ → ℕ) (additive time : ℕ) : ℕ :=
  Nat.log 2 (clock time) + additive

/-- The exact two-query plan, with an explicit composition loss and centering
correction. -/
def plan (clock : ℕ → ℕ) (pairUpperLoss correction : MINCKT.Instance → ℕ) :
    Plan where
  pairInputTime := fun inst => clockIterate clock 1 (paddedTime inst)
  conditionInputTime := fun inst => clockIterate clock 3 (paddedTime inst)
  soiTime := fun inst => clockIterate clock 2 (paddedTime inst)
  pairUpperLoss := pairUpperLoss
  correction := correction

/-- The paper's half-slack centering correction. Its adequacy is deliberately
kept as a separate finite inequality in `LossBudget`. -/
def halfSlackCorrection (clock : ℕ → ℕ) (inst : MINCKT.Instance) : ℕ :=
  (conditionalParameters clock).logarithmicSlack inst / 2

/-- Exact finite loss inequalities for the iterated-clock construction.

The first field pays for the lower guarantee on the condition estimator and
the ordinary pair compiler. The second field fits the paired-estimator loss,
the SoI loss, and the centering correction inside the final gap slack. -/
structure LossBudget (clock : ℕ → ℕ)
    (pairUpperLoss correction : MINCKT.Instance → ℕ)
    (soiLoss : ℕ → ℕ) : Prop where
  /-- Losses that must be removed to obtain the source-clock upper estimate. -/
  upper : ∀ inst,
    Nat.log 2 (clockIterate clock 4 (paddedTime inst)) +
        pairUpperLoss inst ≤
      correction inst
  /-- Losses that must fit inside the final transformed-clock error. -/
  lower : ∀ inst,
    Nat.log 2 (clockIterate clock 2 (paddedTime inst)) +
          soiLoss (clockIterate clock 2 (paddedTime inst)) + correction inst ≤
      (conditionalParameters clock).logarithmicSlack inst

/-- Monotonicity and widening are the exact order properties used to align the
four iterated clocks. Polynomial growth is established separately. -/
structure IsRegularClock (clock : ℕ → ℕ) : Prop where
  /-- More source time cannot reduce the clock allowance. -/
  monotone : Monotone clock
  /-- One clock application never gives less time. -/
  dominates : ∀ time, time ≤ clock time

/-- A regular primitive clock with a uniform polynomial upper bound. -/
structure IsAdmissibleClock (clock : ℕ → ℕ) : Prop extends
    IsRegularClock clock where
  /-- One polynomial controls the primitive clock at every input. -/
  polynomiallyBounded : ∃ coefficient exponent, ∀ time,
    clock time ≤ coefficient * (time + 1) ^ exponent

end Iterated

end Unconditional

end DifferenceEstimator

end GapMINCKT

end Complexity
