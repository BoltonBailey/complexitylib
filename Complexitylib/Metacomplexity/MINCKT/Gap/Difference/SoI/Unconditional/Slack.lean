/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Iterated
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Slack.Defs
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Slack.Internal

/-!
# Explicit slack amplification for the conditional MinKT reduction

The final clock is enlarged constructively so that its base-two logarithm pays
the paired-estimator loss, the condition-estimator loss, the SoI loss, and the
fixed pair compiler overhead. This removes the two abstract `LossBudget`
inequalities from the exact two-query reduction.
-/


public section

namespace Complexity

namespace GapMINCKT

namespace DifferenceEstimator

namespace Unconditional

namespace Iterated

namespace Slack

/-- The slack-amplified clock dominates the source time. -/
theorem finalClock_source_le
    (clock : ℕ → ℕ) (additive compilerLoss : ℕ)
    (outputLength conditionLength time : ℕ) :
    time ≤ finalClock clock additive compilerLoss
      outputLength conditionLength time :=
  finalClock_source_le_internal clock additive compilerLoss
    outputLength conditionLength time

/-- The slack-amplified clock dominates the fourfold query clock. -/
theorem finalClock_iterateFour_le
    (clock : ℕ → ℕ) (additive compilerLoss : ℕ)
    (outputLength conditionLength time : ℕ) :
    clockIterate clock 4 (totalTime outputLength conditionLength time) ≤
      finalClock clock additive compilerLoss
        outputLength conditionLength time :=
  finalClock_iterateFour_le_internal clock additive compilerLoss
    outputLength conditionLength time

/-- The final logarithmic slack contains its complete explicit loss
exponent. -/
theorem slackExponent_le_log_finalClock
    (clock : ℕ → ℕ) (additive compilerLoss : ℕ)
    (outputLength conditionLength time : ℕ) :
    slackExponent clock additive compilerLoss
        outputLength conditionLength time ≤
      Nat.log 2 (finalClock clock additive compilerLoss
        outputLength conditionLength time) :=
  slackExponent_le_log_finalClock_internal clock additive compilerLoss
    outputLength conditionLength time

/-- Monotonicity moves all three query losses from `t'` to the total source
parameter, after which the amplified final slack pays them. -/
theorem lowerLoss_budget
    {clock : ℕ → ℕ} (hclock : Monotone clock)
    (additive compilerLoss : ℕ) (inst : MINCKT.Instance) :
    (ordinaryParameters clock).logarithmicSlack
          ((plan clock compilerLoss).pairInput inst) +
          logarithmicSoILoss clock additive
            ((plan clock compilerLoss).soiTime inst) +
        (plan clock compilerLoss).correction inst ≤
      (parameters clock additive compilerLoss).logarithmicSlack inst :=
  lowerLoss_budget_internal hclock additive compilerLoss inst

/-- The constructive correction exactly pays the condition-query and compiler
losses. -/
theorem upperLoss_budget
    (clock : ℕ → ℕ) (compilerLoss : ℕ)
    (inst : MINCKT.Instance) :
    (ordinaryParameters clock).logarithmicSlack
          ((plan clock compilerLoss).conditionInput inst) +
        (plan clock compilerLoss).pairUpperLoss inst ≤
      (plan clock compilerLoss).correction inst :=
  upperLoss_budget_internal clock compilerLoss inst

/-- Slack amplification and the paired upper-chain theorem produce the full
compatibility contract with no remaining clock or loss hypotheses. -/
theorem IsRegularClock.compatible
    {ordinaryTapes conditionalTapes : ℕ}
    {clock : ℕ → ℕ} {additive compilerLoss : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    (hclock : IsRegularClock clock)
    (hpair : ∀ inst,
      ordinaryMachine.timeBoundedKolmogorovComplexity
            (pair inst.output inst.condition)
              ((plan clock compilerLoss).pairInputTime inst) ≤
        inst.complexity conditionalMachine +
            ordinaryMachine.timeBoundedKolmogorovComplexity
              inst.condition inst.time +
          ((plan clock compilerLoss).pairUpperLoss inst : WithTop ℕ)) :
    Compatible (plan clock compilerLoss) ordinaryMachine conditionalMachine
      (ordinaryParameters clock) (parameters clock additive compilerLoss) clock
        (logarithmicSoILoss clock additive) :=
  Slack.IsRegularClock.compatible_internal hclock hpair

/-- The operational condition-first compiler closes the last machine-specific
premise of the slack-amplified schedule. -/
theorem IsRegularClock.compatible_of_pairComposition
    {ordinaryTapes conditionalTapes : ℕ}
    {clock : ℕ → ℕ} {additive compilerLoss : ℕ}
    {composition : PairCompositionPlan}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    (hclock : IsRegularClock clock)
    (hsupports : SupportsPairUpper (plan clock compilerLoss) composition
      ordinaryMachine conditionalMachine) :
    Compatible (plan clock compilerLoss) ordinaryMachine conditionalMachine
      (ordinaryParameters clock) (parameters clock additive compilerLoss) clock
        (logarithmicSoILoss clock additive) :=
  Slack.IsRegularClock.compatible_of_pairComposition_internal hclock hsupports

end Slack

end Iterated

end Unconditional

end DifferenceEstimator

end GapMINCKT

end Complexity
