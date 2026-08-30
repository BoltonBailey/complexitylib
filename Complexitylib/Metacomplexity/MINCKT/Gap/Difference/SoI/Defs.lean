/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Kolmogorov.Symmetry.Defs
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.Defs

/-!
# SoI accounting for conditional-complexity difference estimators

This definitions layer exposes the exact inputs used to validate Hirahara's
difference estimator. It keeps the two clocks and three finite losses visible:

- a clock for the unconditional upper-chain bound on the pair;
- a base clock at which symmetry of information is applied;
- upper-chain, condition-estimator, and joint-estimator losses.

The transformed conditional clock may be later than the SoI clock at the
chosen base time. This is the `p^3`-to-`p^4` step in the paper. Two
natural-number budget inequalities state which losses are paid by the estimator
correction and which fit inside the final logarithmic slack.
-/


@[expose] public section

namespace Complexity

namespace GapMINCKT

namespace DifferenceEstimator

/-- Per-instance clocks and finite losses in the SoI difference argument. -/
structure SoIAccountingSchedule where
  /-- Base time at which the SoI lower-chain inequality is applied. -/
  soiTime : MINCKT.Instance → ℕ
  /-- Ordinary-machine clock used by the unconditional upper chain. -/
  pairUpperTime : MINCKT.Instance → ℕ
  /-- Additive program-composition loss in the upper chain. -/
  pairUpperLoss : MINCKT.Instance → ℕ
  /-- Additive loss in the lower estimate of condition complexity. -/
  conditionLowerLoss : MINCKT.Instance → ℕ
  /-- Additive loss in the lower estimate of joint complexity. -/
  pairLowerLoss : MINCKT.Instance → ℕ

/-- All estimator and clock inequalities that surround the single invocation
of symmetry of information.

This contract does not assume where the numerical components came from. A
later theorem may instantiate them from one unconditional Fact 3.4 estimator;
the current interface already forces every clock and loss to line up. -/
structure SatisfiesSoIInputs
    {ordinaryTapes conditionalTapes : ℕ}
    (components : DifferenceEstimator)
    (schedule : SoIAccountingSchedule)
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters) (soiClock soiLoss : ℕ → ℕ) : Prop where
  /-- The gap problem's transformed clock is at least the SoI target clock. -/
  soiClock_le_transformedTime : ∀ inst,
    soiClock (schedule.soiTime inst) ≤ parameters.transformedTime inst
  /-- Each chosen SoI base time is large enough for its pair. -/
  soiSize : ∀ inst,
    inst.output.length + inst.condition.length ≤ schedule.soiTime inst
  /-- The minuend is below an ordinary paired complexity used by the upper
  chain. -/
  minuend_upper : ∀ inst,
    (components.minuend inst : WithTop ℕ) ≤
      ordinaryMachine.timeBoundedKolmogorovComplexity
        (pair inst.output inst.condition) (schedule.pairUpperTime inst)
  /-- Unconditional upper chain at the source conditional and condition
  clocks. -/
  pair_upper : ∀ inst,
    ordinaryMachine.timeBoundedKolmogorovComplexity
          (pair inst.output inst.condition) (schedule.pairUpperTime inst) ≤
      inst.complexity conditionalMachine +
          ordinaryMachine.timeBoundedKolmogorovComplexity
            inst.condition inst.time +
        (schedule.pairUpperLoss inst : WithTop ℕ)
  /-- The later-clock condition complexity is below the subtrahend plus its
  estimator loss. -/
  condition_lower : ∀ inst,
    ordinaryMachine.timeBoundedKolmogorovComplexity inst.condition
          (parameters.transformedTime inst) ≤
      (components.subtrahend inst + schedule.conditionLowerLoss inst : ℕ)
  /-- The subtrahend itself is below the condition complexity appearing on the
  left of SoI. -/
  condition_upper : ∀ inst,
    (components.subtrahend inst : WithTop ℕ) ≤
      ordinaryMachine.timeBoundedKolmogorovComplexity inst.condition
        (soiClock (schedule.soiTime inst))
  /-- The ordinary paired complexity on the right of SoI is below the minuend
  plus its estimator loss. -/
  pair_lower : ∀ inst,
    ordinaryMachine.timeBoundedKolmogorovComplexity
          (pair inst.output inst.condition) (schedule.soiTime inst) ≤
      (components.minuend inst + schedule.pairLowerLoss inst : ℕ)
  /-- The correction pays both losses used in the upper accounting direction. -/
  upperLoss_budget : ∀ inst,
    schedule.conditionLowerLoss inst + schedule.pairUpperLoss inst ≤
      components.correction inst
  /-- The final logarithmic slack pays the joint lower loss, SoI loss, and the
  correction subtracted from the estimator. -/
  lowerLoss_budget : ∀ inst,
    schedule.pairLowerLoss inst + soiLoss (schedule.soiTime inst) +
        components.correction inst ≤
      parameters.logarithmicSlack inst

end DifferenceEstimator

end GapMINCKT

end Complexity
