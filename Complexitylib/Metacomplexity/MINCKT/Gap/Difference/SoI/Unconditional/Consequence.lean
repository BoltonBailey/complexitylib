/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Final
public import Complexitylib.Metacomplexity.MINCKT.Gap.Multiplicative

/-!
# The multiplicative-hardness consequence of conditional MinKT SoI

This module composes the complete finite spine of Hirahara's conditional MinKT
argument. An admissible primitive clock supplies a polynomial slack-amplified
gap clock, an operational condition-first compiler supplies the paired upper
chain, and one correct ordinary estimator plus time-bounded symmetry of
information supplies the conditional estimator. If the induced threshold
language is in `P`, NP-hardness of the corresponding multiplicative gap forces
`P = NP`.

Every remaining research obligation stays explicit in the theorem statement;
in particular, this result does not assert the SoI hypothesis, a concrete
universal evaluator, estimator efficiency, or multiplicative-gap hardness.
-/


public section

namespace Complexity

namespace GapMINCKT

namespace DifferenceEstimator

namespace Unconditional

namespace Iterated

namespace Slack

/-- The complete finite multiplicative-hardness consequence of the
slack-amplified SoI reduction.

The clock admissibility hypothesis proves that the final conditional clock is
both widening and polynomially bounded. Only widening is needed to construct
the promise; the polynomial bound remains available as part of the public
parameter theorem. -/
theorem P_eq_NP_of_multiplicative_hard_of_SoI
    {ordinaryTapes conditionalTapes : ℕ}
    {clock : ℕ → ℕ} (additive compilerLoss : ℕ)
    {composition : PairCompositionPlan}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (hclock : IsAdmissibleClock clock)
    (hsupports : SupportsPairUpper (plan clock compilerLoss) composition
      ordinaryMachine conditionalMachine)
    {ordinaryEstimate : GapMINKT.Logarithmic.Estimator}
    (hestimate : ordinaryEstimate.SatisfiesBounds ordinaryMachine
      (ordinaryParameters clock))
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine clock (logarithmicSoILoss clock additive))
    (factor : ℕ → ℕ) (hfactor : ∀ length, 1 ≤ factor length)
    (hhard : PromiseNPHard
      (GapMINCKT.Multiplicative.problem ordinaryMachine conditionalMachine
        (parameters clock additive compilerLoss) factor
          (Slack.IsAdmissibleClock.parameters_admissible hclock additive
            compilerLoss).widening
            hfactor))
    (hpolynomial : GapMINCKT.estimatorLanguage
      ((plan clock compilerLoss).components ordinaryEstimate).estimate ∈ P) :
    P = NP := by
  have hcompatible :=
    Slack.IsRegularClock.compatible_of_pairComposition
      (additive := additive) hclock.toIsRegularClock hsupports
  exact GapMINCKT.Multiplicative.P_eq_NP_of_hard_of_estimatorLanguage_mem_P
    ordinaryMachine conditionalMachine (parameters clock additive compilerLoss)
      factor (Slack.IsAdmissibleClock.parameters_admissible hclock additive
        compilerLoss).widening
        hfactor hhard
          (hcompatible.satisfiesBounds hestimate hsoi
            (Slack.IsAdmissibleClock.parameters_admissible hclock additive
              compilerLoss).widening)
          hpolynomial

/-- Assuming `P ≠ NP`, the simultaneous SoI, estimator-efficiency, compiler,
and multiplicative-hardness hypotheses are inconsistent. This is the precise
contrapositive needed before a future `DistNP ⊆ AvgP → SoI` theorem can rule
out Heuristica. -/
theorem not_timeBoundedSymmetryOfInformation_of_P_ne_NP
    {ordinaryTapes conditionalTapes : ℕ}
    {clock : ℕ → ℕ} (additive compilerLoss : ℕ)
    {composition : PairCompositionPlan}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (hclock : IsAdmissibleClock clock)
    (hsupports : SupportsPairUpper (plan clock compilerLoss) composition
      ordinaryMachine conditionalMachine)
    {ordinaryEstimate : GapMINKT.Logarithmic.Estimator}
    (hestimate : ordinaryEstimate.SatisfiesBounds ordinaryMachine
      (ordinaryParameters clock))
    (factor : ℕ → ℕ) (hfactor : ∀ length, 1 ≤ factor length)
    (hhard : PromiseNPHard
      (GapMINCKT.Multiplicative.problem ordinaryMachine conditionalMachine
        (parameters clock additive compilerLoss) factor
          (Slack.IsAdmissibleClock.parameters_admissible hclock additive
            compilerLoss).widening
            hfactor))
    (hpolynomial : GapMINCKT.estimatorLanguage
      ((plan clock compilerLoss).components ordinaryEstimate).estimate ∈ P)
    (hne : P ≠ NP) :
    ¬TimeBoundedSymmetryOfInformation ordinaryMachine conditionalMachine
      clock (logarithmicSoILoss clock additive) := by
  intro hsoi
  exact hne (P_eq_NP_of_multiplicative_hard_of_SoI additive compilerLoss
    ordinaryMachine conditionalMachine hclock hsupports hestimate hsoi factor
      hfactor hhard hpolynomial)

end Slack

end Iterated

end Unconditional

end DifferenceEstimator

end GapMINCKT

end Complexity
