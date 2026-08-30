/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.StatisticalTest.HybridPrediction.Defs
public import Complexitylib.Metacomplexity.StatisticalTest.HybridPrediction.Internal

/-!
# Next-bit prediction from an actual generator hybrid

This module splits the random bit at one hybrid coordinate from all remaining
randomness and transports the exact Yao prediction identity to the generator's
adjacent hybrid gap. The resulting theorem states exactly that the canonical
test-based predictor succeeds with probability `1/2 + hybridGap`.
-/


public section

namespace Complexity

namespace BitGenerator

/-- Uniform candidate acceptance is exactly acceptance on the current hybrid. -/
theorem candidateAcceptanceProbability_eq_hybrid
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool))
    (step : Fin outputLength) :
    NextBitPrediction.candidateAcceptanceProbability
        (generator.testAtCandidate test step) =
      generator.hybridAcceptanceProbability test step.val :=
  candidateAcceptanceProbability_eq_hybrid_internal generator test step

/-- Substituting the target generator bit is exactly acceptance on the next
hybrid. -/
theorem targetAcceptanceProbability_eq_nextHybrid
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool))
    (step : Fin outputLength) :
    NextBitPrediction.targetAcceptanceProbability
        (generator.targetBit step) (generator.testAtCandidate test step) =
      generator.hybridAcceptanceProbability test (step.val + 1) :=
  targetAcceptanceProbability_eq_nextHybrid_internal generator test step

/-- Exact next-bit theorem for the generator hybrid: the canonical predictor's
success probability is one half plus the adjacent hybrid gap. -/
theorem predictionSuccessProbability_eq_half_add_hybridGap
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool))
    (step : Fin outputLength) :
    NextBitPrediction.successProbability
        (generator.targetBit step) (generator.testAtCandidate test step) =
      1 / 2 + generator.hybridGap test step.val :=
  predictionSuccessProbability_eq_half_add_hybridGap_internal
    generator test step

end BitGenerator

end Complexity
