/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.AverageCase.FiniteEnsemble.Defs

/-!
# The finite next-bit prediction experiment -- definitions

For each background state `omega`, an experiment has a target bit and a test
whose outcome depends on a uniformly random candidate bit. The Yao predictor
returns the candidate when the test accepts and its complement when the test
rejects. All three probabilities use exact uniform finite sample spaces.
-/


@[expose] public section

namespace Complexity

namespace NextBitPrediction

/-- Predict the candidate bit when the test accepts and its complement when
the test rejects. This is `testResult XOR candidate XOR 1`. -/
def predictFromTest (testResult candidate : Bool) : Bool :=
  (testResult.xor candidate).xor true

/-- Test acceptance when the candidate bit is uniform and independent of the
background state. -/
noncomputable def candidateAcceptanceProbability {background : Type*}
    [Fintype background] (testAt : background → Bool → Bool) : ℚ := by
  classical
  exact uniformProbability <|
    Finset.univ.filter fun sample : background × Bool =>
      testAt sample.1 sample.2 = true

/-- Test acceptance when the candidate is replaced by the target bit. -/
noncomputable def targetAcceptanceProbability {background : Type*}
    [Fintype background] (target : background → Bool)
    (testAt : background → Bool → Bool) : ℚ := by
  classical
  exact uniformProbability <|
    Finset.univ.filter fun omega : background =>
      testAt omega (target omega) = true

/-- Probability that the test-based predictor recovers the target from a
uniform independent candidate bit. -/
noncomputable def successProbability {background : Type*}
    [Fintype background] (target : background → Bool)
    (testAt : background → Bool → Bool) : ℚ := by
  classical
  exact uniformProbability <|
    Finset.univ.filter fun sample : background × Bool =>
      predictFromTest (testAt sample.1 sample.2) sample.2 = target sample.1

end NextBitPrediction

end Complexity
