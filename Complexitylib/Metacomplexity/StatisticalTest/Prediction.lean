/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.StatisticalTest.Prediction.Defs
public import Complexitylib.Metacomplexity.StatisticalTest.Prediction.Internal

/-!
# The finite next-bit prediction experiment

This module proves the exact finite identity behind Yao's next-bit argument.
If replacing an independent candidate bit by its target raises test acceptance
by `gap`, then the predictor that trusts the candidate exactly on accepting
tests recovers the target with probability `1/2 + gap`.

The theorem is stated over an arbitrary nonempty finite background space, so
it can be instantiated with NW seeds and all random coordinates other than the
predicted bit without committing to a particular coordinate codec.
-/


public section

namespace Complexity

namespace NextBitPrediction

/-- Exact Yao prediction identity: success is one half plus the acceptance
gain from replacing the independent candidate by the target bit. -/
theorem successProbability_eq_half_add_gap
    {background : Type*} [Fintype background] [Nonempty background]
    (target : background → Bool) (testAt : background → Bool → Bool) :
    successProbability target testAt =
      1 / 2 + targetAcceptanceProbability target testAt -
        candidateAcceptanceProbability testAt :=
  successProbability_eq_half_add_gap_internal target testAt

end NextBitPrediction

end Complexity
