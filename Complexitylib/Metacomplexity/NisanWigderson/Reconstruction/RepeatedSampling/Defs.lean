/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Averaging.Defs

/-!
# Repeated sampling of NW reconstruction advice -- definitions

Independent advice trials are represented by a function from a finite trial
index to the finite reconstruction-advice space. Success means that at least
one sampled advice attains the requested agreement threshold.
-/


@[expose] public section

namespace Complexity

namespace NWDesign

/-- Advice choices attaining a requested reconstruction-agreement threshold. -/
def goodReconstructionAdviceEvent
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength) (agreementThreshold : ℚ) :
    Finset (design.ReconstructionAdvice current) :=
  Finset.univ.filter fun advice =>
    agreementThreshold ≤
      design.reconstructionAgreementProbability hardFunction test current advice

/-- Probability that at least one of `trials` independent uniform advice draws
attains a requested reconstruction-agreement threshold. -/
def repeatedGoodReconstructionAdviceProbability
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength) (agreementThreshold : ℚ)
    (trials : ℕ) : ℚ :=
  uniformAtLeastOneProbability
    (design.goodReconstructionAdviceEvent hardFunction test current
      agreementThreshold)
    trials

end NWDesign

end Complexity
