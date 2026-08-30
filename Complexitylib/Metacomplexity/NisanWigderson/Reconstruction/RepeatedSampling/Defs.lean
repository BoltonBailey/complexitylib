/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Averaging.Defs
public import Mathlib.Data.Rat.Floor

/-!
# Repeated sampling of NW reconstruction advice -- definitions

Independent advice trials are represented by a function from a finite trial
index to the finite reconstruction-advice space. Success means that at least
one sampled advice attains the requested agreement threshold.
-/


@[expose] public section

namespace Complexity

namespace NWDesign

/-- Canonical number of independent advice trials for output length `m` and
positive density `δ`: the ceiling of `2m / δ`. The definition is total; its
sampling guarantee assumes positive density. -/
def reconstructionAdviceTrialCount (outputLength : ℕ) (density : ℚ) : ℕ :=
  Nat.ceil (2 * (outputLength : ℚ) / density)

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
