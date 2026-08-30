/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.GlobalSampling.Defs

/-!
# Executable NW reconstruction certificate search -- definitions

A reconstruction certificate records a polarity for the statistical test and
one globally sampled coordinate/advice trial. Its quality is checked by exact
finite truth-table agreement. A batch search tries both polarities for every
sampled trial and returns the first certificate meeting the requested
threshold.
-/


@[expose] public section

namespace Complexity

namespace NWDesign

/-- Finite reconstruction data selected by the randomized search: a polarity
bit and one globally sampled coordinate/advice trial. -/
structure ReconstructionCertificate (outputLength seedLength : ℕ) where
  /-- Whether to complement the supplied statistical test. -/
  complement : Bool
  /-- The coordinate and fixed-width raw reconstruction advice. -/
  trial : ReconstructionTrial outputLength seedLength

/-- A reconstruction certificate is good when its induced predictor has at
least the requested exact truth-table agreement. -/
def IsGoodReconstructionCertificate
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (agreementThreshold : ℚ)
    (certificate : ReconstructionCertificate outputLength seedLength) : Prop :=
  agreementThreshold ≤
    design.reconstructionTrialAgreementProbability hardFunction
      (BitGenerator.orientTest test certificate.complement) certificate.trial

/-- Executable exact-agreement checker for a finite reconstruction
certificate. -/
def reconstructionCertificatePasses
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (agreementThreshold : ℚ)
    (certificate : ReconstructionCertificate outputLength seedLength) : Bool :=
  decide <| agreementThreshold ≤
    design.reconstructionTrialAgreementProbability hardFunction
      (BitGenerator.orientTest test certificate.complement) certificate.trial

/-- Try both test polarities for one sampled reconstruction trial. -/
def checkReconstructionTrial?
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (agreementThreshold : ℚ)
    (trial : ReconstructionTrial outputLength seedLength) :
    Option (ReconstructionCertificate outputLength seedLength) :=
  let direct : ReconstructionCertificate outputLength seedLength :=
    ⟨false, trial⟩
  if design.reconstructionCertificatePasses hardFunction test
      agreementThreshold direct then
    some direct
  else
    let complemented : ReconstructionCertificate outputLength seedLength :=
      ⟨true, trial⟩
    if design.reconstructionCertificatePasses hardFunction test
        agreementThreshold complemented then
      some complemented
    else
      none

/-- Search a finite batch of global reconstruction trials, trying both test
polarities at every coordinate/advice sample. -/
def findGoodReconstructionCertificate?
    {outputLength inputLength seedLength trials : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (agreementThreshold : ℚ)
    (batch : Fin trials → ReconstructionTrial outputLength seedLength) :
    Option (ReconstructionCertificate outputLength seedLength) :=
  Fin.findSome? fun index =>
    design.checkReconstructionTrial? hardFunction test agreementThreshold
      (batch index)

/-- Batches on which exact checking finds a reconstruction certificate. -/
def checkedReconstructionBatchEvent
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (agreementThreshold : ℚ) (trials : ℕ) :
    Finset (Fin trials → ReconstructionTrial outputLength seedLength) :=
  Finset.univ.filter fun batch =>
    (design.findGoodReconstructionCertificate? hardFunction test
      agreementThreshold batch).isSome

/-- Probability that exact checking of a uniform batch finds a reconstruction
certificate in either test orientation. -/
def checkedReconstructionBatchSuccessProbability
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (agreementThreshold : ℚ) (trials : ℕ) : ℚ :=
  uniformProbability <|
    design.checkedReconstructionBatchEvent hardFunction test
      agreementThreshold trials

end NWDesign

end Complexity
