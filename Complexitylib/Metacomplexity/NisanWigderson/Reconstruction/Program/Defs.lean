/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.CertificateSearch.Defs

/-!
# Explicit NW reconstruction programs -- definitions

The earlier reconstruction predictor was written using the hard function to
construct its predecessor tables. This module materializes those finite tables
as fields of a reconstruction program. Evaluation of the resulting program
uses only its stored data, the fixed statistical test, and the challenge.
-/


@[expose] public section

namespace Complexity

namespace NWDesign

/-- Self-contained finite data used by an oriented NW reconstruction
predictor. The predecessor tables are stored explicitly for precisely the
coordinates earlier than `current`. -/
structure ReconstructionProgram
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength) where
  /-- Whether the fixed statistical test is complemented. -/
  complement : Bool
  /-- Hybrid coordinate whose hard-function value is predicted. -/
  current : Fin outputLength
  /-- Hardwired truth tables for all earlier NW output coordinates. -/
  predecessor : (previous : Finset.Iio current) →
    (design.challengeOverlap current previous.1 → Bool) → Bool
  /-- Seed bits outside the challenged design block. -/
  outside : design.outsideCoordinates current → Bool
  /-- Fixed NW output bits later than the challenged coordinate. -/
  later : laterCoordinates current → Bool
  /-- Candidate value supplied at the challenged coordinate. -/
  candidate : Bool

/-- Materialize all predecessor tables used by a fixed-advice reconstruction
predictor. After this construction, evaluation no longer queries
`hardFunction`. -/
def materializeReconstructionProgram
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (complement : Bool) (current : Fin outputLength)
    (advice : design.ReconstructionAdvice current) :
    design.ReconstructionProgram where
  complement := complement
  current := current
  predecessor previous :=
    design.predecessorTable current previous.1
      (design.outsideSeed current advice.1) hardFunction
  outside := advice.1
  later := advice.2.1
  candidate := advice.2.2

/-- Materialize the explicit reconstruction program named by a checked
certificate. -/
def ReconstructionCertificate.toProgram
    {outputLength inputLength seedLength : ℕ}
    (certificate : ReconstructionCertificate outputLength seedLength)
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool) :
    design.ReconstructionProgram :=
  design.materializeReconstructionProgram hardFunction
    certificate.complement certificate.trial.1
    (design.reconstructionAdviceOfTrial certificate.trial)

namespace ReconstructionProgram

/-- Output query assembled entirely from an explicit reconstruction program. -/
def query
    {outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram)
    (challenge : Fin inputLength → Bool) : Fin outputLength → Bool :=
  fun output =>
    if houtput : output ∈ Finset.Iio program.current then
      program.predecessor ⟨output, houtput⟩
        (BooleanDependency.restrict
          (design.challengeOverlap program.current output) challenge)
    else
      Function.update (laterTail program.current program.later)
        program.current program.candidate output

/-- Evaluate the oriented fixed statistical test on an explicit program's
query. -/
def testAtCandidate
    {outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram)
    (test : Finset (Fin outputLength → Bool))
    (challenge : Fin inputLength → Bool) : Bool :=
  decide (program.query challenge ∈
    BitGenerator.orientTest test program.complement)

/-- Boolean predictor evaluated solely from the stored program and fixed
statistical test. -/
def predictor
    {outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram)
    (test : Finset (Fin outputLength → Bool)) :
    (Fin inputLength → Bool) → Bool :=
  fun challenge => NextBitPrediction.predictFromTest
    (program.testAtCandidate test challenge) program.candidate

/-- Exact uniform agreement of an explicit program with a target hard
function. The target is used only to score the stored predictor. -/
def agreementProbability
    {outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool)) : ℚ :=
  uniformProbability <| Finset.univ.filter fun challenge =>
    program.predictor test challenge = hardFunction challenge

/-- Number of Boolean payload entries stored by a reconstruction program.
The polarity and coordinate are metadata handled by the later codec layer. -/
def booleanPayloadSize
    {outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram) : ℕ :=
  (Finset.univ.sum fun previous : Finset.Iio program.current =>
      Fintype.card
        (design.challengeOverlap program.current previous.1 → Bool)) +
    Fintype.card (design.outsideCoordinates program.current) +
    Fintype.card (laterCoordinates program.current) + 1

end ReconstructionProgram

end NWDesign

end Complexity
