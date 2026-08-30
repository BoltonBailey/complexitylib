/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.ListDecoding.Defs
public
import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.ListDecoding.Internal

/-!
# List decoding explicit NW reconstruction programs

This layer composes checked, encoded NW reconstruction with a finite Boolean
list code. A selected predictor for an encoded source message yields a bounded
decoder candidate set containing the original message.
-/


public section

namespace Complexity

namespace NWDesign

/-- Explicit-program agreement with an encoded message is exactly the generic
Boolean list-code agreement statistic. -/
theorem ReconstructionProgram.agreementProbability_eq_listCode
    {messageLength listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram)
    (code : BooleanListCode messageLength listSize (Fin inputLength → Bool))
    (message : Fin messageLength → Bool)
    (test : Finset (Fin outputLength → Bool)) :
    program.agreementProbability (code.encode message) test =
      BooleanListCode.agreementProbability (code.encode message)
        (program.predictor test) :=
  program.agreementProbability_eq_listCode_internal code message test

/-- Sufficient stored-predictor agreement puts the original source message in
the decoder candidate set, whose cardinality is at most `listSize`. -/
theorem ReconstructionProgram.mem_listDecoderCandidates_and_card_le
    {messageLength listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram)
    (code : BooleanListCode messageLength listSize (Fin inputLength → Bool))
    (message : Fin messageLength → Bool)
    (test : Finset (Fin outputLength → Bool)) (margin : ℚ)
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (hagreement : 1 / 2 + margin ≤
      program.agreementProbability (code.encode message) test) :
    message ∈ program.listDecoderCandidates code test ∧
      (program.listDecoderCandidates code test).card ≤ listSize :=
  program.mem_listDecoderCandidates_and_card_le_internal
    code message test margin hcode hagreement

/-- Any checked certificate at agreement `1/2 + margin` produces a bounded
flat payload and a decoder list of size at most `listSize` containing the
original source message. -/
theorem findGoodReconstructionCertificate_listDecoding_sound
    {messageLength listSize outputLength inputLength seedLength trials budget : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (code : BooleanListCode messageLength listSize (Fin inputLength → Bool))
    (message : Fin messageLength → Bool)
    (test : Finset (Fin outputLength → Bool)) (margin : ℚ)
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (hbudget : design.HasOverlapBudget budget)
    (batch : Fin trials → ReconstructionTrial outputLength seedLength)
    (certificate : ReconstructionCertificate outputLength seedLength)
    (hfind : design.findGoodReconstructionCertificate? (code.encode message)
      test (1 / 2 + margin) batch = some certificate) :
    message ∈ (certificate.toProgram design
        (code.encode message)).listDecoderCandidates code test ∧
      ((certificate.toProgram design
        (code.encode message)).listDecoderCandidates code test).card ≤ listSize ∧
      (certificate.toProgram design
        (code.encode message)).encodeBooleanPayload.length ≤
          budget + (seedLength - inputLength) + 1 :=
  findGoodReconstructionCertificate_listDecoding_sound_internal
    design code message test margin hcode hbudget batch certificate hfind

/-- Finite semantic core of Hirahara's list-decoded NW reconstruction: with
probability at least one half, canonical checked sampling returns a bounded
payload whose predictor decodes to a bounded list containing the source
message. -/
theorem half_le_listDecodedReconstructionProgram_of_randomTest
    {messageLength listSize outputLength inputLength seedLength tapes time
      threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {code : BooleanListCode messageLength listSize (Fin inputLength → Bool)}
    {message : Fin messageLength → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 < density)
    (hcode : code.IsListDecodableAt
      (1 / 2 - (density / (outputLength : ℚ)) / 2))
    (hlow : (design.generator (code.encode message)).HasLowTimeBoundedComplexity
      machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability
          (code.encode message) test
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength density) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate? (code.encode message) test
            (1 / 2 + (density / (outputLength : ℚ)) / 2) batch =
          some certificate →
        message ∈ (certificate.toProgram design
            (code.encode message)).listDecoderCandidates code test ∧
          ((certificate.toProgram design
            (code.encode message)).listDecoderCandidates code test).card ≤ listSize ∧
          (certificate.toProgram design
            (code.encode message)).encodeBooleanPayload.length ≤
              budget + (seedLength - inputLength) + 1 :=
  half_le_listDecodedReconstructionProgram_of_randomTest_internal
    houtputLength hdensity hcode hlow hrandom hdense hbudget

/-- The list-decoded reconstruction theorem with generator complexity
discharged by direct short-seed descriptions. -/
theorem half_le_listDecodedReconstructionProgram_of_seedDescriptions
    {messageLength listSize outputLength inputLength seedLength tapes time
      threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {code : BooleanListCode messageLength listSize (Fin inputLength → Bool)}
    {message : Fin messageLength → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 < density)
    (hcode : code.IsListDecodableAt
      (1 / 2 - (density / (outputLength : ℚ)) / 2))
    (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (design.generator (code.encode message) seed)) time)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability
          (code.encode message) test
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength density) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate? (code.encode message) test
            (1 / 2 + (density / (outputLength : ℚ)) / 2) batch =
          some certificate →
        message ∈ (certificate.toProgram design
            (code.encode message)).listDecoderCandidates code test ∧
          ((certificate.toProgram design
            (code.encode message)).listDecoderCandidates code test).card ≤ listSize ∧
          (certificate.toProgram design
            (code.encode message)).encodeBooleanPayload.length ≤
              budget + (seedLength - inputLength) + 1 :=
  half_le_listDecodedReconstructionProgram_of_seedDescriptions_internal
    houtputLength hdensity hcode hseedLength hproduces hrandom hdense hbudget

end NWDesign

end Complexity
