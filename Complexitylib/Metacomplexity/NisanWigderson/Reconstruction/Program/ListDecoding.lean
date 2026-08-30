/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.ListDecoding.Defs
public
import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.ListDecoding.Internal
public
import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.ListDecoding.Family

/-!
# List decoding explicit NW reconstruction programs

This layer composes checked, encoded NW reconstruction with a finite Boolean
list code. Beyond producing a bounded candidate set containing the source
message, it stores a selecting decoder index in ceiling-logarithmic space and
materializes a program that decodes exactly to the source message. Its complete
codec includes polarity, hybrid coordinate, reconstruction data, and list
index, leaving only ambient parameters external. The family specialization
matches inverse accuracy to reconstruction advantage and converts polynomial
list size into a concrete logarithmic description bound, including the
canonical choice for inverse-polynomially represented test density.
-/


public section

namespace Complexity

namespace NWDesign

/-- The flat Boolean payload of an indexed reconstruction program consists of
the reconstruction data followed by exactly `clog₂(listSize)` index bits. -/
@[simp] theorem IndexedReconstructionProgram.length_encodeBooleanPayload
    {listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : IndexedReconstructionProgram design listSize) :
    program.encodeBooleanPayload.length =
      design.reconstructionDataBitsAt program.reconstruction.current +
        BooleanListCode.decoderIndexBitWidth listSize :=
  program.length_encodeBooleanPayload_internal

/-- Complete indexed-program encoding accounts exactly for polarity, hybrid
coordinate, reconstruction data, and list-decoder index. -/
@[simp] theorem IndexedReconstructionProgram.length_encode
    {listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : IndexedReconstructionProgram design listSize) :
    program.encode.length =
      1 + Fin.bitWidth outputLength +
        design.reconstructionDataBitsAt program.reconstruction.current +
          BooleanListCode.decoderIndexBitWidth listSize :=
  program.length_encode_internal

/-- The concatenated reconstruction-data and list-index encoding round-trips
when polarity and hybrid coordinate are supplied as codec metadata. -/
theorem decodeIndexedReconstructionBooleanPayload?_encode
    {listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : IndexedReconstructionProgram design listSize) :
    decodeIndexedReconstructionBooleanPayload? design listSize
      program.reconstruction.complement program.reconstruction.current
        program.encodeBooleanPayload = some program :=
  decodeIndexedReconstructionBooleanPayload?_encode_internal program

/-- Complete indexed reconstruction encoding round-trips from its ambient
design and list-size parameters alone. -/
@[simp] theorem decodeIndexedReconstructionProgram?_encode
    {listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : IndexedReconstructionProgram design listSize) :
    decodeIndexedReconstructionProgram? design listSize program.encode =
      some program :=
  decodeIndexedReconstructionProgram?_encode_internal program

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

/-- Sufficient agreement materializes an indexed reconstruction program that
decodes exactly to the original source message. Its extra Boolean payload is
exactly one ceiling-logarithmic list index. -/
theorem ReconstructionProgram.exists_indexedProgram_of_half_add_margin
    {messageLength listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram)
    (code : BooleanListCode messageLength listSize (Fin inputLength → Bool))
    (message : Fin messageLength → Bool)
    (test : Finset (Fin outputLength → Bool)) (margin : ℚ)
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (hagreement : 1 / 2 + margin ≤
      program.agreementProbability (code.encode message) test) :
    ∃ indexed : IndexedReconstructionProgram design listSize,
      indexed.reconstruction = program ∧
        indexed.decodedMessage code test = message ∧
          indexed.encodeBooleanPayload.length =
            program.encodeBooleanPayload.length +
              BooleanListCode.decoderIndexBitWidth listSize :=
  program.exists_indexedProgram_of_half_add_margin_internal
    code message test margin hcode hagreement

/-- A checked certificate yields an indexed reconstruction program that
recovers the source message and whose actual Boolean payload includes the
ceiling-logarithmic decoder index. -/
theorem findGoodReconstructionCertificate_indexedProgram_sound
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
    ∃ indexed : IndexedReconstructionProgram design listSize,
      indexed.reconstruction =
          certificate.toProgram design (code.encode message) ∧
        indexed.decodedMessage code test = message ∧
          indexed.encodeBooleanPayload.length ≤
            budget + (seedLength - inputLength) + 1 +
              BooleanListCode.decoderIndexBitWidth listSize :=
  findGoodReconstructionCertificate_indexedProgram_sound_internal
    design code message test margin hcode hbudget batch certificate hfind

/-- A checked certificate yields a complete, round-tripping indexed program
that recovers the source message. Its bound accounts for polarity, hybrid
coordinate, reconstruction data, and decoder-list index. -/
theorem findGoodReconstructionCertificate_fullyEncodedIndexedProgram_sound
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
    ∃ indexed : IndexedReconstructionProgram design listSize,
      indexed.reconstruction =
          certificate.toProgram design (code.encode message) ∧
        indexed.decodedMessage code test = message ∧
          indexed.encode.length ≤
            1 + Fin.bitWidth outputLength +
              (budget + (seedLength - inputLength) + 1) +
                BooleanListCode.decoderIndexBitWidth listSize :=
  findGoodReconstructionCertificate_fullyEncodedIndexedProgram_sound_internal
    design code message test margin hcode hbudget batch certificate hfind

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

/-- With probability at least one half, canonical checked sampling returns a
certificate that extends to an indexed program decoding exactly to the source
message. The actual Boolean payload pays only `clog₂(listSize)` bits beyond
the reconstruction payload. -/
theorem half_le_indexedReconstructionProgram_of_randomTest
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
        ∃ indexed : IndexedReconstructionProgram design listSize,
          indexed.reconstruction =
              certificate.toProgram design (code.encode message) ∧
            indexed.decodedMessage code test = message ∧
              indexed.encodeBooleanPayload.length ≤
                budget + (seedLength - inputLength) + 1 +
                  BooleanListCode.decoderIndexBitWidth listSize :=
  half_le_indexedReconstructionProgram_of_randomTest_internal
    houtputLength hdensity hcode hlow hrandom hdense hbudget

/-- With probability at least one half, canonical checked sampling yields a
complete indexed encoding that round-trips and decodes exactly to the source
message, with every program-specific bit explicitly charged. -/
theorem half_le_fullyEncodedIndexedReconstructionProgram_of_randomTest
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
        ∃ indexed : IndexedReconstructionProgram design listSize,
          indexed.reconstruction =
              certificate.toProgram design (code.encode message) ∧
            indexed.decodedMessage code test = message ∧
              indexed.encode.length ≤
                1 + Fin.bitWidth outputLength +
                  (budget + (seedLength - inputLength) + 1) +
                    BooleanListCode.decoderIndexBitWidth listSize :=
  half_le_fullyEncodedIndexedReconstructionProgram_of_randomTest_internal
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

/-- The exact indexed-program reconstruction theorem with generator
complexity discharged by direct short-seed descriptions. -/
theorem half_le_indexedReconstructionProgram_of_seedDescriptions
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
        ∃ indexed : IndexedReconstructionProgram design listSize,
          indexed.reconstruction =
              certificate.toProgram design (code.encode message) ∧
            indexed.decodedMessage code test = message ∧
              indexed.encodeBooleanPayload.length ≤
                budget + (seedLength - inputLength) + 1 +
                  BooleanListCode.decoderIndexBitWidth listSize :=
  half_le_indexedReconstructionProgram_of_seedDescriptions_internal
    houtputLength hdensity hcode hseedLength hproduces hrandom hdense hbudget

/-- The fully encoded indexed reconstruction theorem with generator
complexity discharged by direct short-seed descriptions. -/
theorem half_le_fullyEncodedIndexedReconstructionProgram_of_seedDescriptions
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
        ∃ indexed : IndexedReconstructionProgram design listSize,
          indexed.reconstruction =
              certificate.toProgram design (code.encode message) ∧
            indexed.decodedMessage code test = message ∧
              indexed.encode.length ≤
                1 + Fin.bitWidth outputLength +
                  (budget + (seedLength - inputLength) + 1) +
                    BooleanListCode.decoderIndexBitWidth listSize :=
  half_le_fullyEncodedIndexedReconstructionProgram_of_seedDescriptions_internal
    houtputLength hdensity hcode hseedLength hproduces hrandom hdense hbudget

end NWDesign

end Complexity
