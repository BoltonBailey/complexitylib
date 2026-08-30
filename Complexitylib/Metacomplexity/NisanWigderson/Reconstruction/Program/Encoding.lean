/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.Encoding.Defs
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.Encoding.Internal

/-!
# Bit encoding of explicit NW reconstruction programs

The stored predecessor tables, outside seed, later tail, and candidate are
serialized as one canonical flat bit string. The codec is parameterized by the
polarity and hybrid coordinate, which belong to the later metadata layer.
-/


public section

namespace Complexity

namespace NWDesign

/-- The total payload-index type has exactly the previously derived number of
Boolean reconstruction entries. -/
theorem card_reconstructionPayloadIndex
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    Fintype.card (ReconstructionPayloadIndex design current) =
      design.reconstructionDataBitsAt current :=
  card_reconstructionPayloadIndex_internal design current

/-- The canonical flat payload has exactly the reconstruction entry count. -/
@[simp] theorem length_encodeBooleanPayload
    {outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram) :
    program.encodeBooleanPayload.length =
      design.reconstructionDataBitsAt program.current :=
  length_encodeBooleanPayload_internal program

/-- Flat payload length agrees exactly with the explicit program's semantic
Boolean payload size. -/
theorem length_encodeBooleanPayload_eq_booleanPayloadSize
    {outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram) :
    program.encodeBooleanPayload.length = program.booleanPayloadSize :=
  length_encodeBooleanPayload_eq_booleanPayloadSize_internal program

/-- Exact round trip for the reconstruction Boolean payload when its polarity
and coordinate metadata are supplied. -/
@[simp] theorem decodeReconstructionBooleanPayload?_encode
    {outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram) :
    decodeReconstructionBooleanPayload? design program.complement
      program.current program.encodeBooleanPayload = some program :=
  decodeReconstructionBooleanPayload?_encode_internal program

/-- Payload decoding fails exactly on strings whose length differs from the
exact reconstruction entry count. -/
@[simp] theorem decodeReconstructionBooleanPayload?_eq_none_iff
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (complement : Bool) (current : Fin outputLength) (bits : List Bool) :
    decodeReconstructionBooleanPayload? design complement current bits = none ↔
      bits.length ≠ design.reconstructionDataBitsAt current :=
  decodeReconstructionBooleanPayload?_eq_none_iff_internal
    design complement current bits

/-- A selected certificate materializes to a predictor meeting the agreement
threshold whose actual flat payload obeys the weak-design length bound. -/
theorem findGoodReconstructionCertificate_encodedProgram_sound
    {outputLength inputLength seedLength trials budget : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (agreementThreshold : ℚ)
    (hbudget : design.HasOverlapBudget budget)
    (batch : Fin trials → ReconstructionTrial outputLength seedLength)
    (certificate : ReconstructionCertificate outputLength seedLength)
    (hfind : design.findGoodReconstructionCertificate? hardFunction test
      agreementThreshold batch = some certificate) :
    agreementThreshold ≤
        (certificate.toProgram design hardFunction).agreementProbability
          hardFunction test ∧
      (certificate.toProgram design hardFunction).encodeBooleanPayload.length ≤
        budget + (seedLength - inputLength) + 1 :=
  findGoodReconstructionCertificate_encodedProgram_sound_internal design
    hardFunction test agreementThreshold hbudget batch certificate hfind

/-- End-to-end encoded reconstruction: canonical checked sampling succeeds
with probability at least one half and every selected stored predictor has
agreement `1/2 + δ/(2m)` and the claimed actual payload length. -/
theorem half_le_encodedReconstructionProgram_of_randomTest
    {outputLength inputLength seedLength tapes time threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {hardFunction : (Fin inputLength → Bool) → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 < density)
    (hlow : (design.generator hardFunction).HasLowTimeBoundedComplexity
      machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability hardFunction test
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength density) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate? hardFunction test
            (1 / 2 + (density / (outputLength : ℚ)) / 2) batch =
          some certificate →
        1 / 2 + (density / (outputLength : ℚ)) / 2 ≤
            (certificate.toProgram design hardFunction).agreementProbability
              hardFunction test ∧
          (certificate.toProgram design hardFunction).encodeBooleanPayload.length ≤
            budget + (seedLength - inputLength) + 1 :=
  half_le_encodedReconstructionProgram_of_randomTest_internal
    houtputLength hdensity hlow hrandom hdense hbudget

/-- The encoded reconstruction theorem with low generator complexity
discharged by direct short-seed descriptions. -/
theorem half_le_encodedReconstructionProgram_of_seedDescriptions
    {outputLength inputLength seedLength tapes time threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {hardFunction : (Fin inputLength → Bool) → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 < density) (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (design.generator hardFunction seed)) time)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability hardFunction test
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength density) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate? hardFunction test
            (1 / 2 + (density / (outputLength : ℚ)) / 2) batch =
          some certificate →
        1 / 2 + (density / (outputLength : ℚ)) / 2 ≤
            (certificate.toProgram design hardFunction).agreementProbability
              hardFunction test ∧
          (certificate.toProgram design hardFunction).encodeBooleanPayload.length ≤
            budget + (seedLength - inputLength) + 1 :=
  half_le_encodedReconstructionProgram_of_seedDescriptions_internal
    houtputLength hdensity hseedLength hproduces hrandom hdense hbudget

end NWDesign

end Complexity
