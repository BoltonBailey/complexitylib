/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.Defs
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.Internal
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.Encoding

/-!
# Explicit NW reconstruction programs

Checked finite certificates can be materialized into reconstruction programs
that store every predecessor table used by their predictor. Program evaluation
therefore has no hard-function oracle; the hard function is used only while
materializing and subsequently scoring the stored predictor. The encoding
submodule flattens every stored Boolean field into a canonical bit string with
an exact decoder and length theorem.
-/


public section

namespace Complexity

namespace NWDesign

/-- Materializing predecessor tables preserves the original reconstruction
query pointwise. -/
theorem materializeReconstructionProgram_query
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (complement : Bool) (current : Fin outputLength)
    (advice : design.ReconstructionAdvice current)
    (challenge : Fin inputLength → Bool) :
    (design.materializeReconstructionProgram hardFunction complement current
        advice).query challenge =
      design.reconstructionQuery hardFunction current advice.1 advice.2.1
        challenge advice.2.2 :=
  materializeReconstructionProgram_query_internal design hardFunction
    complement current advice challenge

/-- The explicit program's oracle-free evaluator computes exactly the
fixed-advice reconstruction predictor from which it was materialized. -/
theorem materializeReconstructionProgram_predictor
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (complement : Bool) (current : Fin outputLength)
    (advice : design.ReconstructionAdvice current) :
    (design.materializeReconstructionProgram hardFunction complement current
        advice).predictor test =
      design.reconstructionPredictor hardFunction
        (BitGenerator.orientTest test complement) current advice.1
        advice.2.1 advice.2.2 :=
  materializeReconstructionProgram_predictor_internal design hardFunction
    test complement current advice

/-- Materializing a reconstruction predictor preserves its exact agreement
probability with the hard function. -/
theorem materializeReconstructionProgram_agreementProbability
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (complement : Bool) (current : Fin outputLength)
    (advice : design.ReconstructionAdvice current) :
    (design.materializeReconstructionProgram hardFunction complement current
        advice).agreementProbability hardFunction test =
      design.reconstructionAgreementProbability hardFunction
        (BitGenerator.orientTest test complement) current advice :=
  materializeReconstructionProgram_agreementProbability_internal
    design hardFunction test complement current advice

/-- Materializing a checked certificate preserves its global-trial agreement
statistic exactly. -/
theorem reconstructionCertificate_toProgram_agreementProbability
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (certificate : ReconstructionCertificate outputLength seedLength) :
    (certificate.toProgram design hardFunction).agreementProbability
        hardFunction test =
      design.reconstructionTrialAgreementProbability hardFunction
        (BitGenerator.orientTest test certificate.complement)
        certificate.trial :=
  reconstructionCertificate_toProgram_agreementProbability_internal
    design hardFunction test certificate

/-- The Boolean fields in an explicit program have exactly the previously
derived non-codec reconstruction payload size. -/
theorem ReconstructionProgram.booleanPayloadSize_eq
    {outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram) :
    program.booleanPayloadSize =
      design.reconstructionDataBitsAt program.current :=
  ReconstructionProgram.booleanPayloadSize_eq_internal program

/-- A selected certificate materializes to an oracle-free predictor meeting
the checked agreement threshold and the weak-design Boolean payload bound. -/
theorem findGoodReconstructionCertificate_program_sound
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
      (certificate.toProgram design hardFunction).booleanPayloadSize ≤
        budget + (seedLength - inputLength) + 1 :=
  findGoodReconstructionCertificate_program_sound_internal design
    hardFunction test agreementThreshold hbudget batch certificate hfind

/-- End-to-end explicit reconstruction: with probability at least one half,
canonical checked sampling finds a stored, oracle-free predictor of agreement
`1/2 + δ/(2m)` and weak-design-bounded Boolean payload. -/
theorem half_le_materializedReconstructionProgram_of_randomTest
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
          (certificate.toProgram design hardFunction).booleanPayloadSize ≤
            budget + (seedLength - inputLength) + 1 :=
  half_le_materializedReconstructionProgram_of_randomTest_internal
    houtputLength hdensity hlow hrandom hdense hbudget

/-- The explicit reconstruction theorem with low generator complexity
discharged by direct short-seed descriptions. -/
theorem half_le_materializedReconstructionProgram_of_seedDescriptions
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
          (certificate.toProgram design hardFunction).booleanPayloadSize ≤
            budget + (seedLength - inputLength) + 1 :=
  half_le_materializedReconstructionProgram_of_seedDescriptions_internal
    houtputLength hdensity hseedLength hproduces hrandom hdense hbudget

end NWDesign

end Complexity
