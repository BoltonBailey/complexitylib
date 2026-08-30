/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public
import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.ListDecoding.Family.Defs
import Complexitylib.Metacomplexity.ListDecoding.Family.Internal
public
import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.ListDecoding.Internal

/-!
# Uniform list-code families in NW reconstruction -- proof internals
-/


public section

namespace Complexity

namespace NWDesign

theorem two_le_reconstructionInverseAccuracy_internal
    {outputLength inverseDensity : ℕ}
    (houtputLength : 0 < outputLength)
    (hinverseDensity : 0 < inverseDensity) :
    2 ≤ reconstructionInverseAccuracy outputLength inverseDensity := by
  rw [reconstructionInverseAccuracy]
  exact le_trans (Nat.le_mul_of_pos_right 2 houtputLength)
    (Nat.le_mul_of_pos_right (2 * outputLength) hinverseDensity)

theorem reconstructionInverseAccuracy_margin_eq_internal
    {outputLength inverseDensity : ℕ}
    (houtputLength : 0 < outputLength)
    (hinverseDensity : 0 < inverseDensity) :
    1 / (reconstructionInverseAccuracy outputLength inverseDensity : ℚ) =
      ((1 / (inverseDensity : ℚ)) / (outputLength : ℚ)) / 2 := by
  simp only [reconstructionInverseAccuracy, Nat.cast_mul, Nat.cast_ofNat]
  norm_num [div_eq_mul_inv]
  field_simp

theorem half_le_fullyEncodedIndexedReconstructionProgram_of_codeFamily_internal
    {messageLength inverseAccuracy outputLength seedLength tapes time
      threshold budget : ℕ}
    (family : BooleanListCodeFamily)
    (hfamily : family.IsListDecodableAtInverseAccuracy)
    (haccuracy : 2 ≤ inverseAccuracy)
    {design : NWDesign outputLength
      (family.coordinateLength messageLength inverseAccuracy) seedLength}
    {message : Fin messageLength → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ}
    (hmargin : 1 / (inverseAccuracy : ℚ) =
      (density / (outputLength : ℚ)) / 2)
    (houtputLength : 0 < outputLength)
    (hdensity : 0 < density)
    (hlow : BitGenerator.HasLowTimeBoundedComplexity
      (design.generator
        ((family.code messageLength inverseAccuracy).encode message))
      machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability
          ((family.code messageLength inverseAccuracy).encode message) test
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength density) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate?
            ((family.code messageLength inverseAccuracy).encode message) test
            (1 / 2 + (density / (outputLength : ℚ)) / 2) batch =
          some certificate →
        ∃ indexed : IndexedReconstructionProgram design
            (family.listSize messageLength inverseAccuracy),
          indexed.reconstruction = certificate.toProgram design
              ((family.code messageLength inverseAccuracy).encode message) ∧
            indexed.decodedMessage
                (family.code messageLength inverseAccuracy) test = message ∧
              indexed.encode.length ≤
                1 + Fin.bitWidth outputLength +
                  (budget + (seedLength -
                    family.coordinateLength messageLength inverseAccuracy) + 1) +
                    BooleanListCode.decoderIndexBitWidth
                      (family.listSize messageLength inverseAccuracy) := by
  have hcode := hfamily messageLength inverseAccuracy haccuracy
  rw [hmargin] at hcode
  exact
    half_le_fullyEncodedIndexedReconstructionProgram_of_randomTest_internal
      houtputLength hdensity hcode hlow hrandom hdense hbudget

theorem
    half_le_fullyEncodedIndexedReconstructionProgram_of_polynomialCodeFamily_internal
    {messageLength inverseAccuracy outputLength seedLength tapes time
      threshold budget : ℕ}
    (family : BooleanListCodeFamily)
    (hfamily : family.IsListDecodableAtInverseAccuracy)
    (bounds : family.PolynomialParameterBounds)
    (haccuracy : 2 ≤ inverseAccuracy)
    {design : NWDesign outputLength
      (family.coordinateLength messageLength inverseAccuracy) seedLength}
    {message : Fin messageLength → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ}
    (hmargin : 1 / (inverseAccuracy : ℚ) =
      (density / (outputLength : ℚ)) / 2)
    (houtputLength : 0 < outputLength)
    (hdensity : 0 < density)
    (hlow : BitGenerator.HasLowTimeBoundedComplexity
      (design.generator
        ((family.code messageLength inverseAccuracy).encode message))
      machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability
          ((family.code messageLength inverseAccuracy).encode message) test
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength density) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate?
            ((family.code messageLength inverseAccuracy).encode message) test
            (1 / 2 + (density / (outputLength : ℚ)) / 2) batch =
          some certificate →
        ∃ indexed : IndexedReconstructionProgram design
            (family.listSize messageLength inverseAccuracy),
          indexed.reconstruction = certificate.toProgram design
              ((family.code messageLength inverseAccuracy).encode message) ∧
            indexed.decodedMessage
                (family.code messageLength inverseAccuracy) test = message ∧
              indexed.encode.length ≤
                1 + Fin.bitWidth outputLength +
                  (budget + (seedLength -
                    family.coordinateLength messageLength inverseAccuracy) + 1) +
                    Nat.clog 2
                      (bounds.listConstant *
                        (inverseAccuracy + 1) ^ bounds.listDegree) := by
  obtain ⟨hhalf, hselected⟩ :=
    half_le_fullyEncodedIndexedReconstructionProgram_of_codeFamily_internal
      family hfamily haccuracy hmargin houtputLength hdensity hlow hrandom
        hdense hbudget
  refine ⟨hhalf, ?_⟩
  intro batch certificate hfind
  obtain ⟨indexed, hreconstruction, hdecode, hlength⟩ :=
    hselected batch certificate hfind
  refine ⟨indexed, hreconstruction, hdecode, hlength.trans ?_⟩
  exact Nat.add_le_add_left
    (BooleanListCodeFamily.decoderIndexBitWidth_le_polynomialBound_internal
      bounds messageLength inverseAccuracy) _

theorem
    half_le_fullyEncodedIndexedReconstructionProgram_of_inverseDensity_internal
    {messageLength outputLength inverseDensity seedLength tapes time
      threshold budget : ℕ}
    (family : BooleanListCodeFamily)
    (hfamily : family.IsListDecodableAtInverseAccuracy)
    (bounds : family.PolynomialParameterBounds)
    (houtputLength : 0 < outputLength)
    (hinverseDensity : 0 < inverseDensity)
    {design : NWDesign outputLength
      (family.coordinateLength messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)) seedLength}
    {message : Fin messageLength → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    (hlow : BitGenerator.HasLowTimeBoundedComplexity
      (design.generator ((family.code messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)).encode
          message)) machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test
      (1 / (inverseDensity : ℚ)))
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability
          ((family.code messageLength
            (reconstructionInverseAccuracy outputLength inverseDensity)).encode
              message) test
          (1 / 2 +
            ((1 / (inverseDensity : ℚ)) / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength
            (1 / (inverseDensity : ℚ))) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength
          (1 / (inverseDensity : ℚ))) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate?
            ((family.code messageLength
              (reconstructionInverseAccuracy outputLength inverseDensity)).encode
                message) test
            (1 / 2 +
              ((1 / (inverseDensity : ℚ)) / (outputLength : ℚ)) / 2) batch =
          some certificate →
        ∃ indexed : IndexedReconstructionProgram design
            (family.listSize messageLength
              (reconstructionInverseAccuracy outputLength inverseDensity)),
          indexed.reconstruction = certificate.toProgram design
              ((family.code messageLength
                (reconstructionInverseAccuracy outputLength inverseDensity)).encode
                  message) ∧
            indexed.decodedMessage
                (family.code messageLength
                  (reconstructionInverseAccuracy outputLength inverseDensity))
                test = message ∧
              indexed.encode.length ≤
                1 + Fin.bitWidth outputLength +
                  (budget + (seedLength - family.coordinateLength messageLength
                    (reconstructionInverseAccuracy outputLength inverseDensity)) +
                      1) +
                    Nat.clog 2
                      (bounds.listConstant *
                        (reconstructionInverseAccuracy outputLength
                          inverseDensity + 1) ^ bounds.listDegree) := by
  exact
    half_le_fullyEncodedIndexedReconstructionProgram_of_polynomialCodeFamily_internal
      family hfamily bounds
        (two_le_reconstructionInverseAccuracy_internal
          houtputLength hinverseDensity)
        (density := 1 / (inverseDensity : ℚ))
        (reconstructionInverseAccuracy_margin_eq_internal
          houtputLength hinverseDensity)
        houtputLength (by positivity) hlow hrandom hdense hbudget

end NWDesign

end Complexity
