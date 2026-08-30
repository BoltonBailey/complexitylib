/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.ListDecoding.Family
public
import
Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.ListDecoding.Family.Internal

/-!
# Uniform list-code families in NW reconstruction

This layer specializes checked NW reconstruction to a code family at inverse
accuracy `q`, under the exact relation `1/q = density/(2*outputLength)` used in
Hirahara's argument. Polynomial list size then gives a concrete logarithmic
bound on the encoded decoder choice.
-/


public section

namespace Complexity

namespace NWDesign

/-- Fully encoded NW reconstruction instantiated by a semantic inverse-accuracy
list-code family. -/
theorem half_le_fullyEncodedIndexedReconstructionProgram_of_codeFamily
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
                      (family.listSize messageLength inverseAccuracy) :=
  half_le_fullyEncodedIndexedReconstructionProgram_of_codeFamily_internal
    family hfamily haccuracy hmargin houtputLength hdensity hlow hrandom
      hdense hbudget

/-- Hirahara-style specialization with the list-index cost bounded by the
family's polynomial list-size guarantee. -/
theorem half_le_fullyEncodedIndexedReconstructionProgram_of_polynomialCodeFamily
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
                        (inverseAccuracy + 1) ^ bounds.listDegree) :=
  half_le_fullyEncodedIndexedReconstructionProgram_of_polynomialCodeFamily_internal
    family hfamily bounds haccuracy hmargin houtputLength hdensity hlow hrandom
      hdense hbudget

end NWDesign

end Complexity
