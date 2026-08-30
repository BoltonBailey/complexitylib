/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.ListDecoding.Family
public
import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.ListDecoding.Family.Defs
public
import
Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.ListDecoding.Family.Internal

/-!
# Uniform list-code families in NW reconstruction

This layer specializes checked NW reconstruction to a code family at inverse
accuracy `q`, under the exact relation `1/q = density/(2*outputLength)` used in
Hirahara's argument. Polynomial list size then gives a concrete logarithmic
bound on the encoded decoder choice. For density `1/inverseDensity`, the final
theorem chooses `q = 2*outputLength*inverseDensity` and discharges that relation.
The final endpoints compose this exact specialization with any efficiently
universal machine while retaining the compiler constant and polynomial clock.
A family-uniform realization chooses those constants before all ambient
instances and charges the explicit design/test encoding in the description.
An oracle-relative endpoint instead supplies the finite test through canonical
membership queries and retains the original reconstruction-description bound.
Its efficiently universal specialization exposes one transfer law valid for
all finite test oracles before applying the half-success reconstruction result.
A fully uniform oracle specialization chooses the compiler constants before
all numeric parameters and designs, charging the exact canonical fixed-width
design encoding.
-/


public section

namespace Complexity

namespace NWDesign

namespace HasEncodedMessageCertificateWithin

/-- A bounded indexed reconstruction description remains a bounded program for
one decoder machine shared by every instance of a list-code family. The exact
self-delimiting cost of the ambient design/test encoding is included in the
description bound. -/
theorem uniformTimeBoundedKolmogorovComplexity_le
    {family : BooleanListCodeFamily}
    {messageLength inverseAccuracy outputLength seedLength : ℕ}
    {design : NWDesign outputLength
      (family.coordinateLength messageLength inverseAccuracy) seedLength}
    {test : Finset (Fin outputLength → Bool)}
    {message : Fin messageLength → Bool} {bound : ℕ}
    (realization : UniformEncodedMessageDecoderRealization family)
    (hcertificate : HasEncodedMessageCertificateWithin design
      (family.code messageLength inverseAccuracy) test message bound) :
    realization.machine.timeBoundedKolmogorovComplexity
        (List.ofFn message)
        (realization.time
          (realization.framedDescriptionBound design test bound)) ≤
      (realization.framedDescriptionBound design test bound : WithTop ℕ) :=
  hcertificate.uniformTimeBoundedKolmogorovComplexity_le_internal realization

/-- A bounded indexed reconstruction certificate remains a bounded
oracle-relative program for one decoder machine shared across the whole code
family. The design encoding is charged explicitly; the finite test remains
oracle access. -/
theorem uniformOracleTimeBoundedKolmogorovComplexity_le
    {family : BooleanListCodeFamily}
    {messageLength inverseAccuracy outputLength seedLength : ℕ}
    {design : NWDesign outputLength
      (family.coordinateLength messageLength inverseAccuracy) seedLength}
    {test : Finset (Fin outputLength → Bool)}
    {message : Fin messageLength → Bool} {bound : ℕ}
    (realization : UniformOracleEncodedMessageDecoderRealization family)
    (hcertificate : HasEncodedMessageCertificateWithin design
      (family.code messageLength inverseAccuracy) test message bound) :
    realization.machine.timeBoundedKolmogorovComplexity
        (finiteTestOracle test) (List.ofFn message)
        (realization.time
          (UniformOracleEncodedMessageDecoderRealization.framedDescriptionBound
            design bound)) ≤
      (UniformOracleEncodedMessageDecoderRealization.framedDescriptionBound
        design bound : WithTop ℕ) :=
  hcertificate.uniformOracleTimeBoundedKolmogorovComplexity_le_internal
    realization

end HasEncodedMessageCertificateWithin

namespace UniformEncodedMessageDecoderRealization

/-- A single uniform family decoder gives one set of universal compiler
constants valid simultaneously for all lengths, accuracies, designs, tests,
messages, and certificate bounds. Ambient information is explicit in the
framed description length and therefore cannot leak into those constants. -/
theorem efficientlyUniversal_transfer
    {family : BooleanListCodeFamily} {universalTapes : ℕ}
    (realization : UniformEncodedMessageDecoderRealization family)
    (universal : TM universalTapes)
    (huniversal : universal.IsEfficientlyUniversal) :
    ∃ constant coefficient exponent,
      ∀ {messageLength inverseAccuracy outputLength seedLength : ℕ}
        (design : NWDesign outputLength
          (family.coordinateLength messageLength inverseAccuracy) seedLength)
        (test : Finset (Fin outputLength → Bool))
        (message : Fin messageLength → Bool) (bound : ℕ),
        HasEncodedMessageCertificateWithin design
            (family.code messageLength inverseAccuracy) test message bound →
          universal.timeBoundedKolmogorovComplexity (List.ofFn message)
              (coefficient *
                (realization.framedDescriptionBound design test bound +
                  realization.time
                    (realization.framedDescriptionBound design test bound) + 1) ^
                    exponent) ≤
            (realization.framedDescriptionBound design test bound +
              constant : ℕ) :=
  realization.efficientlyUniversal_transfer_internal universal huniversal

end UniformEncodedMessageDecoderRealization

namespace UniformOracleEncodedMessageDecoderRealization

/-- Canonical design framing has an exact parameter-only bit cost. -/
@[simp] theorem framedDescriptionBound_eq
    {family : BooleanListCodeFamily}
    {messageLength inverseAccuracy outputLength seedLength : ℕ}
    (design : NWDesign outputLength
      (family.coordinateLength messageLength inverseAccuracy) seedLength)
    (descriptionBound : ℕ) :
    framedDescriptionBound design descriptionBound =
      4 * (messageLength.size + inverseAccuracy.size + outputLength.size +
          (family.coordinateLength messageLength inverseAccuracy).size +
          seedLength.size) + 22 +
        2 * (outputLength *
          family.coordinateLength messageLength inverseAccuracy *
          Fin.bitWidth seedLength) + descriptionBound :=
  framedDescriptionBound_eq_internal design descriptionBound

/-- At inverse-density parameters, canonical design framing makes the complete
description bound an explicit arithmetic expression. -/
@[simp] theorem inverseDensityFramedDescriptionBound_eq
    {family : BooleanListCodeFamily}
    (bounds : family.PolynomialParameterBounds)
    {messageLength outputLength inverseDensity seedLength : ℕ}
    (design : NWDesign outputLength
      (family.coordinateLength messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)) seedLength)
    (budget : ℕ) :
    inverseDensityFramedDescriptionBound bounds design budget =
      4 * (messageLength.size +
          (reconstructionInverseAccuracy outputLength inverseDensity).size +
          outputLength.size +
          (family.coordinateLength messageLength
            (reconstructionInverseAccuracy outputLength inverseDensity)).size +
          seedLength.size) + 22 +
        2 * (outputLength *
          family.coordinateLength messageLength
            (reconstructionInverseAccuracy outputLength inverseDensity) *
          Fin.bitWidth seedLength) +
        inverseDensityDescriptionBound family bounds messageLength outputLength
          inverseDensity seedLength budget :=
  inverseDensityFramedDescriptionBound_eq_internal bounds design budget

/-- One oracle-universal compiler constant and polynomial clock transfer every
certificate across all lengths, accuracies, designs, tests, and messages for a
uniform family decoder. Design framing is explicit and the test remains an
oracle. -/
theorem efficientlyUniversal_transfer
    {family : BooleanListCodeFamily} {universalTapes : ℕ}
    (realization : UniformOracleEncodedMessageDecoderRealization family)
    (universal : OracleTM universalTapes)
    (huniversal : OracleTM.IsEfficientlyUniversal universal) :
    ∃ constant coefficient exponent,
      ∀ {messageLength inverseAccuracy outputLength seedLength : ℕ}
        (design : NWDesign outputLength
          (family.coordinateLength messageLength inverseAccuracy) seedLength)
        (test : Finset (Fin outputLength → Bool))
        (message : Fin messageLength → Bool) (bound : ℕ),
        HasEncodedMessageCertificateWithin design
            (family.code messageLength inverseAccuracy) test message bound →
          universal.timeBoundedKolmogorovComplexity
              (finiteTestOracle test) (List.ofFn message)
              (coefficient *
                (framedDescriptionBound design bound +
                  realization.time
                    (framedDescriptionBound design bound) + 1) ^
                    exponent) ≤
            (framedDescriptionBound design bound + constant : ℕ) :=
  realization.efficientlyUniversal_transfer_internal universal huniversal

end UniformOracleEncodedMessageDecoderRealization

/-- Positive output length and inverse density make the canonical inverse
accuracy at least two. -/
theorem two_le_reconstructionInverseAccuracy
    {outputLength inverseDensity : ℕ}
    (houtputLength : 0 < outputLength)
    (hinverseDensity : 0 < inverseDensity) :
    2 ≤ reconstructionInverseAccuracy outputLength inverseDensity :=
  two_le_reconstructionInverseAccuracy_internal
    houtputLength hinverseDensity

/-- The canonical inverse accuracy has exactly the NW reconstruction margin
for a test of density `1 / inverseDensity`. -/
theorem reconstructionInverseAccuracy_margin_eq
    {outputLength inverseDensity : ℕ}
    (houtputLength : 0 < outputLength)
    (hinverseDensity : 0 < inverseDensity) :
    1 / (reconstructionInverseAccuracy outputLength inverseDensity : ℚ) =
      ((1 / (inverseDensity : ℚ)) / (outputLength : ℚ)) / 2 :=
  reconstructionInverseAccuracy_margin_eq_internal
    houtputLength hinverseDensity

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

/-- Paper-shaped family reconstruction at density `1 / inverseDensity`. The
inverse accuracy is fixed canonically to
`2 * outputLength * inverseDensity`, so no arithmetic compatibility premise
remains. -/
theorem half_le_fullyEncodedIndexedReconstructionProgram_of_inverseDensity
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
                          inverseDensity + 1) ^ bounds.listDegree) :=
  half_le_fullyEncodedIndexedReconstructionProgram_of_inverseDensity_internal
    family hfamily bounds houtputLength hinverseDensity hlow hrandom hdense
      hbudget

/-- Bitstring-certificate form of the inverse-density reconstruction theorem:
with probability at least one half, every returned checked certificate yields
an actual short string decoded to the original source message. -/
theorem half_le_encodedMessageCertificate_of_inverseDensity
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
        HasEncodedMessageCertificateWithin design
          (family.code messageLength
            (reconstructionInverseAccuracy outputLength inverseDensity))
          test message
          (inverseDensityDescriptionBound family bounds messageLength
            outputLength inverseDensity seedLength budget) :=
  half_le_encodedMessageCertificate_of_inverseDensity_internal
    family hfamily bounds houtputLength hinverseDensity hlow hrandom hdense
      hbudget

/-- Time-bounded Kolmogorov form of inverse-density reconstruction. For any
machine realization of the fixed indexed-message decoder, canonical sampling
succeeds with probability at least one half and every returned certificate
proves the advertised machine-relative `Kt` upper bound. -/
theorem half_le_timeBoundedKolmogorovComplexity_of_inverseDensity
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
    (realization : EncodedMessageDecoderRealization design
      (family.code messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)) test)
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
        realization.machine.timeBoundedKolmogorovComplexity
            (List.ofFn message)
            (realization.time (inverseDensityDescriptionBound family bounds
              messageLength outputLength inverseDensity seedLength budget)) ≤
          (inverseDensityDescriptionBound family bounds messageLength
            outputLength inverseDensity seedLength budget : WithTop ℕ) :=
  half_le_timeBoundedKolmogorovComplexity_of_inverseDensity_internal
    family hfamily bounds houtputLength hinverseDensity realization hlow hrandom
      hdense hbudget

/-- Oracle-relative form of inverse-density reconstruction. One decoder machine
handles every finite statistical test through its canonical membership oracle.
Canonical certificate search succeeds with probability at least one half, and
each returned certificate gives the source message the exact existing
description bound with no test-truth-table bits added to the program. -/
theorem half_le_oracleTimeBoundedKolmogorovComplexity_of_inverseDensity
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
    (realization : OracleEncodedMessageDecoderRealization design
      (family.code messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)))
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
        realization.machine.timeBoundedKolmogorovComplexity
            (finiteTestOracle test) (List.ofFn message)
            (realization.time (inverseDensityDescriptionBound family bounds
              messageLength outputLength inverseDensity seedLength budget)) ≤
          (inverseDensityDescriptionBound family bounds messageLength
            outputLength inverseDensity seedLength budget : WithTop ℕ) :=
  half_le_oracleTimeBoundedKolmogorovComplexity_of_inverseDensity_internal
    family hfamily bounds houtputLength hinverseDensity realization hlow hrandom
      hdense hbudget

/-- End-to-end inverse-density reconstruction for an arbitrary efficiently
universal oracle machine. The returned compiler constant and polynomial clock
first satisfy a transfer law for every finite test oracle. Checked certificate
search for the current test then succeeds with probability at least one half,
and every returned certificate gives the source message the explicit
reconstruction-description bound plus that constant. -/
theorem half_le_efficientlyUniversalOracleKolmogorovComplexity_of_inverseDensity
    {messageLength outputLength inverseDensity seedLength tapes time
      threshold budget universalTapes : ℕ}
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
    (realization : OracleEncodedMessageDecoderRealization design
      (family.code messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)))
    (universal : OracleTM universalTapes)
    (huniversal : OracleTM.IsEfficientlyUniversal universal)
    (hlow : BitGenerator.HasLowTimeBoundedComplexity
      (design.generator ((family.code messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)).encode
          message)) machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test
      (1 / (inverseDensity : ℚ)))
    (hbudget : design.HasOverlapBudget budget) :
    ∃ constant coefficient exponent,
      (∀ (otherTest : Finset (Fin outputLength → Bool))
        (otherMessage : Fin messageLength → Bool) (bound : ℕ),
        HasEncodedMessageCertificateWithin design
            (family.code messageLength
              (reconstructionInverseAccuracy outputLength inverseDensity))
            otherTest otherMessage bound →
          universal.timeBoundedKolmogorovComplexity
              (finiteTestOracle otherTest) (List.ofFn otherMessage)
              (coefficient *
                (bound + realization.time bound + 1) ^ exponent) ≤
            (bound + constant : ℕ)) ∧
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
          universal.timeBoundedKolmogorovComplexity
              (finiteTestOracle test) (List.ofFn message)
              (coefficient *
                (inverseDensityDescriptionBound family bounds messageLength
                    outputLength inverseDensity seedLength budget +
                  realization.time
                    (inverseDensityDescriptionBound family bounds messageLength
                      outputLength inverseDensity seedLength budget) + 1) ^
                    exponent) ≤
            (inverseDensityDescriptionBound family bounds messageLength
              outputLength inverseDensity seedLength budget + constant : ℕ) :=
  half_le_efficientlyUniversalOracleKolmogorovComplexity_of_inverseDensity_internal
    family hfamily bounds houtputLength hinverseDensity realization universal
      huniversal hlow hrandom hdense hbudget

/-- End-to-end inverse-density reconstruction for an arbitrary efficiently
universal machine. Canonical sampling succeeds with probability at least one
half; every returned certificate gives the source message a description of the
explicit reconstruction length plus the universal compiler constant, under the
compiler's polynomial clock. The decoder realization remains fixed in the
ambient design/code/test parameters. -/
theorem half_le_efficientlyUniversalKolmogorovComplexity_of_inverseDensity
    {messageLength outputLength inverseDensity seedLength tapes time
      threshold budget universalTapes : ℕ}
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
    (realization : EncodedMessageDecoderRealization design
      (family.code messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)) test)
    (universal : TM universalTapes)
    (huniversal : universal.IsEfficientlyUniversal)
    (hlow : BitGenerator.HasLowTimeBoundedComplexity
      (design.generator ((family.code messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)).encode
          message)) machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test
      (1 / (inverseDensity : ℚ)))
    (hbudget : design.HasOverlapBudget budget) :
    ∃ constant coefficient exponent,
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
          universal.timeBoundedKolmogorovComplexity (List.ofFn message)
              (coefficient *
                (inverseDensityDescriptionBound family bounds messageLength
                    outputLength inverseDensity seedLength budget +
                  realization.time
                    (inverseDensityDescriptionBound family bounds messageLength
                      outputLength inverseDensity seedLength budget) + 1) ^
                    exponent) ≤
            (inverseDensityDescriptionBound family bounds messageLength
              outputLength inverseDensity seedLength budget + constant : ℕ) :=
  half_le_efficientlyUniversalKolmogorovComplexity_of_inverseDensity_internal
    family hfamily bounds houtputLength hinverseDensity realization universal
      huniversal hlow hrandom hdense hbudget

namespace UniformEncodedMessageDecoderRealization

/-- Uniform inverse-density NW reconstruction on an arbitrary efficiently
universal machine. One compiler constant and one polynomial clock work
simultaneously for every numeric parameter, NW design, statistical test, and
source message. The ambient design/test representation is not hidden: its
self-delimiting framing is charged by
`inverseDensityFramedDescriptionBound`.

This is a fully uniform oracle-free transfer theorem. Replacing the explicit
ambient string by random-access oracle access requires a separate oracle
machine model and is not asserted here. -/
theorem half_le_efficientlyUniversalKolmogorovComplexity_of_inverseDensity
    {family : BooleanListCodeFamily} {universalTapes : ℕ}
    (realization : UniformEncodedMessageDecoderRealization family)
    (universal : TM universalTapes)
    (huniversal : universal.IsEfficientlyUniversal) :
    ∃ constant coefficient exponent,
      ∀ (bounds : family.PolynomialParameterBounds)
        {messageLength outputLength inverseDensity seedLength tapes time
          threshold budget : ℕ}
        {design : NWDesign outputLength
          (family.coordinateLength messageLength
            (reconstructionInverseAccuracy outputLength inverseDensity)) seedLength}
        {message : Fin messageLength → Bool}
        {machine : TM tapes} {test : Finset (Fin outputLength → Bool)},
        family.IsListDecodableAtInverseAccuracy →
        0 < outputLength →
        0 < inverseDensity →
        BitGenerator.HasLowTimeBoundedComplexity
          (design.generator ((family.code messageLength
            (reconstructionInverseAccuracy outputLength inverseDensity)).encode
              message)) machine time threshold →
        BitGenerator.IsTimeBoundedRandomTest test machine time threshold →
        BitGenerator.IsDenseTest test (1 / (inverseDensity : ℚ)) →
        design.HasOverlapBudget budget →
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
            universal.timeBoundedKolmogorovComplexity (List.ofFn message)
                (coefficient *
                  (realization.inverseDensityFramedDescriptionBound bounds
                      design test budget +
                    realization.time
                      (realization.inverseDensityFramedDescriptionBound bounds
                        design test budget) + 1) ^ exponent) ≤
              (realization.inverseDensityFramedDescriptionBound bounds
                design test budget + constant : ℕ) :=
  half_le_efficientlyUniversalKolmogorovComplexity_of_inverseDensity_internal
    realization universal huniversal

end UniformEncodedMessageDecoderRealization

namespace UniformOracleEncodedMessageDecoderRealization

/-- Fully family-uniform oracle-relative inverse-density reconstruction. One
decoder machine and one oracle-universal compiler serve every length, accuracy,
design encoding, finite test oracle, and source message. The test costs no
program bits; the explicitly framed design encoding is charged exactly. -/
theorem half_le_efficientlyUniversalKolmogorovComplexity_of_inverseDensity
    {family : BooleanListCodeFamily} {universalTapes : ℕ}
    (realization : UniformOracleEncodedMessageDecoderRealization family)
    (universal : OracleTM universalTapes)
    (huniversal : OracleTM.IsEfficientlyUniversal universal) :
    ∃ constant coefficient exponent,
      ∀ (bounds : family.PolynomialParameterBounds)
        {messageLength outputLength inverseDensity seedLength tapes time
          threshold budget : ℕ}
        {design : NWDesign outputLength
          (family.coordinateLength messageLength
            (reconstructionInverseAccuracy outputLength inverseDensity)) seedLength}
        {message : Fin messageLength → Bool}
        {machine : TM tapes} {test : Finset (Fin outputLength → Bool)},
        family.IsListDecodableAtInverseAccuracy →
        0 < outputLength →
        0 < inverseDensity →
        BitGenerator.HasLowTimeBoundedComplexity
          (design.generator ((family.code messageLength
            (reconstructionInverseAccuracy outputLength inverseDensity)).encode
              message)) machine time threshold →
        BitGenerator.IsTimeBoundedRandomTest test machine time threshold →
        BitGenerator.IsDenseTest test (1 / (inverseDensity : ℚ)) →
        design.HasOverlapBudget budget →
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
            universal.timeBoundedKolmogorovComplexity
                (finiteTestOracle test) (List.ofFn message)
                (coefficient *
                  (inverseDensityFramedDescriptionBound bounds design budget +
                    realization.time
                      (inverseDensityFramedDescriptionBound bounds design
                        budget) + 1) ^ exponent) ≤
              (inverseDensityFramedDescriptionBound bounds design budget +
                constant : ℕ) :=
  half_le_efficientlyUniversalKolmogorovComplexity_of_inverseDensity_internal
    realization universal huniversal

end UniformOracleEncodedMessageDecoderRealization

end NWDesign

end Complexity
