/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.ListDecoding.Family.Defs
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.ListDecoding.Defs
public import Complexitylib.Metacomplexity.NisanWigderson.Encoding.Defs

/-!
# Uniform list-code families in NW reconstruction -- definitions
-/


@[expose] public section

namespace Complexity

namespace NWDesign

/-- Inverse list-decoding accuracy corresponding to NW output length `m` and
test density `1 / inverseDensity`: `q = 2 * m * inverseDensity`. -/
def reconstructionInverseAccuracy
    (outputLength inverseDensity : ℕ) : ℕ :=
  2 * outputLength * inverseDensity

/-- Complete bit-length bound delivered by inverse-density reconstruction with
a polynomially bounded list-code family. -/
def inverseDensityDescriptionBound
    (family : BooleanListCodeFamily)
    (bounds : family.PolynomialParameterBounds)
    (messageLength outputLength inverseDensity seedLength budget : ℕ) : ℕ :=
  1 + Fin.bitWidth outputLength +
    (budget + (seedLength - family.coordinateLength messageLength
      (reconstructionInverseAccuracy outputLength inverseDensity)) + 1) +
      Nat.clog 2
        (bounds.listConstant *
          (reconstructionInverseAccuracy outputLength inverseDensity + 1) ^
            bounds.listDegree)

/-- A single decoder machine for every instance of one Boolean list-code
family. The NW design and statistical test are supplied through an explicit
ambient encoding, while the indexed reconstruction program remains the
self-delimiting second component of the machine input.

This is an oracle-free uniformity interface. In particular, the length of the
ambient encoding is charged explicitly rather than hidden in the universal
compiler constant. -/
structure UniformEncodedMessageDecoderRealization
    (family : BooleanListCodeFamily) where
  /-- Explicit binary representation of the design and statistical test used
  by one decoder invocation. -/
  ambientEncoding :
    ∀ {messageLength inverseAccuracy outputLength seedLength : ℕ},
      NWDesign outputLength
          (family.coordinateLength messageLength inverseAccuracy) seedLength →
        Finset (Fin outputLength → Bool) → List Bool
  /-- Number of work tapes used by the one uniform decoder machine. -/
  tapes : ℕ
  /-- Machine interpreting every framed ambient/program pair. -/
  machine : TM tapes
  /-- Decoder clock as a function of total framed input length. -/
  time : ℕ → ℕ
  /-- Larger framed inputs receive no smaller clock. -/
  time_mono : Monotone time
  /-- Correctness simultaneously for every parameter choice and ambient
  instance. -/
  correct :
    ∀ {messageLength inverseAccuracy outputLength seedLength : ℕ}
      (design : NWDesign outputLength
        (family.coordinateLength messageLength inverseAccuracy) seedLength)
      (test : Finset (Fin outputLength → Bool)) (description : List Bool)
      (message : Fin messageLength → Bool),
      decodeIndexedMessage? design (family.code messageLength inverseAccuracy)
          test description = some message →
        machine.ProducesInTime
          (pair (ambientEncoding design test) description)
          (List.ofFn message)
          (time (pair (ambientEncoding design test) description).length)

namespace UniformEncodedMessageDecoderRealization

/-- Total description bound after self-delimiting framing of the ambient
encoding with an indexed reconstruction description of length at most
`descriptionBound`. -/
def framedDescriptionBound
    {family : BooleanListCodeFamily}
    (realization : UniformEncodedMessageDecoderRealization family)
    {messageLength inverseAccuracy outputLength seedLength : ℕ}
    (design : NWDesign outputLength
      (family.coordinateLength messageLength inverseAccuracy) seedLength)
    (test : Finset (Fin outputLength → Bool))
    (descriptionBound : ℕ) : ℕ :=
  2 * (realization.ambientEncoding design test).length + 2 +
    descriptionBound

/-- Total framed description bound for the canonical inverse-density NW
reconstruction parameters. -/
def inverseDensityFramedDescriptionBound
    {family : BooleanListCodeFamily}
    (realization : UniformEncodedMessageDecoderRealization family)
    (bounds : family.PolynomialParameterBounds)
    {messageLength outputLength inverseDensity seedLength : ℕ}
    (design : NWDesign outputLength
      (family.coordinateLength messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)) seedLength)
    (test : Finset (Fin outputLength → Bool)) (budget : ℕ) : ℕ :=
  realization.framedDescriptionBound design test
    (inverseDensityDescriptionBound family bounds messageLength outputLength
      inverseDensity seedLength budget)

end UniformEncodedMessageDecoderRealization

/-- A single oracle decoder machine for every instance of one Boolean
list-code family. All numeric parameters and the NW design are supplied by the
canonical self-describing instance codec; the statistical test remains separate
oracle access and contributes no program bits. -/
structure UniformOracleEncodedMessageDecoderRealization
    (family : BooleanListCodeFamily) where
  /-- Number of ordinary work tapes in addition to the query tape. -/
  tapes : ℕ
  /-- One oracle decoder machine for the whole family. -/
  machine : OracleTM tapes
  /-- Decoder clock as a function of total framed program length. -/
  time : ℕ → ℕ
  /-- Larger framed programs receive no smaller clock. -/
  time_mono : Monotone time
  /-- Correctness for every family parameter, canonically encoded design, and
  finite test oracle. -/
  correct :
    ∀ {messageLength inverseAccuracy outputLength seedLength : ℕ}
      (design : NWDesign outputLength
        (family.coordinateLength messageLength inverseAccuracy) seedLength)
      (test : Finset (Fin outputLength → Bool)) (description : List Bool)
      (message : Fin messageLength → Bool),
      decodeIndexedMessage? design (family.code messageLength inverseAccuracy)
          test description = some message →
        machine.ProducesInTime (finiteTestOracle test)
          (pair (decoderInstance messageLength inverseAccuracy design).encode
            description) (List.ofFn message)
          (time (pair
            (decoderInstance messageLength inverseAccuracy design).encode
            description).length)

namespace UniformOracleEncodedMessageDecoderRealization

/-- Total program bound after framing a design encoding with an indexed
reconstruction description of length at most `descriptionBound`. -/
def framedDescriptionBound
    {family : BooleanListCodeFamily}
    {messageLength inverseAccuracy outputLength seedLength : ℕ}
    (design : NWDesign outputLength
      (family.coordinateLength messageLength inverseAccuracy) seedLength)
    (descriptionBound : ℕ) : ℕ :=
  2 * (decoderInstance messageLength inverseAccuracy design).encode.length +
    2 + descriptionBound

/-- Total framed program bound at the canonical inverse-density parameters. -/
def inverseDensityFramedDescriptionBound
    {family : BooleanListCodeFamily}
    (bounds : family.PolynomialParameterBounds)
    {messageLength outputLength inverseDensity seedLength : ℕ}
    (design : NWDesign outputLength
      (family.coordinateLength messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)) seedLength)
    (budget : ℕ) : ℕ :=
  framedDescriptionBound design
    (inverseDensityDescriptionBound family bounds messageLength outputLength
      inverseDensity seedLength budget)

end UniformOracleEncodedMessageDecoderRealization

end NWDesign

end Complexity
