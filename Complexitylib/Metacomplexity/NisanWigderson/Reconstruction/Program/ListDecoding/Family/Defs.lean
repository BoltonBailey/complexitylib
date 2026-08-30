/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.ListDecoding.Family.Defs
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.ListDecoding.Defs

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

end NWDesign

end Complexity
