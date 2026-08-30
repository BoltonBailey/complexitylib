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

end NWDesign

end Complexity
