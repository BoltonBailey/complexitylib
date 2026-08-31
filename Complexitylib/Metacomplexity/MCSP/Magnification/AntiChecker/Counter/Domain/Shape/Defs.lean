/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Domain.Defs

/-!
# Finite shapes of bounded circuit codes -- definitions

A branch shape chooses a positive gate count within the small-circuit threshold
and a code length within the delimiter bound. The terminated-unary count prefix
must fit before that delimiter. What remains between the two is a fixed-width
live gate body suitable for a serialized evaluator query.
-/


@[expose] public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- A positive gate count and bounded code length whose unary count prefix fits
strictly before the bounded-code delimiter. -/
def CandidateCodeShape (bound threshold : ℕ) :=
  { shape : Fin threshold × Fin (bound + 1) //
    shape.1.val + 2 ≤ shape.2.val }

namespace CandidateCodeShape

instance (bound threshold : ℕ) : Fintype (CandidateCodeShape bound threshold) :=
  inferInstanceAs (Fintype
    { shape : Fin threshold × Fin (bound + 1) //
      shape.1.val + 2 ≤ shape.2.val })

instance (bound threshold : ℕ) :
    DecidableEq (CandidateCodeShape bound threshold) :=
  inferInstanceAs (DecidableEq
    { shape : Fin threshold × Fin (bound + 1) //
      shape.1.val + 2 ≤ shape.2.val })

/-- Positive gate count represented by this branch shape. -/
def gateCount {bound threshold : ℕ}
    (shape : CandidateCodeShape bound threshold) : ℕ :=
  shape.val.1.val + 1

/-- Delimited circuit-code length represented by this branch shape. -/
def codeLength {bound threshold : ℕ}
    (shape : CandidateCodeShape bound threshold) : ℕ :=
  shape.val.2.val

/-- Width of the serialized gate body after removing the unary count prefix. -/
def gateBodyWidth {bound threshold : ℕ}
    (shape : CandidateCodeShape bound threshold) : ℕ :=
  shape.codeLength - (shape.gateCount + 1)

/-- Extract the gate-body bits between a shape's count prefix and delimiter. -/
def gateBody {bound threshold : ℕ}
    (shape : CandidateCodeShape bound threshold)
    (encoded : BitString (boundedCodeWidth bound)) :
    BitString shape.gateBodyWidth :=
  fun coordinate =>
    encoded ⟨shape.gateCount + 1 + coordinate.val, by
      have hcoordinate := coordinate.isLt
      have hprefix : shape.gateCount + 1 ≤ shape.codeLength := shape.property
      have hlength : shape.codeLength ≤ bound := by
        have := shape.val.2.isLt
        simp only [codeLength]
        omega
      simp only [gateBodyWidth] at hcoordinate
      simp only [boundedCodeWidth]
      omega⟩

/-- Reconstruct the variable-length code selected by a branch shape. -/
def code {bound threshold : ℕ}
    (shape : CandidateCodeShape bound threshold)
    (encoded : BitString (boundedCodeWidth bound)) : List Bool :=
  CircuitCode.NatCode.encode shape.gateCount ++
    (shape.gateBody encoded).toList

/-- The reconstructed variable-length code delimiter-encodes back to the
supplied fixed-width string. -/
def Matches {bound threshold : ℕ}
    (shape : CandidateCodeShape bound threshold)
    (encoded : BitString (boundedCodeWidth bound)) : Prop :=
  encodeBoundedCode bound (shape.code encoded) = encoded

instance {bound threshold : ℕ} (shape : CandidateCodeShape bound threshold)
    (encoded : BitString (boundedCodeWidth bound)) :
    Decidable (shape.Matches encoded) := by
  unfold Matches
  infer_instance

end CandidateCodeShape

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
