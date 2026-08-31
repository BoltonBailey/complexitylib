/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Domain.Shape.Defs
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Domain.Shape.Internal

/-!
# Finite shapes of bounded circuit codes

Every delimiter-encoded canonical small-circuit code has one of finitely many
positive gate-count and code-length shapes. At a fixed shape, the live gate
body has constant width. Encoded survivor membership is therefore an
existential disjunction over a polynomially bounded set of shapes, with exact
shape reconstruction, raw-code validity, and labeled-sample agreement.
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

namespace CandidateCodeShape

/-- The number of valid shapes is at most the number of gate-count and
code-length pairs before imposing the prefix-fit condition. -/
theorem card_le (bound threshold : ℕ) :
    Fintype.card (CandidateCodeShape bound threshold) ≤
      threshold * (bound + 1) :=
  card_le_internal bound threshold

/-- Every branch shape represents a positive gate count. -/
theorem one_le_gateCount {bound threshold : ℕ}
    (shape : CandidateCodeShape bound threshold) :
    1 ≤ shape.gateCount :=
  one_le_gateCount_internal shape

/-- A branch shape's gate count is within the requested threshold. -/
theorem gateCount_le_threshold {bound threshold : ℕ}
    (shape : CandidateCodeShape bound threshold) :
    shape.gateCount ≤ threshold :=
  gateCount_le_threshold_internal shape

/-- The terminated-unary gate-count prefix fits before the delimiter. -/
theorem countPrefix_le_codeLength {bound threshold : ℕ}
    (shape : CandidateCodeShape bound threshold) :
    shape.gateCount + 1 ≤ shape.codeLength :=
  countPrefix_le_codeLength_internal shape

/-- A branch shape's delimiter position lies inside the advertised bound. -/
theorem codeLength_le_bound {bound threshold : ℕ}
    (shape : CandidateCodeShape bound threshold) :
    shape.codeLength ≤ bound :=
  codeLength_le_bound_internal shape

/-- Reconstructing a shape's unary prefix and gate body gives exactly its
selected code length. -/
theorem length_code {bound threshold : ℕ}
    (shape : CandidateCodeShape bound threshold)
    (encoded : BitString (boundedCodeWidth bound)) :
    (shape.code encoded).length = shape.codeLength :=
  length_code_internal shape encoded

/-- Encoded labeled-survivor membership is exactly a finite disjunction over
matching code shapes whose reconstructed code is small, valid, and agrees
with every labeled sample. -/
theorem mem_encodedCandidateLabeledSurvivorCodes_iff_exists_shape
    {count arity threshold : ℕ}
    {samples : Fin count → SuccinctMCSP.Sample arity}
    {encoded : BitString (candidateCodeWidth arity threshold)} :
    encoded ∈ encodedCandidateLabeledSurvivorCodes arity threshold samples ↔
      ∃ shape : CandidateCodeShape
          (AntiChecker.codeLengthBound arity threshold) threshold,
        shape.Matches encoded ∧
          AntiChecker.IsSmallCircuitCode arity threshold
            (shape.code encoded) ∧
          CodeMatchesLabeledSamples samples (shape.code encoded) :=
  mem_encodedCandidateLabeledSurvivorCodes_iff_exists_shape_internal

end CandidateCodeShape

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
