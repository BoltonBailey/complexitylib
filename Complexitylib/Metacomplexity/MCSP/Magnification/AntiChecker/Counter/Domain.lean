/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Domain.Defs
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Domain.Internal

/-!
# Fixed-width anti-checker counter domains

Canonical variable-length circuit codes embed injectively into an explicit
Boolean cube of only one bit more than the maximum code length. Consequently,
counting the encoded survivors is exactly the existing labeled survivor count,
with no padding multiplicity.
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- The bounded-code encoding is injective on lists satisfying its advertised
length bound. -/
theorem encodeBoundedCode_injective_of_length_le
    {bound : ℕ} {first second : List Bool}
    (hfirst : first.length ≤ bound) (hsecond : second.length ≤ bound)
    (hencode : encodeBoundedCode bound first =
      encodeBoundedCode bound second) :
    first = second :=
  encodeBoundedCode_injective_of_length_le_internal
    hfirst hsecond hencode

/-- Membership in the fixed-width survivor domain is witnessed by one
canonical variable-length survivor code and its delimiter encoding. -/
theorem mem_encodedCandidateLabeledSurvivorCodes_iff
    {count arity threshold : ℕ}
    {samples : Fin count → SuccinctMCSP.Sample arity}
    {encoded : BitString (candidateCodeWidth arity threshold)} :
    encoded ∈ encodedCandidateLabeledSurvivorCodes arity threshold samples ↔
      ∃ code ∈ candidateLabeledSurvivorCodes arity threshold samples,
        encodeBoundedCode (AntiChecker.codeLengthBound arity threshold) code =
          encoded :=
  mem_encodedCandidateLabeledSurvivorCodes_iff_internal

/-- Packed-input survivor membership has the same explicit variable-code
witness characterization. -/
theorem mem_encodedSurvivorSet_iff
    {count arity threshold : ℕ}
    {input : BitString (count * (arity + 1))}
    {encoded : BitString (candidateCodeWidth arity threshold)} :
    encoded ∈ encodedSurvivorSet arity threshold input ↔
      ∃ code ∈ candidateLabeledSurvivorCodes arity threshold
          (unpackLabeledSamples input),
        encodeBoundedCode (AntiChecker.codeLengthBound arity threshold) code =
          encoded :=
  mem_encodedSurvivorSet_iff_internal

/-- Encoding canonical labeled survivors in the fixed Boolean cube preserves
their cardinality exactly. -/
theorem card_encodedCandidateLabeledSurvivorCodes
    {count arity threshold : ℕ}
    (samples : Fin count → SuccinctMCSP.Sample arity) :
    (encodedCandidateLabeledSurvivorCodes arity threshold samples).card =
      candidateLabeledSurvivorCount arity threshold samples :=
  card_encodedCandidateLabeledSurvivorCodes_internal samples

/-- The packed-input survivor set has exactly the canonical labeled survivor
count. -/
theorem card_encodedSurvivorSet {count arity threshold : ℕ}
    (input : BitString (count * (arity + 1))) :
    (encodedSurvivorSet arity threshold input).card =
      candidateLabeledSurvivorCount arity threshold
        (unpackLabeledSamples input) :=
  card_encodedSurvivorSet_internal input

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
