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

Valid bounded circuit descriptions encode injectively into one parameter-sized
Boolean cube. Consequently, counting encoded survivors is exactly the existing
labeled survivor count, with no delimiter parser or padding multiplicity.
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- Membership in the fixed-width survivor domain is exactly successful
decoding to a valid description that matches every sample. -/
theorem mem_encodedCandidateLabeledSurvivorCodes_iff
    {count arity threshold : ℕ}
    {samples : Fin count → SuccinctMCSP.Sample arity}
    {encoded : BitString (candidateCodeWidth arity threshold)} :
    encoded ∈ encodedCandidateLabeledSurvivorCodes arity threshold samples ↔
      EncodedDescriptionMatchesLabeledSamples samples encoded :=
  mem_encodedCandidateLabeledSurvivorCodes_iff_internal

/-- Equivalently, a survivor word decodes to one valid description that
matches every labeled sample. -/
theorem mem_encodedCandidateLabeledSurvivorCodes_iff_exists_description
    {count arity threshold : ℕ}
    {samples : Fin count → SuccinctMCSP.Sample arity}
    {encoded : BitString (candidateCodeWidth arity threshold)} :
    encoded ∈ encodedCandidateLabeledSurvivorCodes arity threshold samples ↔
      ∃ description :
          CircuitCode.FixedWidth.ValidDescription arity threshold,
        CircuitCode.FixedWidth.Description.decode? encoded =
          some description.val ∧
        DescriptionMatchesLabeledSamples samples description :=
  mem_encodedCandidateLabeledSurvivorCodes_iff_exists_description_internal

/-- Packed-input survivor membership uses the decoded fixed-description
predicate on the unpacked labeled samples. -/
theorem mem_encodedSurvivorSet_iff
    {count arity threshold : ℕ}
    {input : BitString (count * (arity + 1))}
    {encoded : BitString (candidateCodeWidth arity threshold)} :
    encoded ∈ encodedSurvivorSet arity threshold input ↔
      EncodedDescriptionMatchesLabeledSamples
        (unpackLabeledSamples input) encoded :=
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
