/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Domain.Defs
import Complexitylib.Circuits.Encoding.FixedWidth.Codec
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Relation

/-!
# Fixed-width anti-checker counter domains -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

theorem mem_encodedCandidateLabeledSurvivorCodes_iff_internal
    {count arity threshold : ℕ}
    {samples : Fin count → SuccinctMCSP.Sample arity}
    {encoded : BitString (candidateCodeWidth arity threshold)} :
    encoded ∈ encodedCandidateLabeledSurvivorCodes arity threshold samples ↔
      EncodedDescriptionMatchesLabeledSamples samples encoded := by
  simp [encodedCandidateLabeledSurvivorCodes]

theorem mem_encodedCandidateLabeledSurvivorCodes_iff_exists_description_internal
    {count arity threshold : ℕ}
    {samples : Fin count → SuccinctMCSP.Sample arity}
    {encoded : BitString (candidateCodeWidth arity threshold)} :
    encoded ∈ encodedCandidateLabeledSurvivorCodes arity threshold samples ↔
      ∃ description :
          CircuitCode.FixedWidth.ValidDescription arity threshold,
        CircuitCode.FixedWidth.Description.decode? encoded =
          some description.val ∧
        DescriptionMatchesLabeledSamples samples description := by
  rw [mem_encodedCandidateLabeledSurvivorCodes_iff_internal]
  unfold EncodedDescriptionMatchesLabeledSamples
  cases hdecode : CircuitCode.FixedWidth.Description.decode? encoded with
  | none => simp
  | some description =>
      constructor
      · rintro ⟨hwell, hmatches⟩
        exact ⟨⟨description, hwell⟩, rfl, hmatches⟩
      · rintro ⟨other, hother, hmatches⟩
        have hequal : other.val = description :=
          Option.some.inj hother.symm
        subst description
        exact ⟨other.property, hmatches⟩

theorem mem_encodedSurvivorSet_iff_internal
    {count arity threshold : ℕ}
    {input : BitString (count * (arity + 1))}
    {encoded : BitString (candidateCodeWidth arity threshold)} :
    encoded ∈ encodedSurvivorSet arity threshold input ↔
      EncodedDescriptionMatchesLabeledSamples
        (unpackLabeledSamples input) encoded := by
  exact mem_encodedCandidateLabeledSurvivorCodes_iff_internal

theorem card_encodedCandidateLabeledSurvivorCodes_internal
    {count arity threshold : ℕ}
    (samples : Fin count → SuccinctMCSP.Sample arity) :
    (encodedCandidateLabeledSurvivorCodes arity threshold samples).card =
      candidateLabeledSurvivorCount arity threshold samples := by
  have hset :
      encodedCandidateLabeledSurvivorCodes arity threshold samples =
        (candidateLabeledSurvivorDescriptions arity threshold samples).image
          (fun description =>
            CircuitCode.FixedWidth.Description.encode description.val) := by
    ext encoded
    rw [mem_encodedCandidateLabeledSurvivorCodes_iff_exists_description_internal]
    constructor
    · rintro ⟨description, hdecode, hmatches⟩
      apply Finset.mem_image.mpr
      refine ⟨description, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hmatches⟩, ?_⟩
      exact (CircuitCode.FixedWidth.Description.decode?_eq_some_iff
        encoded description.val).mp hdecode |>.symm
    · rintro hencoded
      rcases Finset.mem_image.mp hencoded with
        ⟨description, hdescription, rfl⟩
      exact ⟨description,
        CircuitCode.FixedWidth.Description.decode?_encode description.val,
        (Finset.mem_filter.mp hdescription).2⟩
  have hinjective : Set.InjOn
      (fun description :
        CircuitCode.FixedWidth.ValidDescription arity threshold =>
          CircuitCode.FixedWidth.Description.encode description.val)
      (candidateLabeledSurvivorDescriptions arity threshold samples) := by
    intro first _ second _ hencode
    apply Subtype.ext
    exact CircuitCode.FixedWidth.Description.encode_injective hencode
  rw [hset]
  exact (Finset.card_image_of_injOn hinjective).trans
    (card_candidateLabeledSurvivorDescriptions samples)

theorem card_encodedSurvivorSet_internal {count arity threshold : ℕ}
    (input : BitString (count * (arity + 1))) :
    (encodedSurvivorSet arity threshold input).card =
      candidateLabeledSurvivorCount arity threshold
        (unpackLabeledSamples input) := by
  exact card_encodedCandidateLabeledSurvivorCodes_internal
    (unpackLabeledSamples input)

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
