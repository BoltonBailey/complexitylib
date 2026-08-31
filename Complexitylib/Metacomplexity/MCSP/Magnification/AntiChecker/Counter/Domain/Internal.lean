/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Domain.Defs
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Enumeration

/-!
# Fixed-width anti-checker counter domains -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

theorem encodeBoundedCode_injective_of_length_le_internal
    {bound : ℕ} {first second : List Bool}
    (hfirst : first.length ≤ bound) (hsecond : second.length ≤ bound)
    (hencode : encodeBoundedCode bound first =
      encodeBoundedCode bound second) :
    first = second := by
  have hlength : first.length = second.length := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · let marker : Fin (boundedCodeWidth bound) :=
        ⟨second.length, by simp [boundedCodeWidth, hsecond]⟩
      have hmarker := congrFun hencode marker
      have hnotLt : ¬second.length < first.length :=
        Nat.not_lt.mpr (Nat.le_of_lt hlt)
      have hneLength : second.length ≠ first.length :=
        Nat.ne_of_gt hlt
      simp [marker, encodeBoundedCode, hnotLt, hneLength] at hmarker
    · let marker : Fin (boundedCodeWidth bound) :=
        ⟨first.length, by simp [boundedCodeWidth, hfirst]⟩
      have hmarker := congrFun hencode marker
      have hnotLt : ¬first.length < second.length :=
        Nat.not_lt.mpr (Nat.le_of_lt hgt)
      have hneLength : first.length ≠ second.length :=
        Nat.ne_of_gt hgt
      simp [marker, encodeBoundedCode, hnotLt, hneLength] at hmarker
  apply List.ext_get hlength
  intro index hfirstIndex hsecondIndex
  let content : Fin (boundedCodeWidth bound) :=
    ⟨index, by simp [boundedCodeWidth]; omega⟩
  have hcontent := congrFun hencode content
  simpa [content, encodeBoundedCode, hfirstIndex, hsecondIndex] using hcontent

theorem card_encodedCandidateLabeledSurvivorCodes_internal
    {count arity threshold : ℕ}
    (samples : Fin count → SuccinctMCSP.Sample arity) :
    (encodedCandidateLabeledSurvivorCodes arity threshold samples).card =
      candidateLabeledSurvivorCount arity threshold samples := by
  unfold encodedCandidateLabeledSurvivorCodes
  rw [Finset.card_image_of_injOn]
  · rfl
  · intro first hfirst second hsecond hencode
    have hfirstCandidate :
        first ∈ AntiChecker.candidateCodes arity threshold := by
      exact (Finset.mem_filter.mp hfirst).1
    have hsecondCandidate :
        second ∈ AntiChecker.candidateCodes arity threshold := by
      exact (Finset.mem_filter.mp hsecond).1
    apply encodeBoundedCode_injective_of_length_le_internal
    · exact (AntiChecker.mem_candidateCodes_iff.mp hfirstCandidate).1
    · exact (AntiChecker.mem_candidateCodes_iff.mp hsecondCandidate).1
    · exact hencode

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
