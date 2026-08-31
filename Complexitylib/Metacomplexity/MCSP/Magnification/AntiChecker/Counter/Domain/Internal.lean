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
    let marker : Fin (boundedCodeWidth bound) :=
      Fin.castAdd bound
        (⟨first.length, Nat.lt_succ_iff.mpr hfirst⟩ : Fin (bound + 1))
    have hmarker := congrFun hencode marker
    dsimp only [marker, encodeBoundedCode] at hmarker
    rw [Fin.append_left, Fin.append_left] at hmarker
    simpa [Nat.min_eq_left hfirst, Nat.min_eq_left hsecond] using hmarker
  apply List.ext_get hlength
  intro index hfirstIndex hsecondIndex
  have hindex : index < bound := lt_of_lt_of_le hfirstIndex hfirst
  let content : Fin (boundedCodeWidth bound) :=
    Fin.natAdd (bound + 1) (⟨index, hindex⟩ : Fin bound)
  have hcontent := congrFun hencode content
  dsimp only [content, encodeBoundedCode] at hcontent
  rw [Fin.append_right, Fin.append_right] at hcontent
  simpa [hfirstIndex, hsecondIndex] using hcontent

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
