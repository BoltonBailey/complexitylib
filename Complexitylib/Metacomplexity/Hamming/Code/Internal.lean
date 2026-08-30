/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Hamming.Code.Defs
import Complexitylib.Metacomplexity.Hamming.Internal

/-!
# Finite Boolean codes -- proof internals
-/


public section

namespace Complexity

namespace BooleanCode

theorem mem_codewords_iff_internal {messageLength blockLength : ℕ}
    (code : BooleanCode messageLength blockLength)
    (word : BooleanHamming.Word blockLength) :
    word ∈ code.codewords ↔ ∃ message, code.encode message = word := by
  simp [codewords]

theorem card_codewords_internal {messageLength blockLength : ℕ}
    (code : BooleanCode messageLength blockLength) :
    code.codewords.card = 2 ^ messageLength := by
  rw [codewords,
    Finset.card_image_of_injective Finset.univ code.encode_injective,
    Finset.card_univ, card_finArrowBool]

theorem isSeparated_codewords_internal {messageLength blockLength : ℕ}
    {code : BooleanCode messageLength blockLength} {minimumDistance : ℕ}
    (hdistance : code.HasMinimumDistance minimumDistance) :
    BooleanHamming.IsSeparated code.codewords minimumDistance := by
  intro left hleft right hright hne
  obtain ⟨leftMessage, hleftCode⟩ :=
    (mem_codewords_iff_internal code left).mp hleft
  obtain ⟨rightMessage, hrightCode⟩ :=
    (mem_codewords_iff_internal code right).mp hright
  have hmessages : leftMessage ≠ rightMessage := by
    intro heq
    apply hne
    rw [← hleftCode, ← hrightCode, heq]
  simpa [hleftCode, hrightCode] using
    hdistance leftMessage rightMessage hmessages

theorem packing_bound_internal {messageLength blockLength minimumDistance radius : ℕ}
    {code : BooleanCode messageLength blockLength}
    (hdistance : code.HasMinimumDistance minimumDistance)
    (hradius : 2 * radius < minimumDistance) :
    2 ^ messageLength * BooleanHamming.volume blockLength radius ≤
      2 ^ blockLength := by
  have hpacking := BooleanHamming.packing_bound_internal
    (code := code.codewords)
    (isSeparated_codewords_internal hdistance) hradius
  rw [card_codewords_internal] at hpacking
  exact hpacking

theorem mem_decodeCandidates_iff_internal {messageLength blockLength : ℕ}
    (code : BooleanCode messageLength blockLength)
    (received : BooleanHamming.Word blockLength) (radius : ℕ)
    (message : BooleanHamming.Word messageLength) :
    message ∈ code.decodeCandidates received radius ↔
      BooleanHamming.distance (code.encode message) received ≤ radius := by
  simp [decodeCandidates]

theorem mem_decodeCandidates_of_close_internal {messageLength blockLength : ℕ}
    (code : BooleanCode messageLength blockLength)
    (received : BooleanHamming.Word blockLength) (radius : ℕ)
    (message : BooleanHamming.Word messageLength)
    (hclose : BooleanHamming.distance (code.encode message) received ≤ radius) :
    message ∈ code.decodeCandidates received radius := by
  exact (mem_decodeCandidates_iff_internal code received radius message).mpr hclose

theorem eq_of_mem_decodeCandidates_internal {messageLength blockLength : ℕ}
    {code : BooleanCode messageLength blockLength}
    {minimumDistance radius : ℕ}
    (hdistance : code.HasMinimumDistance minimumDistance)
    (hradius : 2 * radius < minimumDistance)
    (received : BooleanHamming.Word blockLength)
    {left right : BooleanHamming.Word messageLength}
    (hleft : left ∈ code.decodeCandidates received radius)
    (hright : right ∈ code.decodeCandidates received radius) :
    left = right := by
  by_contra hne
  have hminimum := hdistance left right hne
  have hleftClose :=
    (mem_decodeCandidates_iff_internal code received radius left).mp hleft
  have hrightClose :=
    (mem_decodeCandidates_iff_internal code received radius right).mp hright
  have hreceivedRight :
      BooleanHamming.distance received (code.encode right) ≤ radius := by
    rw [BooleanHamming.distance_comm_internal]
    exact hrightClose
  have htriangle := BooleanHamming.distance_triangle_internal
    (code.encode left) received (code.encode right)
  omega

theorem card_decodeCandidates_le_one_internal {messageLength blockLength : ℕ}
    {code : BooleanCode messageLength blockLength}
    {minimumDistance radius : ℕ}
    (hdistance : code.HasMinimumDistance minimumDistance)
    (hradius : 2 * radius < minimumDistance)
    (received : BooleanHamming.Word blockLength) :
    (code.decodeCandidates received radius).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro left right hleft hright
  exact eq_of_mem_decodeCandidates_internal
    hdistance hradius received hleft hright

theorem decodeCandidates_eq_singleton_of_close_internal
    {messageLength blockLength : ℕ}
    {code : BooleanCode messageLength blockLength}
    {minimumDistance radius : ℕ}
    (hdistance : code.HasMinimumDistance minimumDistance)
    (hradius : 2 * radius < minimumDistance)
    (received : BooleanHamming.Word blockLength)
    (message : BooleanHamming.Word messageLength)
    (hclose : BooleanHamming.distance (code.encode message) received ≤ radius) :
    code.decodeCandidates received radius = {message} := by
  have hmessage :=
    mem_decodeCandidates_of_close_internal code received radius message hclose
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨hmessage, ?_⟩
  intro candidate hcandidate
  exact eq_of_mem_decodeCandidates_internal
    hdistance hradius received hcandidate hmessage

theorem decodeUnique?_eq_some_of_close_internal
    {messageLength blockLength : ℕ}
    {code : BooleanCode messageLength blockLength}
    {minimumDistance radius : ℕ}
    (hdistance : code.HasMinimumDistance minimumDistance)
    (hradius : 2 * radius < minimumDistance)
    (received : BooleanHamming.Word blockLength)
    (message : BooleanHamming.Word messageLength)
    (hclose : BooleanHamming.distance (code.encode message) received ≤ radius) :
    code.decodeUnique? received radius = some message := by
  rw [decodeUnique?,
    decodeCandidates_eq_singleton_of_close_internal
      hdistance hradius received message hclose]
  simp

end BooleanCode

end Complexity
