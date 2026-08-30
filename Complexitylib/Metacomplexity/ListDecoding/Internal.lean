/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.ListDecoding.Defs
import Complexitylib.Classes.AverageCase.FiniteEnsemble.Internal

/-!
# Finite Boolean list decoding -- proof internals
-/


public section

universe u

namespace Complexity

namespace BooleanListCode

theorem length_encodeDecoderIndex_internal
    {listSize : ℕ} (index : Fin listSize) :
    (encodeDecoderIndex index).length = decoderIndexBitWidth listSize := by
  simp [encodeDecoderIndex, decoderIndexBitWidth, Nat.length_toBits]

theorem decodeDecoderIndex?_encodeDecoderIndex_internal
    {listSize : ℕ} (index : Fin listSize) :
    decodeDecoderIndex? listSize (encodeDecoderIndex index) = some index := by
  have hfits : index.val < 2 ^ decoderIndexBitWidth listSize :=
    lt_of_lt_of_le index.isLt
      (Nat.le_pow_clog Nat.one_lt_two listSize)
  unfold decodeDecoderIndex?
  rw [length_encodeDecoderIndex_internal, dif_pos rfl]
  simp only [encodeDecoderIndex]
  simp [Nat.fromBits_toBits hfits, index.isLt]

theorem decodeAtIndexBits?_encodeDecoderIndex_internal
    {messageLength listSize : ℕ} {coordinate : Type u}
    (code : BooleanListCode messageLength listSize coordinate)
    (received : coordinate → Bool) (index : Fin listSize) :
    code.decodeAtIndexBits? received (encodeDecoderIndex index) =
      some (code.decode received index) := by
  simp [decodeAtIndexBits?, decodeDecoderIndex?_encodeDecoderIndex_internal]

theorem relativeDistance_eq_one_sub_agreementProbability_internal
    {coordinate : Type u} [Fintype coordinate] [DecidableEq coordinate]
    [Nonempty coordinate] (left right : coordinate → Bool) :
    relativeDistance left right = 1 - agreementProbability left right := by
  have hevent :
      (Finset.univ.filter fun input => left input ≠ right input) =
        (Finset.univ.filter fun input => left input = right input)ᶜ := by
    ext input
    simp
  rw [relativeDistance, agreementProbability, hevent,
    uniformProbability_compl_internal]

theorem agreementProbability_add_relativeDistance_internal
    {coordinate : Type u} [Fintype coordinate] [DecidableEq coordinate]
    [Nonempty coordinate] (left right : coordinate → Bool) :
    agreementProbability left right + relativeDistance left right = 1 := by
  rw [relativeDistance_eq_one_sub_agreementProbability_internal]
  ring

theorem relativeDistance_le_of_agreementProbability_ge_internal
    {coordinate : Type u} [Fintype coordinate] [DecidableEq coordinate]
    [Nonempty coordinate] {left right : coordinate → Bool} {radius : ℚ}
    (hagreement : 1 - radius ≤ agreementProbability left right) :
    relativeDistance left right ≤ radius := by
  rw [relativeDistance_eq_one_sub_agreementProbability_internal]
  linarith

theorem exists_decoder_index_of_agreementProbability_ge_internal
    {messageLength listSize : ℕ} {coordinate : Type u}
    [Fintype coordinate] [DecidableEq coordinate] [Nonempty coordinate]
    {code : BooleanListCode messageLength listSize coordinate} {radius : ℚ}
    (hcode : code.IsListDecodableAt radius)
    (message : Fin messageLength → Bool) (received : coordinate → Bool)
    (hagreement : 1 - radius ≤
      agreementProbability (code.encode message) received) :
    ∃ index, code.decode received index = message := by
  exact hcode message received
    (relativeDistance_le_of_agreementProbability_ge_internal hagreement)

theorem exists_indexBits_of_agreementProbability_ge_internal
    {messageLength listSize : ℕ} {coordinate : Type u}
    [Fintype coordinate] [DecidableEq coordinate] [Nonempty coordinate]
    {code : BooleanListCode messageLength listSize coordinate} {radius : ℚ}
    (hcode : code.IsListDecodableAt radius)
    (message : Fin messageLength → Bool) (received : coordinate → Bool)
    (hagreement : 1 - radius ≤
      agreementProbability (code.encode message) received) :
    ∃ bits : List Bool,
      bits.length = decoderIndexBitWidth listSize ∧
        code.decodeAtIndexBits? received bits = some message := by
  obtain ⟨index, hdecode⟩ :=
    exists_decoder_index_of_agreementProbability_ge_internal
      hcode message received hagreement
  refine ⟨encodeDecoderIndex index,
    length_encodeDecoderIndex_internal index, ?_⟩
  rw [decodeAtIndexBits?_encodeDecoderIndex_internal, hdecode]

theorem mem_candidates_of_agreementProbability_ge_internal
    {messageLength listSize : ℕ} {coordinate : Type u}
    [Fintype coordinate] [DecidableEq coordinate] [Nonempty coordinate]
    {code : BooleanListCode messageLength listSize coordinate} {radius : ℚ}
    (hcode : code.IsListDecodableAt radius)
    (message : Fin messageLength → Bool) (received : coordinate → Bool)
    (hagreement : 1 - radius ≤
      agreementProbability (code.encode message) received) :
    message ∈ code.candidates received := by
  obtain ⟨index, hdecode⟩ :=
    exists_decoder_index_of_agreementProbability_ge_internal
      hcode message received hagreement
  exact Finset.mem_image.mpr ⟨index, Finset.mem_univ index, hdecode⟩

theorem card_candidates_le_internal
    {messageLength listSize : ℕ} {coordinate : Type u}
    (code : BooleanListCode messageLength listSize coordinate)
    (received : coordinate → Bool) :
    (code.candidates received).card ≤ listSize := by
  unfold candidates
  calc
    (Finset.univ.image (code.decode received)).card ≤
        (Finset.univ : Finset (Fin listSize)).card :=
      Finset.card_image_le
    _ = listSize := by simp

theorem mem_candidates_of_half_add_margin_internal
    {messageLength listSize : ℕ} {coordinate : Type u}
    [Fintype coordinate] [DecidableEq coordinate] [Nonempty coordinate]
    {code : BooleanListCode messageLength listSize coordinate} {margin : ℚ}
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (message : Fin messageLength → Bool) (received : coordinate → Bool)
    (hagreement : 1 / 2 + margin ≤
      agreementProbability (code.encode message) received) :
    message ∈ code.candidates received := by
  apply mem_candidates_of_agreementProbability_ge_internal
    hcode message received
  convert hagreement using 1
  all_goals ring

theorem exists_indexBits_of_half_add_margin_internal
    {messageLength listSize : ℕ} {coordinate : Type u}
    [Fintype coordinate] [DecidableEq coordinate] [Nonempty coordinate]
    {code : BooleanListCode messageLength listSize coordinate} {margin : ℚ}
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (message : Fin messageLength → Bool) (received : coordinate → Bool)
    (hagreement : 1 / 2 + margin ≤
      agreementProbability (code.encode message) received) :
    ∃ bits : List Bool,
      bits.length = decoderIndexBitWidth listSize ∧
        code.decodeAtIndexBits? received bits = some message := by
  apply exists_indexBits_of_agreementProbability_ge_internal
    hcode message received
  convert hagreement using 1
  all_goals ring

theorem mem_candidates_and_card_le_of_half_add_margin_internal
    {messageLength listSize : ℕ} {coordinate : Type u}
    [Fintype coordinate] [DecidableEq coordinate] [Nonempty coordinate]
    {code : BooleanListCode messageLength listSize coordinate} {margin : ℚ}
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (message : Fin messageLength → Bool) (received : coordinate → Bool)
    (hagreement : 1 / 2 + margin ≤
      agreementProbability (code.encode message) received) :
    message ∈ code.candidates received ∧
      (code.candidates received).card ≤ listSize := by
  exact ⟨mem_candidates_of_half_add_margin_internal
    hcode message received hagreement,
    card_candidates_le_internal code received⟩

end BooleanListCode

end Complexity
