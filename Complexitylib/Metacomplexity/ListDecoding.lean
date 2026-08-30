/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.ListDecoding.Defs
public import Complexitylib.Metacomplexity.ListDecoding.Internal
public import Complexitylib.Metacomplexity.ListDecoding.Family

/-!
# Finite Boolean list decoding

Exact truth-table agreement above `1/2 + ε` places the original message in
the candidate set of any code list-decodable up to radius `1/2 - ε`. The
candidate set contains at most the advertised indexed list size. A canonical
fixed-width codec stores the selecting index in exactly `clog₂(listSize)` bits
and turns the existential decoder occurrence into an actual bit string. The
family layer separates semantic inverse-accuracy decoding, concrete polynomial
parameter bounds, and single-machine encoder/full-decoder uniformity.
-/


public section

universe u

namespace Complexity

namespace BooleanListCode

/-- Encoding a decoder index uses exactly the ceiling-logarithmic number of
bits needed for the advertised list size. -/
@[simp] theorem length_encodeDecoderIndex
    {listSize : ℕ} (index : Fin listSize) :
    (encodeDecoderIndex index).length = decoderIndexBitWidth listSize :=
  length_encodeDecoderIndex_internal index

/-- Fixed-width decoder-index encoding round-trips exactly. -/
theorem decodeDecoderIndex?_encodeDecoderIndex
    {listSize : ℕ} (index : Fin listSize) :
    decodeDecoderIndex? listSize (encodeDecoderIndex index) = some index :=
  decodeDecoderIndex?_encodeDecoderIndex_internal index

/-- Selecting a list decoder output through its encoded index agrees with
selecting it directly. -/
theorem decodeAtIndexBits?_encodeDecoderIndex
    {messageLength listSize : ℕ} {coordinate : Type u}
    (code : BooleanListCode messageLength listSize coordinate)
    (received : coordinate → Bool) (index : Fin listSize) :
    code.decodeAtIndexBits? received (encodeDecoderIndex index) =
      some (code.decode received index) :=
  decodeAtIndexBits?_encodeDecoderIndex_internal code received index

/-- Relative Boolean Hamming distance is one minus exact agreement
probability. -/
theorem relativeDistance_eq_one_sub_agreementProbability
    {coordinate : Type u} [Fintype coordinate] [DecidableEq coordinate]
    [Nonempty coordinate] (left right : coordinate → Bool) :
    relativeDistance left right = 1 - agreementProbability left right :=
  relativeDistance_eq_one_sub_agreementProbability_internal left right

/-- Exact agreement and relative Hamming distance partition the coordinate
space. -/
theorem agreementProbability_add_relativeDistance
    {coordinate : Type u} [Fintype coordinate] [DecidableEq coordinate]
    [Nonempty coordinate] (left right : coordinate → Bool) :
    agreementProbability left right + relativeDistance left right = 1 :=
  agreementProbability_add_relativeDistance_internal left right

/-- Agreement at least `1 - radius` implies relative distance at most
`radius`. -/
theorem relativeDistance_le_of_agreementProbability_ge
    {coordinate : Type u} [Fintype coordinate] [DecidableEq coordinate]
    [Nonempty coordinate] {left right : coordinate → Bool} {radius : ℚ}
    (hagreement : 1 - radius ≤ agreementProbability left right) :
    relativeDistance left right ≤ radius :=
  relativeDistance_le_of_agreementProbability_ge_internal hagreement

/-- A list-decoding guarantee and sufficient agreement produce an indexed
decoder occurrence of the original message. -/
theorem exists_decoder_index_of_agreementProbability_ge
    {messageLength listSize : ℕ} {coordinate : Type u}
    [Fintype coordinate] [DecidableEq coordinate] [Nonempty coordinate]
    {code : BooleanListCode messageLength listSize coordinate} {radius : ℚ}
    (hcode : code.IsListDecodableAt radius)
    (message : Fin messageLength → Bool) (received : coordinate → Bool)
    (hagreement : 1 - radius ≤
      agreementProbability (code.encode message) received) :
    ∃ index, code.decode received index = message :=
  exists_decoder_index_of_agreementProbability_ge_internal
    hcode message received hagreement

/-- A list-decoding guarantee and sufficient agreement produce an actual
fixed-width bit string selecting the original message. -/
theorem exists_indexBits_of_agreementProbability_ge
    {messageLength listSize : ℕ} {coordinate : Type u}
    [Fintype coordinate] [DecidableEq coordinate] [Nonempty coordinate]
    {code : BooleanListCode messageLength listSize coordinate} {radius : ℚ}
    (hcode : code.IsListDecodableAt radius)
    (message : Fin messageLength → Bool) (received : coordinate → Bool)
    (hagreement : 1 - radius ≤
      agreementProbability (code.encode message) received) :
    ∃ bits : List Bool,
      bits.length = decoderIndexBitWidth listSize ∧
        code.decodeAtIndexBits? received bits = some message :=
  exists_indexBits_of_agreementProbability_ge_internal
    hcode message received hagreement

/-- Sufficient agreement places the original message in the decoder candidate
set. -/
theorem mem_candidates_of_agreementProbability_ge
    {messageLength listSize : ℕ} {coordinate : Type u}
    [Fintype coordinate] [DecidableEq coordinate] [Nonempty coordinate]
    {code : BooleanListCode messageLength listSize coordinate} {radius : ℚ}
    (hcode : code.IsListDecodableAt radius)
    (message : Fin messageLength → Bool) (received : coordinate → Bool)
    (hagreement : 1 - radius ≤
      agreementProbability (code.encode message) received) :
    message ∈ code.candidates received :=
  mem_candidates_of_agreementProbability_ge_internal
    hcode message received hagreement

/-- Deduplicating the indexed decoder output leaves at most `listSize`
messages. -/
theorem card_candidates_le
    {messageLength listSize : ℕ} {coordinate : Type u}
    (code : BooleanListCode messageLength listSize coordinate)
    (received : coordinate → Bool) :
    (code.candidates received).card ≤ listSize :=
  card_candidates_le_internal code received

/-- For a code list-decodable to radius `1/2 - ε`, agreement
`1/2 + ε` puts the message in the decoder candidate set. -/
theorem mem_candidates_of_half_add_margin
    {messageLength listSize : ℕ} {coordinate : Type u}
    [Fintype coordinate] [DecidableEq coordinate] [Nonempty coordinate]
    {code : BooleanListCode messageLength listSize coordinate} {margin : ℚ}
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (message : Fin messageLength → Bool) (received : coordinate → Bool)
    (hagreement : 1 / 2 + margin ≤
      agreementProbability (code.encode message) received) :
    message ∈ code.candidates received :=
  mem_candidates_of_half_add_margin_internal
    hcode message received hagreement

/-- At agreement `1/2 + ε`, the original message is selected by an actual
ceiling-logarithmic decoder-index string. -/
theorem exists_indexBits_of_half_add_margin
    {messageLength listSize : ℕ} {coordinate : Type u}
    [Fintype coordinate] [DecidableEq coordinate] [Nonempty coordinate]
    {code : BooleanListCode messageLength listSize coordinate} {margin : ℚ}
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (message : Fin messageLength → Bool) (received : coordinate → Bool)
    (hagreement : 1 / 2 + margin ≤
      agreementProbability (code.encode message) received) :
    ∃ bits : List Bool,
      bits.length = decoderIndexBitWidth listSize ∧
        code.decodeAtIndexBits? received bits = some message :=
  exists_indexBits_of_half_add_margin_internal
    hcode message received hagreement

/-- Hirahara's abstract list-decoding bridge: a `1/2 + ε` approximator
identifies a candidate set containing the original message and having at most
the advertised list size. -/
theorem mem_candidates_and_card_le_of_half_add_margin
    {messageLength listSize : ℕ} {coordinate : Type u}
    [Fintype coordinate] [DecidableEq coordinate] [Nonempty coordinate]
    {code : BooleanListCode messageLength listSize coordinate} {margin : ℚ}
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (message : Fin messageLength → Bool) (received : coordinate → Bool)
    (hagreement : 1 / 2 + margin ≤
      agreementProbability (code.encode message) received) :
    message ∈ code.candidates received ∧
      (code.candidates received).card ≤ listSize :=
  mem_candidates_and_card_le_of_half_add_margin_internal
    hcode message received hagreement

end BooleanListCode

end Complexity
