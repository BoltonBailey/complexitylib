/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.AverageCase.FiniteEnsemble.Defs
public import Complexitylib.Mathlib.NatBits

/-!
# Finite Boolean list decoding -- definitions

A Boolean list code maps fixed-length messages to Boolean functions on an
arbitrary finite coordinate type. Its decoder returns a fixed-size indexed
candidate list. Relative distance and agreement are exact rational uniform
probabilities, matching the truth-table view used in metacomplexity.
-/


@[expose] public section

universe u

namespace Complexity

/-- A fixed-length binary code together with a decoder producing `listSize`
candidate messages. -/
structure BooleanListCode (messageLength listSize : ℕ) (coordinate : Type u) where
  /-- Encode a message as a Boolean function on the codeword coordinates. -/
  encode : (Fin messageLength → Bool) → coordinate → Bool
  /-- Decode any received word into a fixed-size indexed candidate list. -/
  decode : (coordinate → Bool) → Fin listSize →
    (Fin messageLength → Bool)

namespace BooleanListCode

/-- Exact fraction of coordinates on which two Boolean words agree. -/
def agreementProbability {coordinate : Type u} [Fintype coordinate]
    (left right : coordinate → Bool) : ℚ :=
  uniformProbability <| Finset.univ.filter fun input => left input = right input

/-- Exact relative Hamming distance between two Boolean words. -/
def relativeDistance {coordinate : Type u} [Fintype coordinate]
    (left right : coordinate → Bool) : ℚ :=
  uniformProbability <| Finset.univ.filter fun input => left input ≠ right input

/-- List-decoding guarantee at a relative Hamming radius. -/
def IsListDecodableAt {messageLength listSize : ℕ} {coordinate : Type u}
    [Fintype coordinate] (code : BooleanListCode messageLength listSize coordinate)
    (radius : ℚ) : Prop :=
  ∀ message received,
    relativeDistance (code.encode message) received ≤ radius →
      ∃ index, code.decode received index = message

/-- Distinct messages appearing among the decoder's indexed candidates. -/
def candidates {messageLength listSize : ℕ} {coordinate : Type u}
    (code : BooleanListCode messageLength listSize coordinate)
    (received : coordinate → Bool) : Finset (Fin messageLength → Bool) :=
  Finset.univ.image (code.decode received)

/-- Number of bits sufficient to select one of `listSize` indexed decoder
outputs. -/
def decoderIndexBitWidth (listSize : ℕ) : ℕ :=
  Nat.clog 2 listSize

/-- Fixed-width binary encoding of an indexed decoder output. -/
def encodeDecoderIndex {listSize : ℕ} (index : Fin listSize) : List Bool :=
  Nat.toBits (decoderIndexBitWidth listSize) index

/-- Decode a fixed-width decoder index, rejecting malformed lengths and
values outside `Fin listSize`. -/
def decodeDecoderIndex? (listSize : ℕ) (bits : List Bool) : Option (Fin listSize) :=
  if _hlength : bits.length = decoderIndexBitWidth listSize then
    if hvalue : Nat.fromBits bits < listSize then
      some ⟨Nat.fromBits bits, hvalue⟩
    else
      none
  else
    none

/-- Decode a source message using a fixed-width encoded list index. -/
def decodeAtIndexBits? {messageLength listSize : ℕ} {coordinate : Type u}
    (code : BooleanListCode messageLength listSize coordinate)
    (received : coordinate → Bool) (bits : List Bool) :
    Option (Fin messageLength → Bool) :=
  match decodeDecoderIndex? listSize bits with
  | some index => some (code.decode received index)
  | none => none

end BooleanListCode

end Complexity
