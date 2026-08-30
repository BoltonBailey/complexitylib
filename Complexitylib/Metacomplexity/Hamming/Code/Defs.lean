/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Hamming.Defs

/-!
# Finite Boolean codes -- definitions

An abstract Boolean code is an injective map from fixed-length messages to
fixed-length codewords. Correctness, minimum distance, exhaustive decoding,
and rate are represented independently of any efficiency claim.
-/


@[expose] public section

namespace Complexity

/-- An injective fixed-block-length Boolean encoding. -/
structure BooleanCode (messageLength blockLength : ℕ) where
  /-- Encode one message as a codeword. -/
  encode : BooleanHamming.Word messageLength → BooleanHamming.Word blockLength
  /-- Distinct messages have distinct codewords. -/
  encode_injective : Function.Injective encode

namespace BooleanCode

/-- Exact rational information rate for the two code lengths. At block length
zero this uses the total rational-division convention. -/
def rate (messageLength blockLength : ℕ) : ℚ :=
  messageLength / blockLength

/-- Finite image of all messages. -/
def codewords {messageLength blockLength : ℕ}
    (code : BooleanCode messageLength blockLength) :
    Finset (BooleanHamming.Word blockLength) :=
  Finset.univ.image code.encode

/-- Every pair of distinct messages encodes at distance at least the stated
minimum. -/
def HasMinimumDistance {messageLength blockLength : ℕ}
    (code : BooleanCode messageLength blockLength)
    (minimumDistance : ℕ) : Prop :=
  ∀ left right, left ≠ right →
    minimumDistance ≤ BooleanHamming.distance (code.encode left) (code.encode right)

/-- Exhaustive list of messages whose codewords lie in a received-word ball. -/
def decodeCandidates {messageLength blockLength : ℕ}
    (code : BooleanCode messageLength blockLength)
    (received : BooleanHamming.Word blockLength) (radius : ℕ) :
    Finset (BooleanHamming.Word messageLength) :=
  Finset.univ.filter fun message =>
    BooleanHamming.distance (code.encode message) received ≤ radius

/-- Exhaustive decoder returning the first nearby message, if one exists.
Minimum-distance hypotheses make this result unique but do not make the search
efficient. -/
noncomputable def decodeUnique? {messageLength blockLength : ℕ}
    (code : BooleanCode messageLength blockLength)
    (received : BooleanHamming.Word blockLength) (radius : ℕ) :
    Option (BooleanHamming.Word messageLength) :=
  (code.decodeCandidates received radius).toList.head?

end BooleanCode

end Complexity
