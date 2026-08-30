/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Hamming.Code.Defs
public import Complexitylib.Metacomplexity.Hamming.Code.Internal

/-!
# Finite Boolean codes

This module turns the finite Hamming geometry into an abstract coding layer.
An injective code has exactly `2^messageLength` codewords, minimum distance
implies the exact sphere-packing bound, and exhaustive decoding is uniquely
correct below half that distance. No runtime claim is bundled into these
semantic results.
-/


public section

namespace Complexity

namespace BooleanCode

/-- Codewords are exactly encoded messages. -/
theorem mem_codewords_iff {messageLength blockLength : ℕ}
    (code : BooleanCode messageLength blockLength)
    (word : BooleanHamming.Word blockLength) :
    word ∈ code.codewords ↔ ∃ message, code.encode message = word :=
  mem_codewords_iff_internal code word

/-- An injective Boolean code has exactly `2^messageLength` codewords. -/
@[simp] theorem card_codewords {messageLength blockLength : ℕ}
    (code : BooleanCode messageLength blockLength) :
    code.codewords.card = 2 ^ messageLength :=
  card_codewords_internal code

/-- A message-level minimum-distance contract separates the finite codeword
set by the same amount. -/
theorem isSeparated_codewords {messageLength blockLength : ℕ}
    {code : BooleanCode messageLength blockLength} {minimumDistance : ℕ}
    (hdistance : code.HasMinimumDistance minimumDistance) :
    BooleanHamming.IsSeparated code.codewords minimumDistance :=
  isSeparated_codewords_internal hdistance

/-- Coding-theoretic Hamming packing bound with exact finite parameters. -/
theorem packing_bound {messageLength blockLength minimumDistance radius : ℕ}
    {code : BooleanCode messageLength blockLength}
    (hdistance : code.HasMinimumDistance minimumDistance)
    (hradius : 2 * radius < minimumDistance) :
    2 ^ messageLength * BooleanHamming.volume blockLength radius ≤
      2 ^ blockLength :=
  packing_bound_internal hdistance hradius

/-- Candidate-list membership is exactly proximity of the encoded message. -/
@[simp] theorem mem_decodeCandidates_iff {messageLength blockLength : ℕ}
    (code : BooleanCode messageLength blockLength)
    (received : BooleanHamming.Word blockLength) (radius : ℕ)
    (message : BooleanHamming.Word messageLength) :
    message ∈ code.decodeCandidates received radius ↔
      BooleanHamming.distance (code.encode message) received ≤ radius :=
  mem_decodeCandidates_iff_internal code received radius message

/-- Every sufficiently close message occurs in exhaustive decoding. -/
theorem mem_decodeCandidates_of_close {messageLength blockLength : ℕ}
    (code : BooleanCode messageLength blockLength)
    (received : BooleanHamming.Word blockLength) (radius : ℕ)
    (message : BooleanHamming.Word messageLength)
    (hclose : BooleanHamming.distance (code.encode message) received ≤ radius) :
    message ∈ code.decodeCandidates received radius :=
  mem_decodeCandidates_of_close_internal code received radius message hclose

/-- Below half the minimum distance, any two decoding candidates coincide. -/
theorem eq_of_mem_decodeCandidates {messageLength blockLength : ℕ}
    {code : BooleanCode messageLength blockLength}
    {minimumDistance radius : ℕ}
    (hdistance : code.HasMinimumDistance minimumDistance)
    (hradius : 2 * radius < minimumDistance)
    (received : BooleanHamming.Word blockLength)
    {left right : BooleanHamming.Word messageLength}
    (hleft : left ∈ code.decodeCandidates received radius)
    (hright : right ∈ code.decodeCandidates received radius) :
    left = right :=
  eq_of_mem_decodeCandidates_internal
    hdistance hradius received hleft hright

/-- Exhaustive decoding contains at most one message below half the minimum
distance. -/
theorem card_decodeCandidates_le_one {messageLength blockLength : ℕ}
    {code : BooleanCode messageLength blockLength}
    {minimumDistance radius : ℕ}
    (hdistance : code.HasMinimumDistance minimumDistance)
    (hradius : 2 * radius < minimumDistance)
    (received : BooleanHamming.Word blockLength) :
    (code.decodeCandidates received radius).card ≤ 1 :=
  card_decodeCandidates_le_one_internal hdistance hradius received

/-- A nearby message is the entire exhaustive candidate set below half the
minimum distance. -/
theorem decodeCandidates_eq_singleton_of_close
    {messageLength blockLength : ℕ}
    {code : BooleanCode messageLength blockLength}
    {minimumDistance radius : ℕ}
    (hdistance : code.HasMinimumDistance minimumDistance)
    (hradius : 2 * radius < minimumDistance)
    (received : BooleanHamming.Word blockLength)
    (message : BooleanHamming.Word messageLength)
    (hclose : BooleanHamming.distance (code.encode message) received ≤ radius) :
    code.decodeCandidates received radius = {message} :=
  decodeCandidates_eq_singleton_of_close_internal
    hdistance hradius received message hclose

/-- The exhaustive decoder recovers every message from fewer than half the
minimum-distance errors. -/
theorem decodeUnique?_eq_some_of_close
    {messageLength blockLength : ℕ}
    {code : BooleanCode messageLength blockLength}
    {minimumDistance radius : ℕ}
    (hdistance : code.HasMinimumDistance minimumDistance)
    (hradius : 2 * radius < minimumDistance)
    (received : BooleanHamming.Word blockLength)
    (message : BooleanHamming.Word messageLength)
    (hclose : BooleanHamming.distance (code.encode message) received ≤ radius) :
    code.decodeUnique? received radius = some message :=
  decodeUnique?_eq_some_of_close_internal
    hdistance hradius received message hclose

end BooleanCode

end Complexity
