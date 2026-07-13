/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.Encoding
import Complexitylib.Circuits.Family
import Complexitylib.Encoding.Pairing

/-!
# Encodings of whole circuit families

This module adds the length-zero wrapper around the positive-arity circuit
codec. A leading tag distinguishes the explicit empty-input answer from an
ordinary encoded circuit.
-/

namespace Complexity

namespace CircuitFamily

/-- Encode the member of an AND/OR circuit family at input length `n`.

The zero-length member is the tag `false` followed by its explicit answer.
Positive lengths use the tag `true` followed by the ordinary circuit code. -/
def encodeAt (F : CircuitFamily Basis.andOr2) : (n : ℕ) → List Bool
  | 0 => [false, F.emptyOutput]
  | n + 1 => true :: CircuitCode.encodeCircuit (F.circuit (n + 1))

/-- The length-zero member encodes as the `false` tag followed by the explicit answer bit. -/
@[simp] theorem encodeAt_zero (F : CircuitFamily Basis.andOr2) :
    F.encodeAt 0 = [false, F.emptyOutput] := rfl

/-- A positive-length member encodes as the `true` tag followed by its circuit's code. -/
@[simp] theorem encodeAt_succ (F : CircuitFamily Basis.andOr2) (n : ℕ) :
    F.encodeAt (n + 1) =
      true :: CircuitCode.encodeCircuit (F.circuit (n + 1)) := rfl

end CircuitFamily

namespace CircuitCode

/-- Evaluate a tagged family code on a variable-length input.

The zero tag is accepted only for the empty input and must carry exactly one
answer bit. The positive tag is accepted only for a nonempty input and delegates
to the exact-arity circuit evaluator. -/
def evalFamilyCode (code input : List Bool) : Option Bool :=
  if input.isEmpty then
    match code with
    | [false, answer] => some answer
    | _ => none
  else
    match code with
    | true :: circuitCode => evalCode input.length circuitCode input
    | _ => none

/-- Decode one self-delimiting machine input into a tagged family code and
its argument, then evaluate the code. Malformed outer pairs and malformed
inner circuit codes both return `none`. -/
def evalFamilyPair? (z : List Bool) : Option Bool :=
  (unpair? z).bind fun (code, input) => evalFamilyCode code input

/-- Evaluating a canonical pair delegates directly to the tagged family-code
evaluator. -/
@[simp] theorem evalFamilyPair?_pair (code input : List Bool) :
    evalFamilyPair? (pair code input) = evalFamilyCode code input := by
  simp [evalFamilyPair?]

/-- On the empty input, successful evaluation is exactly a canonical zero tag
    carrying one answer bit. -/
theorem evalFamilyCode_nil_isSome_iff (code : List Bool) :
    (evalFamilyCode code []).isSome ↔
      ∃ answer : Bool, code = [false, answer] := by
  cases code with
  | nil => simp [evalFamilyCode]
  | cons tag rest =>
      cases tag <;> cases rest with
      | nil => simp [evalFamilyCode]
      | cons answer tail =>
          cases tail <;> simp [evalFamilyCode]

/-- On a nonempty input, successful evaluation is exactly a positive tag
    carrying a canonical, topologically well-formed circuit code. -/
theorem evalFamilyCode_isSome_iff_of_ne_nil (code input : List Bool)
    (hne : input ≠ []) :
    (evalFamilyCode code input).isSome ↔
      ∃ circuit : RawCircuit,
        code = true :: circuit.encode ∧ circuit.WellFormed input.length := by
  cases code with
  | nil => simp [evalFamilyCode, hne]
  | cons tag circuitCode =>
      cases tag <;> simp [evalFamilyCode, hne, evalCode_isSome_iff]

/-- Tagged family encoding handles the explicit empty-input bit and agrees with
    the typed circuit at every positive input length. -/
@[simp] theorem evalFamilyCode_encodeAt (F : CircuitFamily Basis.andOr2)
    {n : ℕ} (input : BitString n) :
    evalFamilyCode (F.encodeAt n) input.toList = some (F.function n input) := by
  cases n with
  | zero =>
      have hnil : input.toList = [] := by
        apply List.eq_nil_of_length_eq_zero
        exact BitString.length_toList input
      simp [evalFamilyCode, hnil]
  | succ n =>
      have hne : input.toList ≠ [] := by
        intro h
        have hlen := BitString.length_toList input
        simp [h] at hlen
      simp [evalFamilyCode, hne, evalCode_encodeCircuit]

/-- Machine-facing list form of `evalFamilyCode_encodeAt`: selecting the member
    at the supplied input's length agrees with `CircuitFamily.evalList`. -/
@[simp] theorem evalFamilyCode_encodeAt_length (F : CircuitFamily Basis.andOr2)
    (input : List Bool) :
    evalFamilyCode (F.encodeAt input.length) input = some (F.evalList input) := by
  simpa [BitString.toList, CircuitFamily.evalList] using
    evalFamilyCode_encodeAt F input.get

/-- Pairing a family member's canonical code with its input evaluates to the
family's Boolean answer. -/
theorem evalFamilyPair?_encodeAt (F : CircuitFamily Basis.andOr2)
    (input : List Bool) :
    evalFamilyPair? (pair (F.encodeAt input.length) input) =
      some (F.evalList input) := by
  simp

/-- The length-zero tagged code has exactly two bits: the tag and the answer. -/
theorem encodeAt_zero_length (F : CircuitFamily Basis.andOr2) :
    (F.encodeAt 0).length = 2 := rfl

/-- A positive-length tagged code is one bit (the tag) longer than the underlying
    circuit code. -/
@[simp] theorem encodeAt_succ_length (F : CircuitFamily Basis.andOr2) (n : ℕ) :
    (F.encodeAt (n + 1)).length =
      (encodeCircuit (F.circuit (n + 1))).length + 1 := by
  simp [CircuitFamily.encodeAt]

/-- The positive-length tagged family code inherits the concrete polynomial
    bound for its member circuit. -/
theorem encodeAt_succ_length_le (F : CircuitFamily Basis.andOr2) (n : ℕ) :
    (F.encodeAt (n + 1)).length ≤
      2 + F.size (n + 1) * (2 * (n + 1 + F.size (n + 1)) + 6) := by
  have h := encodeCircuit_length_le_size (F.circuit (n + 1))
  rw [encodeAt_succ_length]
  rw [F.size_succ]
  omega

/-- Every tagged family code satisfies the concrete length bound, including
    the explicit two-bit code at input length zero. -/
theorem encodeAt_length_le (F : CircuitFamily Basis.andOr2) (n : ℕ) :
    (F.encodeAt n).length ≤
      2 + F.size n * (2 * (n + F.size n) + 6) := by
  cases n with
  | zero => simp
  | succ n =>
      simpa [Nat.succ_eq_add_one] using encodeAt_succ_length_le F n

end CircuitCode

end Complexity
