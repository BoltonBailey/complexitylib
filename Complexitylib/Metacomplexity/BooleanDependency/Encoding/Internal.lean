/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.BooleanDependency.Encoding.Defs

/-!
# Canonical encoding of finite Boolean assignments and tables -- proof internals
-/


public section

namespace Complexity

namespace BooleanDependency

theorem OrderedAssignment.card_internal
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) :
    Fintype.card (OrderedAssignment coordinates) = 2 ^ coordinates.card := by
  simpa using Fintype.card_congr
    (OrderedAssignment.indexEquiv coordinates)

theorem length_encodeOrderedFunction_internal
    {index : Type*} [Fintype index] [LinearOrder index]
    (function : index → Bool) :
    (encodeOrderedFunction function).length = Fintype.card index := by
  simp [encodeOrderedFunction]

theorem decodeOrderedFunction?_encodeOrderedFunction_internal
    {index : Type*} [Fintype index] [LinearOrder index]
    (function : index → Bool) :
    decodeOrderedFunction? (encodeOrderedFunction function) = some function := by
  simp [decodeOrderedFunction?, encodeOrderedFunction]

theorem encodeOrderedFunction_injective_internal
    {index : Type*} [Fintype index] [LinearOrder index] :
    Function.Injective (encodeOrderedFunction : (index → Bool) → List Bool) := by
  intro first second heq
  have hdecode := congrArg
    (decodeOrderedFunction? (index := index)) heq
  simpa only [decodeOrderedFunction?_encodeOrderedFunction_internal,
    Option.some.injEq] using hdecode

theorem decodeOrderedFunction?_eq_none_iff_internal
    {index : Type*} [Fintype index] [LinearOrder index]
    (bits : List Bool) :
    decodeOrderedFunction? (index := index) bits = none ↔
      bits.length ≠ Fintype.card index := by
  simp [decodeOrderedFunction?]

theorem length_encodeAssignment_internal
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) (assignment : coordinates → Bool) :
    (encodeAssignment coordinates assignment).length = coordinates.card := by
  simp [encodeAssignment]

theorem decodeAssignment?_encodeAssignment_internal
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) (assignment : coordinates → Bool) :
    decodeAssignment? coordinates (encodeAssignment coordinates assignment) =
      some assignment := by
  simp [decodeAssignment?, encodeAssignment]

theorem encodeAssignment_injective_internal
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) :
    Function.Injective (encodeAssignment coordinates) := by
  intro first second heq
  have hdecode := congrArg (decodeAssignment? coordinates) heq
  simpa only [decodeAssignment?_encodeAssignment_internal,
    Option.some.injEq] using hdecode

theorem decodeAssignment?_eq_none_iff_internal
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) (bits : List Bool) :
    decodeAssignment? coordinates bits = none ↔
      bits.length ≠ coordinates.card := by
  simp [decodeAssignment?]

theorem length_encodeTable_internal
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate)
    (table : (coordinates → Bool) → Bool) :
    (encodeTable coordinates table).length = 2 ^ coordinates.card := by
  simp [encodeTable]

theorem decodeTable?_encodeTable_internal
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate)
    (table : (coordinates → Bool) → Bool) :
    decodeTable? coordinates (encodeTable coordinates table) = some table := by
  simp [decodeTable?, encodeTable]

theorem encodeTable_injective_internal
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) :
    Function.Injective (encodeTable coordinates) := by
  intro first second heq
  have hdecode := congrArg (decodeTable? coordinates) heq
  simpa only [decodeTable?_encodeTable_internal,
    Option.some.injEq] using hdecode

theorem decodeTable?_eq_none_iff_internal
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) (bits : List Bool) :
    decodeTable? coordinates bits = none ↔
      bits.length ≠ 2 ^ coordinates.card := by
  simp [decodeTable?]

end BooleanDependency

end Complexity
