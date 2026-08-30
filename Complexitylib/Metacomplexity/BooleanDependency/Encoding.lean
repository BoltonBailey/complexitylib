/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.BooleanDependency.Encoding.Defs
public import Complexitylib.Metacomplexity.BooleanDependency.Encoding.Internal

/-!
# Canonical encoding of finite Boolean assignments and tables

This module exposes computable exact-length codecs for Boolean functions on
finite ordered domains, assignments on ordered finite coordinate sets, and
their full Boolean truth tables.
-/


public section

namespace Complexity

namespace BooleanDependency

/-- There are exactly `2^|S|` canonically ordered assignments to `S`. -/
theorem OrderedAssignment.card
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) :
    Fintype.card (OrderedAssignment coordinates) = 2 ^ coordinates.card :=
  OrderedAssignment.card_internal coordinates

/-- Ordered finite-function encodings contain exactly one bit per input. -/
@[simp] theorem length_encodeOrderedFunction
    {index : Type*} [Fintype index] [LinearOrder index]
    (function : index → Bool) :
    (encodeOrderedFunction function).length = Fintype.card index :=
  length_encodeOrderedFunction_internal function

/-- Exact round trip for Boolean functions on finite ordered domains. -/
@[simp] theorem decodeOrderedFunction?_encodeOrderedFunction
    {index : Type*} [Fintype index] [LinearOrder index]
    (function : index → Bool) :
    decodeOrderedFunction? (encodeOrderedFunction function) = some function :=
  decodeOrderedFunction?_encodeOrderedFunction_internal function

/-- Canonical ordered finite-function encoding is injective. -/
theorem encodeOrderedFunction_injective
    {index : Type*} [Fintype index] [LinearOrder index] :
    Function.Injective
      (encodeOrderedFunction : (index → Bool) → List Bool) :=
  encodeOrderedFunction_injective_internal

/-- Ordered finite-function decoding fails exactly on malformed lengths. -/
@[simp] theorem decodeOrderedFunction?_eq_none_iff
    {index : Type*} [Fintype index] [LinearOrder index]
    (bits : List Bool) :
    decodeOrderedFunction? (index := index) bits = none ↔
      bits.length ≠ Fintype.card index :=
  decodeOrderedFunction?_eq_none_iff_internal bits

/-- Assignment encodings contain exactly one bit per selected coordinate. -/
@[simp] theorem length_encodeAssignment
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) (assignment : coordinates → Bool) :
    (encodeAssignment coordinates assignment).length = coordinates.card :=
  length_encodeAssignment_internal coordinates assignment

/-- Exact assignment-codec round trip. -/
@[simp] theorem decodeAssignment?_encodeAssignment
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) (assignment : coordinates → Bool) :
    decodeAssignment? coordinates (encodeAssignment coordinates assignment) =
      some assignment :=
  decodeAssignment?_encodeAssignment_internal coordinates assignment

/-- Canonical assignment encoding is injective. -/
theorem encodeAssignment_injective
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) :
    Function.Injective (encodeAssignment coordinates) :=
  encodeAssignment_injective_internal coordinates

/-- Assignment decoding fails exactly on strings of the wrong length. -/
@[simp] theorem decodeAssignment?_eq_none_iff
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) (bits : List Bool) :
    decodeAssignment? coordinates bits = none ↔
      bits.length ≠ coordinates.card :=
  decodeAssignment?_eq_none_iff_internal coordinates bits

/-- A full Boolean table has exactly `2^|S|` serialized entries. -/
@[simp] theorem length_encodeTable
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate)
    (table : (coordinates → Bool) → Bool) :
    (encodeTable coordinates table).length = 2 ^ coordinates.card :=
  length_encodeTable_internal coordinates table

/-- Exact dependency-table-codec round trip. -/
@[simp] theorem decodeTable?_encodeTable
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate)
    (table : (coordinates → Bool) → Bool) :
    decodeTable? coordinates (encodeTable coordinates table) = some table :=
  decodeTable?_encodeTable_internal coordinates table

/-- Canonical dependency-table encoding is injective. -/
theorem encodeTable_injective
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) :
    Function.Injective (encodeTable coordinates) :=
  encodeTable_injective_internal coordinates

/-- Table decoding fails exactly on strings without one bit per assignment. -/
@[simp] theorem decodeTable?_eq_none_iff
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) (bits : List Bool) :
    decodeTable? coordinates bits = none ↔
      bits.length ≠ 2 ^ coordinates.card :=
  decodeTable?_eq_none_iff_internal coordinates bits

end BooleanDependency

end Complexity
