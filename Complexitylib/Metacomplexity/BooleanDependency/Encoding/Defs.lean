/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Batteries.Data.BitVec.Lemmas
public import Complexitylib.Metacomplexity.BooleanDependency.Defs
public import Mathlib.Data.Finset.Sort

/-!
# Canonical encoding of finite Boolean assignments and tables -- definitions

Coordinates are listed in their linear order. Boolean assignments to `k`
coordinates are then indexed by the corresponding little-endian `k`-bit
vector, giving a computable equivalence with `Fin (2^k)`. This fixes a canonical
order for serializing arbitrary Boolean dependency tables.
-/


@[expose] public section

namespace Complexity

namespace BooleanDependency

/-- Computable little-endian indexing of all Boolean assignments to an ordered
finite coordinate set. -/
def assignmentIndexEquiv {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) :
    (coordinates → Bool) ≃ Fin (2 ^ coordinates.card) where
  toFun assignment :=
    (BitVec.ofFnLE fun position =>
      assignment (coordinates.orderIsoOfFin rfl position)).toFin
  invFun index := fun coordinate =>
    (BitVec.ofFin index).getLsb
      ((coordinates.orderIsoOfFin rfl).symm coordinate)
  left_inv assignment := by
    funext coordinate
    simp
  right_inv index := by
    apply Fin.ext
    simp [Fin.ofBits, Nat.ofBits_testBit, Nat.mod_eq_of_lt index.isLt]

/-- Boolean assignments equipped with their canonical little-endian order. -/
structure OrderedAssignment {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) where
  /-- Underlying assignment. -/
  toFun : coordinates → Bool

namespace OrderedAssignment

instance {coordinate : Type*} [LinearOrder coordinate]
    {coordinates : Finset coordinate} :
    CoeFun (OrderedAssignment coordinates) (fun _ => coordinates → Bool) :=
  ⟨toFun⟩

/-- Ordered assignments are canonically equivalent to their little-endian
indices. -/
def indexEquiv {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) :
    OrderedAssignment coordinates ≃ Fin (2 ^ coordinates.card) where
  toFun assignment := assignmentIndexEquiv coordinates assignment.toFun
  invFun index := ⟨(assignmentIndexEquiv coordinates).symm index⟩
  left_inv assignment := by cases assignment; simp
  right_inv index := by simp

instance {coordinate : Type*} [LinearOrder coordinate]
    {coordinates : Finset coordinate} :
    DecidableEq (OrderedAssignment coordinates) :=
  (indexEquiv coordinates).decidableEq

instance {coordinate : Type*} [LinearOrder coordinate]
    {coordinates : Finset coordinate} :
    Fintype (OrderedAssignment coordinates) :=
  Fintype.ofEquiv (Fin (2 ^ coordinates.card))
    (indexEquiv coordinates).symm

instance {coordinate : Type*} [LinearOrder coordinate]
    {coordinates : Finset coordinate} :
    LinearOrder (OrderedAssignment coordinates) :=
  (indexEquiv coordinates).linearOrder

end OrderedAssignment

/-- Encode a Boolean function on any finite linearly ordered domain. -/
def encodeOrderedFunction {index : Type*} [Fintype index] [LinearOrder index]
    (function : index → Bool) : List Bool :=
  List.ofFn fun position : Fin (Fintype.card index) =>
    function (Fintype.orderIsoFinOfCardEq index rfl position)

/-- Decode a Boolean function on a finite linearly ordered domain only from a
bit string with exactly one entry per domain element. -/
def decodeOrderedFunction? {index : Type*} [Fintype index] [LinearOrder index]
    (bits : List Bool) : Option (index → Bool) :=
  if hlength : bits.length = Fintype.card index then
    some fun input =>
      let position := (Fintype.orderIsoFinOfCardEq index rfl).symm input
      bits.get ⟨position.val, by rw [hlength]; exact position.isLt⟩
  else
    none

/-- Encode one assignment by listing its coordinate values in increasing
coordinate order. -/
def encodeAssignment {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) (assignment : coordinates → Bool) :
    List Bool :=
  List.ofFn fun position : Fin coordinates.card =>
    assignment (coordinates.orderIsoOfFin rfl position)

/-- Decode an assignment only from a bit string of the exact required length. -/
def decodeAssignment? {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) (bits : List Bool) :
    Option (coordinates → Bool) :=
  if hlength : bits.length = coordinates.card then
    some fun coordinate =>
      let position := (coordinates.orderIsoOfFin rfl).symm coordinate
      bits.get ⟨position.val, by rw [hlength]; exact position.isLt⟩
  else
    none

/-- Serialize a Boolean table in the canonical little-endian assignment
order. -/
def encodeTable {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate)
    (table : (coordinates → Bool) → Bool) : List Bool :=
  List.ofFn fun index : Fin (2 ^ coordinates.card) =>
    table ((assignmentIndexEquiv coordinates).symm index)

/-- Decode a Boolean table only from a bit string with exactly one entry for
every assignment. -/
def decodeTable? {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) (bits : List Bool) :
    Option ((coordinates → Bool) → Bool) :=
  if hlength : bits.length = 2 ^ coordinates.card then
    some fun assignment =>
      let index := assignmentIndexEquiv coordinates assignment
      bits.get ⟨index.val, by rw [hlength]; exact index.isLt⟩
  else
    none

end BooleanDependency

end Complexity
