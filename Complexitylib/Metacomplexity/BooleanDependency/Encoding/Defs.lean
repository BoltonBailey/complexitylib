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
