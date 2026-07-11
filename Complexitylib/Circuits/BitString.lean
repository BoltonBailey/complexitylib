/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.Basic
import Mathlib.Data.List.OfFn

/-!
# Fixed-length bit strings and lists

Circuits consume fixed-length functions `BitString n = Fin n → Bool`, while
machine languages consume `List Bool`. This module makes `List.ofFn` the
canonical serialization and provides round-trip lemmas in both directions.

The variable-length equivalence is already available from Mathlib as
`List.equivSigmaTuple : List Bool ≃ Σ n, BitString n`.
-/

namespace Complexity

namespace BitString

/-- Serialize a fixed-length bit string in increasing index order. -/
def toList (x : BitString n) : List Bool :=
  List.ofFn x

/-- Read a list of the specified length as a fixed-length bit string. -/
def ofList (xs : List Bool) {n : ℕ} (h : xs.length = n) : BitString n :=
  fun i => xs.get (Fin.cast h.symm i)

/-- Serialization preserves length: `toList` of an `n`-bit string has length `n`. -/
@[simp] theorem length_toList (x : BitString n) : x.toList.length = n := by
  simp [toList]

/-- Indexing into the serialized list agrees with the original bit string: `x.toList[i] = x i`. -/
@[simp] theorem getElem_toList (x : BitString n) (i : Fin n) :
    x.toList[i.val]'(by rw [length_toList]; exact i.isLt) = x i := by
  simp [toList]

/-- Round trip, list side: serializing `ofList xs h` recovers the original list `xs`. -/
@[simp] theorem toList_ofList (xs : List Bool) {n : ℕ} (h : xs.length = n) :
    toList (ofList xs h) = xs := by
  subst n
  simpa only [toList, ofList, Fin.cast_refl] using List.ofFn_get xs

/-- Round trip, bit-string side: deserializing `toList x` recovers the original bit string `x`. -/
@[simp] theorem ofList_toList (x : BitString n) :
    ofList (toList x) (length_toList x) = x := by
  funext i
  simp [ofList, toList]

/-- Serialization is injective: two bit strings have equal `toList` iff they are equal. -/
@[simp] theorem toList_inj {x y : BitString n} : x.toList = y.toList ↔ x = y :=
  List.ofFn_inj

/-- Serialization commutes with pointwise maps: `toList (f ∘ x) = x.toList.map f`. -/
@[simp] theorem toList_map (f : Bool → Bool) (x : BitString n) :
    toList (fun i => f (x i)) = x.toList.map f :=
  List.ofFn_comp' x f

/-- Serialization sends `Fin.append` to list append: `toList (x ++ y) = x.toList ++ y.toList`. -/
@[simp] theorem toList_append (x : BitString m) (y : BitString n) :
    toList (Fin.append x y) = x.toList ++ y.toList := by
  change List.ofFn (Fin.append x y) = List.ofFn x ++ List.ofFn y
  exact List.ofFn_fin_append x y

end BitString

end Complexity
