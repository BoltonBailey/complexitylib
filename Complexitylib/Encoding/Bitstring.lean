/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Complexitylib.Encoding.Delimit
import Mathlib.Computability.Encoding
import Mathlib.Data.PNat.Defs
import Mathlib.Algebra.Field.Rat

/-!
# Bitstring Encoding Typeclass

This file provides a typeclass-inferrable version of Mathlib's `Computability.Encoding`,
specialized to the alphabet `Bool`.

Making it a `class` makes it easier to quickly ask if a function is computable in polynomial
time, without having to explicitly pass around the encoding.

The idea of this class is to set up instances for common types like `Bool`, `ℕ`, `ℤ`, `ℚ`,
and instance derivations for product and list types, so that the resulting instance for any
common type will be polytime-transcodable with any other reasonable binary encoding of that
type.

Thus, while it may not be obvious without looking carefully which of several essentially
equivalent encodings of a type is being used, we can at least be sure that for functions
between types with `BitstringEncoding` instances, questions of polynomial-time computability
are well-defined, in the sense that the formalization will capture the intended meaning.

Multipartite data is concatenated out of *self-delimiting blocks*, framed by the single
delimiting operation `Complexity.delimit` from `Complexitylib.Encoding.Delimit` (each payload
bit doubled, terminated by the separator `[false, true]`) and parsed back by its `unpair?` —
the same framing underlying the machine-input pairing codec `Complexity.pair`
(`pair x y = delimit x ++ y`) of `Complexitylib.Encoding.Pairing`.

This layer is deliberately independent of the machine model. The type `Bitstring` below is
unrelated to the fixed-length `BitString n := Fin n → Bool` used by the circuit layers.
-/

namespace Complexity

/-- A canonical encoding of a type as bitstrings (`List Bool`).

This is a class version of Mathlib's (bundled) `Computability.Encoding`, specialized to the
alphabet `Bool`. -/
class BitstringEncoding (α : Type*) where
  /-- The encoding function. -/
  encode : α → List Bool
  /-- The decoding function; `none` on bitstrings that encode nothing. -/
  decode : List Bool → Option α
  /-- Decoding is a left inverse of encoding. -/
  decode_encode : ∀ x, decode (encode x) = some x

attribute [simp] BitstringEncoding.decode_encode

namespace BitstringEncoding

variable {α β : Type*}

theorem encode_injective [BitstringEncoding α] :
    Function.Injective (encode : α → List Bool) := fun _ _ h =>
  Option.some_injective _ (by rw [← decode_encode, ← decode_encode, h])

/-- Transport a `BitstringEncoding` along an injection `f` with partial inverse `g`. -/
@[reducible]
def ofLeftInverse [BitstringEncoding β] (f : α → β) (g : β → Option α)
    (h : ∀ x, g (f x) = some x) : BitstringEncoding α where
  encode a := encode (f a)
  decode l := (decode l).bind g
  decode_encode a := by simp [h]

/- ## Ground instances -/

/-- `ℕ` is encoded by its (little-endian) binary representation, as in
`Computability.encodeNat`. -/
instance : BitstringEncoding ℕ where
  encode := Computability.encodeNat
  decode l := some (Computability.decodeNat l)
  decode_encode n := congrArg some (Computability.decode_encodeNat n)

/-- `Bool` is encoded as a singleton bitstring. -/
instance : BitstringEncoding Bool where
  encode b := [b]
  decode l := match l with
    | [b] => some b
    | _ => none
  decode_encode _ := rfl

/-- `Unit` is encoded as the empty bitstring. This is the tensor unit for the pair encoding:
`encode ((), x) = false :: true :: encode x` and `encode (x, ()) = delimit (encode x)`. -/
instance : BitstringEncoding Unit where
  encode _ := []
  decode l := match l with
    | [] => some ()
    | _ => none
  decode_encode _ := rfl

/-- Decode every block in a list of bitstrings, failing if any block fails to decode.

(This is `List.mapM decode` in the `Option` monad, written out by hand so that it works
for `α` in any universe.) -/
def decodeAll [BitstringEncoding α] : List (List Bool) → Option (List α)
  | [] => some []
  | b :: t =>
    match decode b, decodeAll t with
    | some a, some l => some (a :: l)
    | _, _ => none

@[simp]
theorem decodeAll_map_encode [BitstringEncoding α] (l : List α) :
    decodeAll (l.map encode) = some l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [decodeAll, ih]

/- ## Derived instances -/

/-- An encoding of `Option α` is obtained encoding `none` as the empty bitstring
and `some a` as the encoding of `a` prefixed by a `true`. -/
instance [BitstringEncoding α] : BitstringEncoding (Option α) where
  encode
    | none => []
    | some a => true :: encode a
  decode input :=
    match input with
    | [] => some none
    | true :: rest => (decode rest).map some
    | false :: _ => none
  decode_encode
    | none => rfl
    | some a => by simp

/-- Decode a bitstring as a pair: parse one self-delimiting block off the front for the first
component, and decode the remainder as the second. This is the `decode` of the `α × β` instance,
given as a standalone definition so that it can be unfolded and reasoned about by name. -/
def decodePair [BitstringEncoding α] [BitstringEncoding β] (input : List Bool) :
    Option (α × β) :=
  match unpair? input with
  | none => none
  | some (block, rest) =>
    match decode block, decode rest with
    | some a, some b => some (a, b)
    | _, _ => none

/-- A pair is encoded as a self-delimiting block for the first component followed by the
encoding of the second — the same layout as the machine-input pairing codec
`Complexity.pair`. -/
instance [BitstringEncoding α] [BitstringEncoding β] : BitstringEncoding (α × β) where
  encode p := delimit (encode p.1) ++ encode p.2
  decode := decodePair
  decode_encode p := by simp [decodePair]

theorem decode_prod_eq_decodePair [BitstringEncoding α] [BitstringEncoding β] :
    (decode : List Bool → Option (α × β)) = decodePair := rfl

/-- A list is encoded as the concatenation of self-delimiting blocks for its elements. -/
instance [BitstringEncoding α] : BitstringEncoding (List α) where
  encode l := ((l.map encode).map delimit).flatten
  decode input :=
    match undelimitBlocks input with
    | none => none
    | some blocks => decodeAll blocks
  decode_encode l := by
    rw [undelimitBlocks_flatten_delimit (l.map encode)]
    exact decodeAll_map_encode l

/-- A subtype inherits the encoding of the ambient type; decoding additionally checks the
defining predicate. This yields encodings for `ℕ+` and friends for free. -/
instance {p : α → Prop} [BitstringEncoding α] [DecidablePred p] :
    BitstringEncoding (Subtype p) where
  encode x := encode x.val
  decode input := (decode input).bind fun a => if h : p a then some ⟨a, h⟩ else none
  decode_encode x := by simp [x.property]

/-- `ℕ+` is encoded as the subtype `{n : ℕ // 0 < n}` it is defined to be. -/
instance : BitstringEncoding ℕ+ :=
  inferInstanceAs (BitstringEncoding {n : ℕ // 0 < n})

/-- `ℤ` is encoded via the pair `(n.toNat, (-n).toNat)` (one component is always `0`). -/
instance : BitstringEncoding ℤ :=
  ofLeftInverse (fun n : ℤ => (n.toNat, (-n).toNat))
    (fun p => some ((p.1 : ℤ) - (p.2 : ℤ))) (fun n => congrArg some (by dsimp only; omega))

/-- `ℚ` is encoded as its (reduced) numerator-denominator pair. -/
instance : BitstringEncoding ℚ :=
  ofLeftInverse (fun q : ℚ => (q.num, q.den))
    (fun p => some ((p.1 : ℚ) / (p.2 : ℚ))) (fun q => by simp [Rat.num_div_den])

end BitstringEncoding

/-- A bitstring: definitionally `List Bool`, but kept as a distinct (semireducible) type-level
name so that it can carry the identity `BitstringEncoding` without overlapping the generic
`List α` instance.

Data that is conceptually a raw bitstring should be typed as `Bitstring`, and is encoded as
itself; a `List Bool` that is conceptually a list which happens to contain booleans keeps the
generic self-delimiting list encoding (four bits per element). Because `Bitstring` is not
reducible, instance search never sees through it, so the two encodings cannot be confused: a
lemma about the generic `List α` encoding instantiated at `α := Bool` and a lemma about
`Bitstring` can never silently disagree about which encoding is meant.

(Not to be confused with the fixed-length `BitString n := Fin n → Bool` of the circuit
layers.) -/
def Bitstring : Type := List Bool

/-- A bitstring is encoded as itself. -/
instance : BitstringEncoding Bitstring where
  encode := id
  decode := some
  decode_encode _ := rfl

/-- Convert a `List Bool` to a `Bitstring`. Definitionally the identity; useful for stating
lemmas that mix the two types without relying on definitional unfolding. -/
def Bitstring.ofList (l : List Bool) : Bitstring := l

/-- Convert a `Bitstring` to a `List Bool`. Definitionally the identity. -/
def Bitstring.toList (l : Bitstring) : List Bool := l

namespace BitstringEncoding

@[simp]
theorem encode_ofList (l : List Bool) : encode (Bitstring.ofList l) = l := rfl

theorem decode_bitstring (l : List Bool) :
    (decode l : Option Bitstring) = some (Bitstring.ofList l) := rfl

end BitstringEncoding

end Complexity
