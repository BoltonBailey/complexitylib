/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Defs
public import Complexitylib.Mathlib.NatBits

/-!
# Canonical encodings of Nisan--Wigderson designs -- definitions

Every coordinate of every ordered design block is encoded in the canonical
`clog_2(seedLength)`-bit `Fin` representation. A fixed lexicographic order on
output coordinate, input coordinate, and bit position turns the entire design
into one flat bit string.
-/


@[expose] public section

namespace Complexity

namespace NWDesign

/-- Index of one bit in the complete coordinate table of an NW design. -/
abbrev CoordinateBitIndex
    (outputLength inputLength seedLength : ℕ) :=
  (Fin outputLength × Fin inputLength) × Fin (Fin.bitWidth seedLength)

/-- Row-major equivalence between coordinate-bit table indices and flat bit
positions. -/
def coordinateBitIndexEquiv
    (outputLength inputLength seedLength : ℕ) :
    CoordinateBitIndex outputLength inputLength seedLength ≃
      Fin (outputLength * inputLength * Fin.bitWidth seedLength) :=
  (Equiv.prodCongr finProdFinEquiv (Equiv.refl _)).trans finProdFinEquiv

/-- Boolean table underlying the canonical NW-design encoding. -/
def coordinateBitTable
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength) :
    CoordinateBitIndex outputLength inputLength seedLength → Bool :=
  fun ((output, input), bit) =>
    (design.coordinates output input).toBits.get
      ⟨bit.val, by
        rw [Fin.length_toBits]
        exact bit.isLt⟩

/-- Canonical flat encoding of every coordinate in every ordered design block. -/
def encode {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength) : List Bool :=
  List.ofFn fun position =>
    design.coordinateBitTable
      ((coordinateBitIndexEquiv outputLength inputLength seedLength).symm
        position)

/-- Decode the fixed-width coordinate at one output/input position of an encoded
design. A malformed total length or an out-of-range coordinate is rejected. -/
def decodeCoordinate?
    (outputLength inputLength seedLength : ℕ) (bits : List Bool)
    (output : Fin outputLength) (input : Fin inputLength) :
    Option (Fin seedLength) :=
  if hlength : bits.length =
      outputLength * inputLength * Fin.bitWidth seedLength then
    Fin.fromBits? seedLength <| List.ofFn fun bit =>
      bits.get
        ⟨(coordinateBitIndexEquiv outputLength inputLength seedLength
          ((output, input), bit)).val, by
            rw [hlength]
            exact (coordinateBitIndexEquiv outputLength inputLength
              seedLength ((output, input), bit)).isLt⟩
  else
    none

/-- Total coordinate table extracted from bits whose every coordinate decodes.
The proof is erased from executable code. -/
def decodedCoordinates
    (outputLength inputLength seedLength : ℕ) (bits : List Bool)
    (hvalid : ∀ output input,
      (decodeCoordinate? outputLength inputLength seedLength bits output input).isSome) :
    Fin outputLength → Fin inputLength → Fin seedLength :=
  fun output input =>
    (decodeCoordinate? outputLength inputLength seedLength bits output input).get
      (hvalid output input)

/-- Decode a canonical NW-design bit string. Besides length and coordinate-range
checks, this rejects any block whose decoded coordinate map is not injective. -/
def decode?
    (outputLength inputLength seedLength : ℕ) (bits : List Bool) :
    Option (NWDesign outputLength inputLength seedLength) :=
  if _hlength : bits.length =
      outputLength * inputLength * Fin.bitWidth seedLength then
    if hvalid : ∀ output input,
        (decodeCoordinate? outputLength inputLength seedLength bits output input).isSome then
      let coordinates :=
        decodedCoordinates outputLength inputLength seedLength bits hvalid
      if hinjective : ∀ output, Function.Injective (coordinates output) then
        some ⟨fun output => ⟨coordinates output, hinjective output⟩⟩
      else
        none
    else
      none
  else
    none

end NWDesign

end Complexity
