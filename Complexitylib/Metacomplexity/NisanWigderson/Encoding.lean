/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Encoding.Defs
public import Complexitylib.Metacomplexity.NisanWigderson.Encoding.Internal

/-!
# Canonical codec for Nisan--Wigderson designs

The complete ordered coordinate table is encoded injectively using exactly
`outputLength * inputLength * clog_2(seedLength)` bits. The executable decoder
rejects malformed lengths, out-of-range coordinates, and noninjective blocks,
round-trips every valid design, and accepts only that design's canonical
encoding.
-/


public section

namespace Complexity

namespace NWDesign

/-- Canonical NW-design encoding has the exact rectangular coordinate-table
length. -/
@[simp] theorem length_encode
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength) :
    design.encode.length =
      outputLength * inputLength * Fin.bitWidth seedLength :=
  length_encode_internal design

/-- Canonical NW-design encoding is injective. -/
theorem encode_injective
    {outputLength inputLength seedLength : ℕ} :
    Function.Injective
      (encode : NWDesign outputLength inputLength seedLength → List Bool) :=
  encode_injective_internal

/-- Decoding one coordinate from an encoded design recovers it exactly. -/
@[simp] theorem decodeCoordinate?_encode
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (output : Fin outputLength) (input : Fin inputLength) :
    decodeCoordinate? outputLength inputLength seedLength design.encode
        output input =
      some (design.coordinates output input) :=
  decodeCoordinate?_encode_internal design output input

/-- The canonical NW-design decoder round-trips every valid design. -/
@[simp] theorem decode?_encode
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength) :
    decode? outputLength inputLength seedLength design.encode = some design :=
  decode?_encode_internal design

/-- The decoder rejects every string whose total length is malformed, including
when the design has no output or input coordinates. -/
theorem decode?_eq_none_of_length_ne
    (outputLength inputLength seedLength : ℕ) (bits : List Bool)
    (hlength : bits.length ≠
      outputLength * inputLength * Fin.bitWidth seedLength) :
    decode? outputLength inputLength seedLength bits = none :=
  decode?_eq_none_of_length_ne_internal outputLength inputLength seedLength bits
    hlength

/-- Decoding yields a given design exactly on its canonical encoding. -/
theorem decode?_eq_some_iff
    {outputLength inputLength seedLength : ℕ} (bits : List Bool)
    (design : NWDesign outputLength inputLength seedLength) :
    decode? outputLength inputLength seedLength bits = some design ↔
      bits = design.encode :=
  decode?_eq_some_iff_internal bits design

end NWDesign

end Complexity
