/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.ListDecoding.Defs
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.Encoding.Defs

/-!
# List decoding explicit NW reconstruction programs -- definitions

An explicit reconstruction program approximating an encoded message can be
fed directly to the code's list decoder. This module names the resulting
finite candidate set before proving that sufficient reconstruction agreement
places the original message inside it.
-/


@[expose] public section

namespace Complexity

namespace NWDesign

/-- An explicit NW reconstruction program together with one indexed output of
a list decoder. -/
structure IndexedReconstructionProgram
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (listSize : ℕ) where
  /-- The oracle-free Boolean predictor materialized from reconstruction
  advice. -/
  reconstruction : design.ReconstructionProgram
  /-- Which one of the list decoder's indexed outputs to select. -/
  decoderIndex : Fin listSize

namespace IndexedReconstructionProgram

/-- Source message selected by an indexed reconstruction program. -/
def decodedMessage
    {messageLength listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : IndexedReconstructionProgram design listSize)
    (code : BooleanListCode messageLength listSize (Fin inputLength → Bool))
    (test : Finset (Fin outputLength → Bool)) : Fin messageLength → Bool :=
  code.decode (program.reconstruction.predictor test) program.decoderIndex

/-- Flat Boolean data stored by an indexed reconstruction program. The
polarity and hybrid coordinate remain external codec metadata. -/
def encodeBooleanPayload
    {listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : IndexedReconstructionProgram design listSize) : List Bool :=
  program.reconstruction.encodeBooleanPayload ++
    BooleanListCode.encodeDecoderIndex program.decoderIndex

/-- Complete encoding of an indexed reconstruction program: polarity,
hybrid coordinate, reconstruction data, and list-decoder index. Only ambient
parameters remain external. -/
def encode
    {listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : IndexedReconstructionProgram design listSize) : List Bool :=
  program.reconstruction.complement ::
    program.reconstruction.current.toBits ++ program.encodeBooleanPayload

end IndexedReconstructionProgram

/-- Decode the Boolean payload of an indexed reconstruction program using an
externally supplied polarity and hybrid coordinate. -/
def decodeIndexedReconstructionBooleanPayload?
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength) (listSize : ℕ)
    (complement : Bool) (current : Fin outputLength) (bits : List Bool) :
    Option (IndexedReconstructionProgram design listSize) :=
  let payloadLength := design.reconstructionDataBitsAt current
  let programBits := bits.take payloadLength
  let indexBits := bits.drop payloadLength
  match decodeReconstructionBooleanPayload? design complement current programBits,
      BooleanListCode.decodeDecoderIndex? listSize indexBits with
  | some reconstruction, some decoderIndex =>
      some { reconstruction, decoderIndex }
  | _, _ => none

/-- Decode a complete indexed reconstruction program relative to its ambient
design and list-size parameters. -/
def decodeIndexedReconstructionProgram?
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength) (listSize : ℕ)
    (bits : List Bool) : Option (IndexedReconstructionProgram design listSize) :=
  match bits with
  | [] => none
  | complement :: body =>
      let coordinateWidth := Fin.bitWidth outputLength
      match Fin.fromBits? outputLength (body.take coordinateWidth) with
      | none => none
      | some current =>
          decodeIndexedReconstructionBooleanPayload? design listSize
            complement current (body.drop coordinateWidth)

namespace ReconstructionProgram

/-- Candidate source messages obtained by list decoding the Boolean predictor
stored in an explicit reconstruction program. -/
def listDecoderCandidates
    {messageLength listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram)
    (code : BooleanListCode messageLength listSize (Fin inputLength → Bool))
    (test : Finset (Fin outputLength → Bool)) :
    Finset (Fin messageLength → Bool) :=
  code.candidates (program.predictor test)

end ReconstructionProgram

end NWDesign

end Complexity
