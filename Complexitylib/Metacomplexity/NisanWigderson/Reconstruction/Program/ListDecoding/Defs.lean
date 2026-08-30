/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.ListDecoding.Defs
public import Complexitylib.Metacomplexity.Kolmogorov.Defs
public import Complexitylib.Metacomplexity.Kolmogorov.Oracle.Defs
public import Complexitylib.Metacomplexity.StatisticalTest.Oracle.Defs
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.Encoding.Defs

/-!
# List decoding explicit NW reconstruction programs -- definitions

An explicit reconstruction program approximating an encoded message can be
fed directly to the code's list decoder. Besides the finite candidate set,
this module defines the complete bitstring decoder, bounded decoded
certificates, and the machine-realization interface used to obtain a
machine-relative time-bounded Kolmogorov bound.
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

/-- Decode a complete indexed-program bit string and run its semantic source
message decoder. The ambient design, list code, and statistical test are fixed
parameters rather than hidden program fields. -/
def decodeIndexedMessage?
    {messageLength listSize outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (code : BooleanListCode messageLength listSize (Fin inputLength → Bool))
    (test : Finset (Fin outputLength → Bool)) (bits : List Bool) :
    Option (Fin messageLength → Bool) :=
  match decodeIndexedReconstructionProgram? design listSize bits with
  | some program => some (program.decodedMessage code test)
  | none => none

/-- A literal bitstring description, bounded in length, that the fixed indexed
reconstruction decoder maps to a source message. -/
def HasEncodedMessageCertificateWithin
    {messageLength listSize outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (code : BooleanListCode messageLength listSize (Fin inputLength → Bool))
    (test : Finset (Fin outputLength → Bool))
    (message : Fin messageLength → Bool) (bound : ℕ) : Prop :=
  ∃ description : List Bool,
    decodeIndexedMessage? design code test description = some message ∧
      description.length ≤ bound

/-- A deterministic machine realizing the fixed indexed-message decoder. The
clock depends on description length and is monotone so a length bound yields a
single common time budget. -/
structure EncodedMessageDecoderRealization
    {messageLength listSize outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (code : BooleanListCode messageLength listSize (Fin inputLength → Bool))
    (test : Finset (Fin outputLength → Bool)) where
  /-- Number of work tapes used by the decoder machine. -/
  tapes : ℕ
  /-- Machine interpreting complete indexed reconstruction descriptions. -/
  machine : TM tapes
  /-- Decoder time as a function of description length. -/
  time : ℕ → ℕ
  /-- Larger descriptions receive no smaller clock. -/
  time_mono : Monotone time
  /-- Every semantically decoded message is produced by the machine within the
  advertised clock. -/
  correct : ∀ description message,
    decodeIndexedMessage? design code test description = some message →
      machine.ProducesInTime description (List.ofFn message)
        (time description.length)

/-- One oracle machine realizing the indexed-message decoder for every finite
statistical test. The design and list code remain fixed machine parameters,
but the test is supplied through its canonical Boolean oracle and therefore
does not occupy program bits. -/
structure OracleEncodedMessageDecoderRealization
    {messageLength listSize outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (code : BooleanListCode messageLength listSize (Fin inputLength → Bool)) where
  /-- Number of ordinary work tapes used in addition to the query tape. -/
  tapes : ℕ
  /-- Oracle machine interpreting complete indexed reconstruction programs. -/
  machine : OracleTM tapes
  /-- Decoder time as a function of program length. -/
  time : ℕ → ℕ
  /-- Larger descriptions receive no smaller clock. -/
  time_mono : Monotone time
  /-- Correctness for every finite test supplied through
  `finiteTestOracle`. -/
  correct : ∀ (test : Finset (Fin outputLength → Bool)) description message,
    decodeIndexedMessage? design code test description = some message →
      machine.ProducesInTime (finiteTestOracle test) description
        (List.ofFn message) (time description.length)

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
