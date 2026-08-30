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
