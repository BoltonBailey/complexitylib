/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Codec.Defs
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Padded.Defs
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Sequence.Defs

/-!
# Sequential fixed-width evaluation semantics -- definitions

This module defines the paired result invariant used to compare a compiled
encoded-evaluation prefix with direct evaluation of the same padded raw-gate
prefix. The compiled memo includes the description code and formula-internal
wires; the raw memo contains only sample inputs and one value per gate slot.
-/


@[expose] public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace Description

namespace EvaluationSequence

open EvaluationLayout

/-- Lift an index in a bounded prefix to the full fixed slot array. -/
def prefixSlot {gateBound count : Nat} (hcount : count ≤ gateBound)
    (slot : Fin count) : Fin gateBound :=
  ⟨slot.val, lt_of_lt_of_le slot.isLt hcount⟩

/-- Description code followed by one sample input. -/
def combinedInput {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound)
    (input : BitString inputWidth) :
    BitString (baseWireCount inputWidth gateBound) :=
  Fin.append (Description.encode description) input

/-- Initial memo array for encoded evaluation. -/
def inputWires {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound)
    (input : BitString inputWidth) : Array Bool :=
  Array.ofFn (combinedInput description input)

/-- First `count` gates of the padded direct-semantics circuit. -/
def rawPrefix {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound)
    (count : Nat) : RawCircuit :=
  description.toPaddedRawCircuit.take count

/-- Paired successful evaluation of one compiled prefix and its direct raw
semantics, including the memo correspondence at every emitted slot output. -/
structure PrefixResult {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound)
    (input : BitString inputWidth) (count : Nat)
    (hcount : count ≤ gateBound) where
  /-- Memo after the compiled encoded-evaluation prefix. -/
  circuitWires : Array Bool
  /-- Memo after the direct padded raw-gate prefix. -/
  rawWires : Array Bool
  /-- Successful compiled-prefix evaluation. -/
  circuitEval :
    RawCircuit.evalAux? (prefixCircuit inputWidth gateBound count)
        (inputWires description input) = some circuitWires
  /-- Successful direct raw-prefix evaluation. -/
  rawEval :
    RawCircuit.evalAux? (rawPrefix description count)
        (Array.ofFn input) = some rawWires
  /-- Exact compiled memo size. -/
  circuitSize :
    circuitWires.size =
      baseWireCount inputWidth gateBound +
        prefixSize inputWidth gateBound count
  /-- Exact direct raw memo size. -/
  rawSize : rawWires.size = inputWidth + count
  /-- The compiled evaluator preserves its description-and-input prefix. -/
  inputPreserved : ∀ wire < baseWireCount inputWidth gateBound,
    circuitWires[wire]? = (inputWires description input)[wire]?
  /-- Every compiled slot output equals the corresponding direct raw memo. -/
  outputs : ∀ slot : Fin count,
    circuitWires[stepOutputWire inputWidth gateBound
        (prefixSlot hcount slot)]? =
      rawWires[inputWidth + slot.val]?

end EvaluationSequence

end Description

end FixedWidth

end CircuitCode

end Complexity
