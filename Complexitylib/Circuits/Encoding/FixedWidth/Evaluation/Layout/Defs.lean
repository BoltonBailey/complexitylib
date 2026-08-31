/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Gate.Defs

/-!
# Sequential fixed-width evaluator wire layout -- definitions

The evaluator receives a description code followed by one sample input. It
then compiles one formula fragment per bounded gate slot. This module assigns
absolute wires to primary inputs and earlier gate results without yet building
or executing the concatenated raw circuit.

The numeric prefix schedule depends only on the public exact gate-formula size,
so later compilation and streaming constructions share one wire layout.
-/


@[expose] public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace Description

namespace EvaluationLayout

/-- Number of incoming wires: description code followed by one sample input. -/
def baseWireCount (inputWidth gateBound : Nat) : Nat :=
  codeWidth inputWidth gateBound + inputWidth

/-- Gate-formula size at a natural slot index, with zero outside the bound. -/
def sizeAt (inputWidth gateBound index : Nat) : Nat :=
  if hindex : index < gateBound then
    GateFormula.gateSize inputWidth gateBound ⟨index, hindex⟩
  else
    0

/-- Total gate-formula size of the first `count` slots. -/
def prefixSize (inputWidth gateBound : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 =>
      prefixSize inputWidth gateBound count +
        sizeAt inputWidth gateBound count

/-- Number of wires available before compiling one gate-slot formula. -/
def stepAvailable (inputWidth gateBound : Nat)
    (slot : Fin gateBound) : Nat :=
  baseWireCount inputWidth gateBound +
    prefixSize inputWidth gateBound slot.val

/-- Absolute output wire assigned to one compiled gate-slot formula. -/
def stepOutputWire (inputWidth gateBound : Nat)
    (slot : Fin gateBound) : Nat :=
  stepAvailable inputWidth gateBound slot +
    GateFormula.gateSize inputWidth gateBound slot - 1

/-- Lift a prior local gate index to the global bounded slot type. -/
def earlierSlot {gateBound : Nat} (slot : Fin gateBound)
    (earlier : Fin slot.val) : Fin gateBound :=
  ⟨earlier.val, lt_trans earlier.isLt slot.isLt⟩

/-- One-node formulas naming the primary inputs and earlier gate results
available to a particular gate slot. -/
def sourceFormula (inputWidth gateBound : Nat) (slot : Fin gateBound) :
    Fin (inputWidth + slot.val) → BoolFormula :=
  Fin.addCases
    (fun input : Fin inputWidth =>
      .var (codeWidth inputWidth gateBound + input.val))
    (fun earlier : Fin slot.val =>
      .var (stepOutputWire inputWidth gateBound
        (earlierSlot slot earlier)))

/-- Formula computing one sequentially laid-out encoded gate slot. -/
def stepFormula (inputWidth gateBound : Nat)
    (slot : Fin gateBound) : BoolFormula :=
  GateFormula.gate inputWidth gateBound slot
    (sourceFormula inputWidth gateBound slot)

end EvaluationLayout

end Description

end FixedWidth

end CircuitCode

end Complexity
