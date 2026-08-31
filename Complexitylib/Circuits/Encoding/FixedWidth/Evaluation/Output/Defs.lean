/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Sequence.Semantics.Defs
public import Complexitylib.Circuits.Encoding.FixedWidth.Lookup.Defs
public import Complexitylib.Circuits.Encoding.FixedWidth.Validity.Defs

/-!
# Fixed-width evaluator output selection -- definitions

The complete bounded evaluator emits one value for every gate slot. The active
gate count is therefore used as a one-based lookup index: zero selects a dummy
false source, while count `k + 1` selects the output of slot `k`.
-/


@[expose] public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace Description

namespace EvaluationOutput

open EvaluationLayout

/-- Number of wires available after evaluating every bounded gate slot. -/
def fullAvailable (inputWidth gateBound : Nat) : Nat :=
  baseWireCount inputWidth gateBound +
    prefixSize inputWidth gateBound gateBound

/-- Formula word naming the encoded active-gate count. -/
def countWord (inputWidth gateBound : Nat) :
    Fin (gateCountWidth gateBound) → BoolFormula :=
  ValidityFormula.countBit inputWidth gateBound

/-- One-based output table: zero is a dummy value and `k + 1` names slot `k`. -/
def sources (inputWidth gateBound : Nat) :
    Fin (gateBound + 1) → BoolFormula :=
  Fin.cases .fls fun slot =>
    .var (stepOutputWire inputWidth gateBound slot)

/-- Formula selecting the last active gate from the complete bounded sequence. -/
def formula (inputWidth gateBound : Nat) : BoolFormula :=
  LookupFormula.select
    (countWord inputWidth gateBound)
    (sources inputWidth gateBound)

/-- Exact tree size of the output-selector formula. -/
def selectorSize (gateBound : Nat) : Nat :=
  LookupFormula.selectSize (gateCountWidth gateBound) (gateBound + 1)

/-- Compile the output selector after the complete bounded gate sequence. -/
def compileRaw (inputWidth gateBound : Nat) : RawCircuit :=
  BoolFormula.compileRaw (fullAvailable inputWidth gateBound)
    (formula inputWidth gateBound)

/-- Absolute wire carrying the compiled selector result. -/
def outputWire (inputWidth gateBound : Nat) : Nat :=
  BoolFormula.rawOutputWire (fullAvailable inputWidth gateBound)
    (formula inputWidth gateBound)

/-- Total Boolean assignment read from an evaluated memo array. -/
def memoAssignment (wires : Array Bool) : Nat → Bool :=
  fun wire => (wires[wire]?).getD false

/-- Slot immediately preceding a positive active-gate count. -/
def lastActiveSlot {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound)
    (hpositive : description.Positive) : Fin gateBound :=
  ⟨description.gateCountNat - 1, by
    have hcount := description.gateCount.isLt
    change description.gateCountNat < gateBound + 1 at hcount
    change 0 < description.gateCountNat at hpositive
    omega⟩

end EvaluationOutput

end Description

end FixedWidth

end CircuitCode

end Complexity
