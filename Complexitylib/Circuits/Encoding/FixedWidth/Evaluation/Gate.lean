/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Gate.Defs
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Gate.Internal

/-!
# Fixed-width encoded-gate evaluation formulas

This module exposes the exact semantics, tree size, and support of the formula
that evaluates one gate slot in a fixed-width circuit description.
-/


public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace Description

namespace GateFormula

/-- Conditional formula negation agrees with Boolean XOR. -/
@[simp] theorem eval_negateIf (flag value : BoolFormula)
    (assignment : Nat → Bool) :
    (negateIf flag value).eval assignment =
      (flag.eval assignment).xor (value.eval assignment) :=
  eval_negateIf_internal flag value assignment

/-- The compact conditional-negation formula has its exact tree size. -/
@[simp] theorem size_negateIf (flag value : BoolFormula) :
    (negateIf flag value).size =
      2 * flag.size + 2 * value.size + 4 :=
  size_negateIf_internal flag value

/-- The operation formula follows the fixed-width true-AND, false-OR
convention. -/
@[simp] theorem eval_applyOperation (operation left right : BoolFormula)
    (assignment : Nat → Bool) :
    (applyOperation operation left right).eval assignment =
      match operation.eval assignment with
      | true => left.eval assignment && right.eval assignment
      | false => left.eval assignment || right.eval assignment :=
  eval_applyOperation_internal operation left right assignment

/-- The compact operation-selection formula has its exact tree size. -/
@[simp] theorem size_applyOperation (operation left right : BoolFormula) :
    (applyOperation operation left right).size =
      operation.size + 2 * left.size + 2 * right.size + 5 :=
  size_applyOperation_internal operation left right

/-- Under the slot's backward-reference invariant, the encoded-gate formula
agrees exactly with the raw gate selected by the assignment's code prefix. -/
theorem eval_gate {inputWidth gateBound : Nat}
    (slot : Fin gateBound)
    (sources : Fin (inputWidth + slot.val) → BoolFormula)
    (assignment : Nat → Bool)
    (hslot :
      (decodedSlot inputWidth gateBound slot assignment).WellFormedAt
        (inputWidth + slot.val)) :
    (gate inputWidth gateBound slot sources).eval assignment =
      (decodedSlot inputWidth gateBound slot assignment).toRawGate.eval
        ((sources ⟨(decodedSlot inputWidth gateBound slot assignment).input0Value,
          hslot.1⟩).eval assignment)
        ((sources ⟨(decodedSlot inputWidth gateBound slot assignment).input1Value,
          hslot.2⟩).eval assignment) :=
  eval_gate_internal slot sources assignment hslot

/-- Exact encoded-gate formula size for one-node source formulas. -/
@[simp] theorem size_gate {inputWidth gateBound : Nat}
    (slot : Fin gateBound)
    (sources : Fin (inputWidth + slot.val) → BoolFormula)
    (hsources : ∀ source, (sources source).size = 1) :
    (gate inputWidth gateBound slot sources).size =
      gateSize inputWidth gateBound slot :=
  size_gate_internal slot sources hsources

/-- The gate formula only references its code prefix and declared sources. -/
theorem vars_gate_lt {inputWidth gateBound available : Nat}
    (slot : Fin gateBound)
    (sources : Fin (inputWidth + slot.val) → BoolFormula)
    (hcode : codeWidth inputWidth gateBound ≤ available)
    (hsources : ∀ source wire,
      wire ∈ (sources source).vars → wire < available) :
    ∀ wire ∈ (gate inputWidth gateBound slot sources).vars,
      wire < available :=
  vars_gate_lt_internal slot sources hcode hsources

end GateFormula

end Description

end FixedWidth

end CircuitCode

end Complexity
