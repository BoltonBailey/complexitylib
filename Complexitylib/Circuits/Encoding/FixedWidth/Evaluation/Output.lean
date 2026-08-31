/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Output.Defs
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Output.Internal

/-!
# Fixed-width evaluator output selection

The compiled selector is scoped to the completed gate-sequence memo. On an
encoded positive description it returns exactly the last active gate value,
which the sequence invariant identifies with the corresponding direct raw-gate
memo entry.
-/


public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace Description

namespace EvaluationOutput

open EvaluationLayout

/-- Every bounded gate result is available before output selection begins. -/
theorem stepOutputWire_lt_fullAvailable
    {inputWidth gateBound : Nat} (slot : Fin gateBound) :
    stepOutputWire inputWidth gateBound slot <
      fullAvailable inputWidth gateBound :=
  stepOutputWire_lt_fullAvailable_internal slot

/-- Exact size of the last-active-gate selector formula. -/
@[simp] theorem size_formula (inputWidth gateBound : Nat) :
    (formula inputWidth gateBound).size = selectorSize gateBound :=
  size_formula_internal inputWidth gateBound

/-- The selector only names the description prefix and completed gate outputs. -/
theorem vars_formula_lt (inputWidth gateBound : Nat) :
    ∀ wire ∈ (formula inputWidth gateBound).vars,
      wire < fullAvailable inputWidth gateBound :=
  vars_formula_lt_internal inputWidth gateBound

/-- The encoded positive gate count selects exactly the last active slot. -/
theorem eval_formula_of_code
    {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound)
    (hpositive : description.Positive) (assignment : Nat → Bool)
    (hcode : ∀ coordinate,
      assignment coordinate.val = Description.encode description coordinate) :
    (formula inputWidth gateBound).eval assignment =
      assignment (stepOutputWire inputWidth gateBound
        (lastActiveSlot description hpositive)) :=
  eval_formula_of_code_internal description hpositive assignment hcode

/-- On a complete lockstep evaluation, selector semantics is the direct padded
memo value at the last active slot. -/
theorem some_eval_formula_prefixResult
    {inputWidth gateBound : Nat}
    {description : Description inputWidth gateBound}
    (hdescription : description.WellFormed)
    (input : BitString inputWidth)
    (result : EvaluationSequence.PrefixResult description input gateBound
      (Nat.le_refl gateBound)) :
    some ((formula inputWidth gateBound).eval
        (memoAssignment result.circuitWires)) =
      result.rawWires[inputWidth +
        (lastActiveSlot description hdescription.1).val]? :=
  some_eval_formula_prefixResult_internal hdescription input result

/-- On a valid description, selector semantics is exactly ordinary raw-circuit
evaluation on the sample input. -/
theorem some_eval_formula_eq_eval?
    {inputWidth gateBound : Nat}
    {description : Description inputWidth gateBound}
    (hdescription : description.WellFormed)
    (input : BitString inputWidth)
    (result : EvaluationSequence.PrefixResult description input gateBound
      (Nat.le_refl gateBound)) :
    some ((formula inputWidth gateBound).eval
        (memoAssignment result.circuitWires)) =
      description.toRawCircuit.eval? input.toList :=
  some_eval_formula_eq_eval?_internal hdescription input result

/-- Selector compilation emits exactly its advertised formula size. -/
@[simp] theorem length_compileRaw (inputWidth gateBound : Nat) :
    (compileRaw inputWidth gateBound).length = selectorSize gateBound :=
  length_compileRaw_internal inputWidth gateBound

/-- The selector fragment only references wires available after the complete
gate sequence. -/
theorem topologicallyWellFormed_compileRaw (inputWidth gateBound : Nat) :
    (compileRaw inputWidth gateBound).TopologicallyWellFormed
      (fullAvailable inputWidth gateBound) :=
  topologicallyWellFormed_compileRaw_internal inputWidth gateBound

/-- The complete evaluator emits the gate-sequence prefix and one selector
formula. -/
@[simp] theorem length_circuit (inputWidth gateBound : Nat) :
    (circuit inputWidth gateBound).length =
      prefixSize inputWidth gateBound gateBound + selectorSize gateBound :=
  length_circuit_internal inputWidth gateBound

/-- The complete evaluator's designated output is its final emitted wire. -/
theorem outputWire_eq (inputWidth gateBound : Nat) :
    outputWire inputWidth gateBound =
      baseWireCount inputWidth gateBound +
        (circuit inputWidth gateBound).length - 1 :=
  outputWire_eq_internal inputWidth gateBound

/-- The complete evaluator is topologically valid from its description-and-
sample input block. -/
theorem topologicallyWellFormed_circuit (inputWidth gateBound : Nat) :
    (circuit inputWidth gateBound).TopologicallyWellFormed
      (baseWireCount inputWidth gateBound) :=
  topologicallyWellFormed_circuit_internal inputWidth gateBound

/-- A valid fixed-width description's complete evaluator runs successfully and
returns its direct raw-circuit value. -/
noncomputable def result {inputWidth gateBound : Nat}
    {description : Description inputWidth gateBound}
    (hdescription : description.WellFormed)
    (input : BitString inputWidth) : Result description input :=
  resultInternal hdescription input

/-- The complete evaluator is nonempty because its selector emits at least one
gate. -/
theorem circuit_ne_nil (inputWidth gateBound : Nat) :
    circuit inputWidth gateBound ≠ [] :=
  circuit_ne_nil_internal inputWidth gateBound

/-- Complete fixed-width evaluation agrees exactly with ordinary raw-circuit
evaluation on a valid encoded description and sample. -/
theorem eval?_circuit
    {inputWidth gateBound : Nat}
    {description : Description inputWidth gateBound}
    (hdescription : description.WellFormed)
    (input : BitString inputWidth) :
    (circuit inputWidth gateBound).eval?
        (EvaluationSequence.combinedInput description input).toList =
      description.toRawCircuit.eval? input.toList :=
  eval?_circuit_internal hdescription input

end EvaluationOutput

end Description

end FixedWidth

end CircuitCode

end Complexity
