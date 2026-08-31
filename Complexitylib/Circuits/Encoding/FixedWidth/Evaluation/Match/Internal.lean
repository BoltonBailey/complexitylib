/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Match.Defs
import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Output
import Complexitylib.Circuits.Encoding.Fragment

/-!
# Fixed-width one-sample output matching -- proof internals
-/


public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace Description

namespace EvaluationMatch

open EvaluationLayout

theorem length_circuit_internal (inputWidth gateBound : Nat)
    (expected : Bool) :
    (circuit inputWidth gateBound expected).length =
      (EvaluationOutput.circuit inputWidth gateBound).length + 1 := by
  simp [circuit, RawCircuit.appendOutputMatch]

theorem topologicallyWellFormed_circuit_internal
    (inputWidth gateBound : Nat) (expected : Bool) :
    (circuit inputWidth gateBound expected).TopologicallyWellFormed
      (baseWireCount inputWidth gateBound) := by
  unfold circuit RawCircuit.appendOutputMatch
  rw [RawCircuit.topologicallyWellFormed_append]
  constructor
  · exact EvaluationOutput.topologicallyWellFormed_circuit
      inputWidth gateBound
  · have hcode : codeWidth inputWidth gateBound ≠ 0 :=
      NeZero.ne (codeWidth inputWidth gateBound)
    simp [RawCircuit.TopologicallyWellFormed,
      RawGate.WellFormedAt, RawGate.copy, baseWireCount]
    omega

theorem eval?_circuit_eq_some_true_iff_internal
    {inputWidth gateBound : Nat}
    {description : Description inputWidth gateBound}
    (hdescription : description.WellFormed)
    (input : BitString inputWidth) (expected : Bool) :
    (circuit inputWidth gateBound expected).eval?
        (EvaluationSequence.combinedInput description input).toList = some true ↔
      description.toRawCircuit.eval? input.toList = some expected := by
  unfold circuit
  have hlength :
      (EvaluationSequence.combinedInput description input).toList.length =
        baseWireCount inputWidth gateBound :=
    BitString.length_toList _
  calc
    (RawCircuit.appendOutputMatch (baseWireCount inputWidth gateBound)
          (EvaluationOutput.circuit inputWidth gateBound) expected).eval?
          (EvaluationSequence.combinedInput description input).toList =
        some true ↔
        (EvaluationOutput.circuit inputWidth gateBound).eval?
          (EvaluationSequence.combinedInput description input).toList =
            some expected := by
      simpa only [hlength] using
        (RawCircuit.eval?_appendOutputMatch_eq_some_true_iff
          (EvaluationOutput.circuit inputWidth gateBound)
          (EvaluationSequence.combinedInput description input).toList
          expected (EvaluationOutput.circuit_ne_nil inputWidth gateBound))
    _ ↔ description.toRawCircuit.eval? input.toList = some expected := by
      rw [EvaluationOutput.eval?_circuit hdescription input]

end EvaluationMatch

end Description

end FixedWidth

end CircuitCode

end Complexity
