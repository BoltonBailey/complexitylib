/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Match.Defs
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Match.Internal

/-!
# Fixed-width one-sample output matching

The fixed-label extension is one gate larger than the complete evaluator,
remains topologically valid, and accepts exactly when the represented raw
circuit returns the selected label on the supplied sample input.
-/


public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace Description

namespace EvaluationMatch

open EvaluationLayout

/-- One fixed-label check adds exactly one final gate. -/
@[simp] theorem length_circuit (inputWidth gateBound : Nat)
    (expected : Bool) :
    (circuit inputWidth gateBound expected).length =
      (EvaluationOutput.circuit inputWidth gateBound).length + 1 :=
  length_circuit_internal inputWidth gateBound expected

/-- The fixed-label evaluator is topologically valid from the encoded
description and sample input block. -/
theorem topologicallyWellFormed_circuit
    (inputWidth gateBound : Nat) (expected : Bool) :
    (circuit inputWidth gateBound expected).TopologicallyWellFormed
      (baseWireCount inputWidth gateBound) :=
  topologicallyWellFormed_circuit_internal inputWidth gateBound expected

/-- A valid fixed-width description passes the fixed-label check exactly when
its ordinary raw circuit returns that label on the sample. -/
theorem eval?_circuit_eq_some_true_iff
    {inputWidth gateBound : Nat}
    {description : Description inputWidth gateBound}
    (hdescription : description.WellFormed)
    (input : BitString inputWidth) (expected : Bool) :
    (circuit inputWidth gateBound expected).eval?
        (EvaluationSequence.combinedInput description input).toList = some true ↔
      description.toRawCircuit.eval? input.toList = some expected :=
  eval?_circuit_eq_some_true_iff_internal hdescription input expected

end EvaluationMatch

end Description

end FixedWidth

end CircuitCode

end Complexity
