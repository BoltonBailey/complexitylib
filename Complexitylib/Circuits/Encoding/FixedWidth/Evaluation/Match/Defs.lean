/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Output.Defs
public import Complexitylib.Circuits.Encoding.Fragment.Defs

/-!
# Fixed-width one-sample output matching -- definitions

For a fixed expected label, append one final gate that accepts exactly when the
complete fixed-width evaluator returns that label. The description code and
sample input remain the circuit's incoming wire block.
-/


@[expose] public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace Description

namespace EvaluationMatch

open EvaluationLayout

/-- Complete fixed-width evaluation followed by equality with one fixed label. -/
def circuit (inputWidth gateBound : Nat) (expected : Bool) : RawCircuit :=
  RawCircuit.appendOutputMatch (baseWireCount inputWidth gateBound)
    (EvaluationOutput.circuit inputWidth gateBound) expected

end EvaluationMatch

end Description

end FixedWidth

end CircuitCode

end Complexity
