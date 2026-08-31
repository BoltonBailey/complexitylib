/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Layout.Defs

/-!
# Sequential fixed-width gate evaluation -- definitions

Each gate-slot formula is compiled after the exact wire prefix assigned by the
layout layer. Prefix circuits concatenate the first `count` compiled steps;
out-of-range natural indices contribute the empty fragment so the builder is
total, while the public evaluator uses exactly `gateBound` steps.
-/


@[expose] public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace Description

namespace EvaluationSequence

open EvaluationLayout

/-- Raw formula fragment computing one fixed-width gate slot. -/
def stepCircuit (inputWidth gateBound : Nat)
    (slot : Fin gateBound) : RawCircuit :=
  BoolFormula.compileRaw
    (stepAvailable inputWidth gateBound slot)
    (stepFormula inputWidth gateBound slot)

/-- Compiled step at a natural index, empty when the index is out of range. -/
def stepCircuitAt (inputWidth gateBound index : Nat) : RawCircuit :=
  if hindex : index < gateBound then
    stepCircuit inputWidth gateBound ⟨index, hindex⟩
  else
    []

/-- Concatenation of the first `count` sequential gate-slot fragments. -/
def prefixCircuit (inputWidth gateBound : Nat) : Nat → RawCircuit
  | 0 => []
  | count + 1 =>
      prefixCircuit inputWidth gateBound count ++
        stepCircuitAt inputWidth gateBound count

/-- Raw fragment computing all bounded gate-slot values for one description
and sample input. -/
def circuit (inputWidth gateBound : Nat) : RawCircuit :=
  prefixCircuit inputWidth gateBound gateBound

end EvaluationSequence

end Description

end FixedWidth

end CircuitCode

end Complexity
