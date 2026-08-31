/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Sequence.Defs
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Sequence.Internal

/-!
# Sequential fixed-width gate evaluation

This module exposes the exact length and topological correctness of the raw
fragment that computes every fixed-width gate slot in sequence.
-/


public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace Description

namespace EvaluationSequence

open EvaluationLayout

/-- A compiled gate step emits exactly its advertised formula size. -/
@[simp] theorem length_stepCircuit {inputWidth gateBound : Nat}
    (slot : Fin gateBound) :
    (stepCircuit inputWidth gateBound slot).length =
      GateFormula.gateSize inputWidth gateBound slot :=
  length_stepCircuit_internal slot

/-- The total natural-index step builder agrees with the numeric size oracle. -/
@[simp] theorem length_stepCircuitAt (inputWidth gateBound index : Nat) :
    (stepCircuitAt inputWidth gateBound index).length =
      sizeAt inputWidth gateBound index :=
  length_stepCircuitAt_internal inputWidth gateBound index

/-- A prefix circuit emits exactly its corresponding formula-size prefix. -/
@[simp] theorem length_prefixCircuit (inputWidth gateBound count : Nat) :
    (prefixCircuit inputWidth gateBound count).length =
      prefixSize inputWidth gateBound count :=
  length_prefixCircuit_internal inputWidth gateBound count

/-- The complete gate sequence has the full bounded formula-size prefix. -/
@[simp] theorem length_circuit (inputWidth gateBound : Nat) :
    (circuit inputWidth gateBound).length =
      prefixSize inputWidth gateBound gateBound :=
  length_circuit_internal inputWidth gateBound

/-- Every compiled gate step references only its entry prefix or gates emitted
earlier in that formula fragment. -/
theorem topologicallyWellFormed_stepCircuit
    {inputWidth gateBound : Nat} (slot : Fin gateBound) :
    (stepCircuit inputWidth gateBound slot).TopologicallyWellFormed
      (stepAvailable inputWidth gateBound slot) :=
  topologicallyWellFormed_stepCircuit_internal slot

/-- Every in-range sequential prefix is topologically well formed from the
description-and-sample input block. -/
theorem topologicallyWellFormed_prefixCircuit
    (inputWidth gateBound count : Nat) (hcount : count ≤ gateBound) :
    (prefixCircuit inputWidth gateBound count).TopologicallyWellFormed
      (baseWireCount inputWidth gateBound) :=
  topologicallyWellFormed_prefixCircuit_internal
    inputWidth gateBound count hcount

/-- The complete bounded gate sequence is topologically well formed. -/
theorem topologicallyWellFormed_circuit (inputWidth gateBound : Nat) :
    (circuit inputWidth gateBound).TopologicallyWellFormed
      (baseWireCount inputWidth gateBound) :=
  topologicallyWellFormed_circuit_internal inputWidth gateBound

end EvaluationSequence

end Description

end FixedWidth

end CircuitCode

end Complexity
