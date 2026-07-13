/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.Encoding.Internal.Fragment

/-!
# Appendable raw-circuit fragments

Generic composition laws for building a `CircuitCode.RawCircuit` in successive
topologically ordered fragments. Evaluation passes the memo array from one
fragment to the next, and successful evaluation preserves every previously
available wire.
-/

namespace Complexity

namespace CircuitCode

namespace RawCircuit

/-- Evaluating appended raw fragments is sequential evaluation with the first
fragment's memo array passed to the second. -/
theorem evalAux?_append (first second : RawCircuit) (wires : Array Bool) :
    evalAux? (first ++ second) wires =
      (evalAux? first wires).bind (evalAux? second) :=
  evalAux?_append_internal first second wires

/-- Appended fragments are topological exactly when each fragment is
topological at its corresponding initial wire count. -/
theorem topologicallyWellFormed_append (available : ℕ)
    (first second : RawCircuit) :
    TopologicallyWellFormed available (first ++ second) ↔
      TopologicallyWellFormed available first ∧
        TopologicallyWellFormed (available + first.length) second :=
  topologicallyWellFormed_append_internal available first second

/-- Successful fragment evaluation does not change any pre-existing wire. -/
theorem evalAux?_preserves_prefix {circuit : RawCircuit}
    {wires result : Array Bool} (heval : evalAux? circuit wires = some result)
    {i : ℕ} (hi : i < wires.size) : result[i]? = wires[i]? :=
  evalAux?_preserves_prefix_internal heval hi

end RawCircuit

end CircuitCode

end Complexity
