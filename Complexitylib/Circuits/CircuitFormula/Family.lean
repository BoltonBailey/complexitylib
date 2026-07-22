/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonConverse
import Complexitylib.Circuits.CircuitFormula.Family.Defs
import Complexitylib.Circuits.CircuitFormula.Family.Internal

/-!
# Circuit-family outputs as formula families

This module lifts selected-output circuit unfolding to total families. A typed
fan-in-two circuit family yields a formula family with identical semantics and
at most twice its depth. Consequently the total-assignment view of every
`NC1` Boolean-function family lies in `FormulaNC1` and hence in the width-`5`
branching-program class `Width5BP`.

No formula-size bound is used: shared circuit DAGs may expand exponentially
when unfolded. Barrington's construction depends on formula depth, which the
translation controls directly.
-/

namespace Complexity

namespace Circuit

/-- A single-output circuit's global depth is the depth of its unique output. -/
theorem depth_eq_outputDepth_zero {N G : ℕ} [NeZero N]
    (circuit : Circuit Basis.andOr2 N 1 G) :
    circuit.depth = circuit.outputDepth 0 :=
  depth_eq_outputDepth_zero_internal circuit

end Circuit

namespace CircuitFamily

/-- The unfolded formula at length `n` has exactly the circuit family's
length-`n` semantics on the corresponding total assignment. -/
theorem eval_outputFormulaFamily
    (F : CircuitFamily Basis.andOr2) (n : ℕ) (assignment : ℕ → Bool) :
    BoolFormula.eval assignment (F.outputFormulaFamily n) =
      F.function n (fun input => assignment input.val) :=
  eval_outputFormulaFamily_internal F n assignment

/-- Family-level selected-output unfolding increases depth by at most a factor
of two. -/
theorem depth_outputFormulaFamily_le
    (F : CircuitFamily Basis.andOr2) (n : ℕ) :
    (F.outputFormulaFamily n).depth ≤ 2 * F.depth n :=
  depth_outputFormulaFamily_le_internal F n

/-- Unfolding a circuit family computes its total-assignment semantics. -/
theorem outputFormulaFamily_computes
    {F : CircuitFamily Basis.andOr2} {f : BoolFunFamily}
    (hcomputes : F.Computes f) :
    F.outputFormulaFamily.Computes f.onTotalAssignments :=
  outputFormulaFamily_computes_internal hcomputes

/-- A `c * log₂ n + c` circuit-depth bound produces a logarithmic-depth
formula family. -/
theorem outputFormulaFamily_logDepth
    {F : CircuitFamily Basis.andOr2} {c : ℕ}
    (hdepth : F.DepthBoundedBy fun n => c * Nat.log 2 n + c) :
    F.outputFormulaFamily.LogDepth :=
  outputFormulaFamily_logDepth_internal hdepth

end CircuitFamily

/-- The total-assignment views of `NC1` Boolean-function families are
logarithmic-depth formula families. -/
theorem NC1_onTotalAssignments_subset_FormulaNC1 :
    BoolFunFamily.onTotalAssignments '' NC1 ⊆ FormulaNC1 :=
  NC1_onTotalAssignments_subset_FormulaNC1_internal

/-- Pointwise form of the bridge from typed `NC1` circuit families to
logarithmic-depth formula families. -/
theorem BoolFunFamily.onTotalAssignments_mem_FormulaNC1
    {f : BoolFunFamily} (hf : f ∈ NC1) :
    f.onTotalAssignments ∈ FormulaNC1 :=
  NC1_onTotalAssignments_subset_FormulaNC1 ⟨f, hf, rfl⟩

/-- **Barrington for typed `NC1` circuit families.** Their total-assignment
views have polynomial-length width-`5` permutation branching programs. -/
theorem NC1_onTotalAssignments_subset_Width5BP :
    BoolFunFamily.onTotalAssignments '' NC1 ⊆ Width5BP :=
  NC1_onTotalAssignments_subset_FormulaNC1.trans
    formulaNC1_subset_width5BP

/-- Pointwise Barrington theorem for a typed `NC1` Boolean-function family. -/
theorem BoolFunFamily.onTotalAssignments_mem_Width5BP
    {f : BoolFunFamily} (hf : f ∈ NC1) :
    f.onTotalAssignments ∈ Width5BP :=
  NC1_onTotalAssignments_subset_Width5BP ⟨f, hf, rfl⟩

end Complexity
