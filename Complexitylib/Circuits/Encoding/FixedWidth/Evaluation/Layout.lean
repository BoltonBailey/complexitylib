/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Layout.Defs
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Layout.Internal

/-!
# Sequential fixed-width evaluator wire layout

This module exposes the exact formula-size schedule and backward-reference
invariants used to concatenate fixed-width encoded-gate formulas.
-/


public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace Description

namespace EvaluationLayout

/-- At an in-range slot, the numeric size oracle is the exact gate-formula
size. -/
@[simp] theorem sizeAt_eq {inputWidth gateBound : Nat}
    (slot : Fin gateBound) :
    sizeAt inputWidth gateBound slot.val =
      GateFormula.gateSize inputWidth gateBound slot :=
  sizeAt_eq_internal slot

/-- The prefix schedule advances by the size of its next slot. -/
@[simp] theorem prefixSize_succ (inputWidth gateBound count : Nat) :
    prefixSize inputWidth gateBound (count + 1) =
      prefixSize inputWidth gateBound count +
        sizeAt inputWidth gateBound count :=
  prefixSize_succ_internal inputWidth gateBound count

/-- Formula-size prefixes are monotone in their slot count. -/
theorem prefixSize_mono (inputWidth gateBound : Nat)
    {first second : Nat} (hbound : first ≤ second) :
    prefixSize inputWidth gateBound first ≤
      prefixSize inputWidth gateBound second :=
  prefixSize_mono_internal inputWidth gateBound hbound

/-- The end of a step is the global base plus the next size prefix. -/
theorem stepEnd_eq_prefix_succ {inputWidth gateBound : Nat}
    (slot : Fin gateBound) :
    stepAvailable inputWidth gateBound slot +
        GateFormula.gateSize inputWidth gateBound slot =
      baseWireCount inputWidth gateBound +
        prefixSize inputWidth gateBound (slot.val + 1) :=
  stepEnd_eq_prefix_succ_internal slot

/-- Every earlier gate result is available before the current step begins. -/
theorem earlier_output_lt_stepAvailable {inputWidth gateBound : Nat}
    (slot : Fin gateBound) (earlier : Fin slot.val) :
    stepOutputWire inputWidth gateBound (earlierSlot slot earlier) <
      stepAvailable inputWidth gateBound slot :=
  earlier_output_lt_stepAvailable_internal slot earlier

/-- Every generated source is represented by one variable leaf. -/
@[simp] theorem size_sourceFormula {inputWidth gateBound : Nat}
    (slot : Fin gateBound) (source : Fin (inputWidth + slot.val)) :
    (sourceFormula inputWidth gateBound slot source).size = 1 :=
  size_sourceFormula_internal slot source

/-- Each laid-out step has exactly its advertised gate-formula size. -/
@[simp] theorem size_stepFormula {inputWidth gateBound : Nat}
    (slot : Fin gateBound) :
    (stepFormula inputWidth gateBound slot).size =
      GateFormula.gateSize inputWidth gateBound slot :=
  size_stepFormula_internal slot

/-- Formula compilation places the step result on its assigned output wire. -/
@[simp] theorem rawOutputWire_stepFormula {inputWidth gateBound : Nat}
    (slot : Fin gateBound) :
    BoolFormula.rawOutputWire
        (stepAvailable inputWidth gateBound slot)
        (stepFormula inputWidth gateBound slot) =
      stepOutputWire inputWidth gateBound slot :=
  rawOutputWire_stepFormula_internal slot

/-- Every source formula references a wire available at step entry. -/
theorem vars_sourceFormula_lt {inputWidth gateBound : Nat}
    (slot : Fin gateBound) :
    ∀ source wire,
      wire ∈ (sourceFormula inputWidth gateBound slot source).vars →
      wire < stepAvailable inputWidth gateBound slot :=
  vars_sourceFormula_lt_internal slot

/-- The complete gate-step formula is topologically scoped to the prefix
available before its compilation. -/
theorem vars_stepFormula_lt {inputWidth gateBound : Nat}
    (slot : Fin gateBound) :
    ∀ wire ∈ (stepFormula inputWidth gateBound slot).vars,
      wire < stepAvailable inputWidth gateBound slot :=
  vars_stepFormula_lt_internal slot

end EvaluationLayout

end Description

end FixedWidth

end CircuitCode

end Complexity
