/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Case.Defs
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Case.Internal

/-!
# Direct-unrolling transition-case generator

Exact contracts for the forward stream of a fixed transition case, together
with soundness of the complete case-formula emitter.
-/

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Complete fixed transition-case emission is sound. -/
theorem emitCaseFormula_sound
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ) :
    (emitCaseFormula stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).Sound :=
  emitCaseFormula_sound_internal stateCount workCount stateIndex
    inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt

/-- A clean case-formula entry state satisfies every framed arithmetic,
reference, and gate-emission precondition of the complete emitter. -/
theorem emitCaseFormula_requires
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitCaseFormula stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).requires values :=
  emitCaseFormula_requires_internal stateCount workCount stateIndex
    inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt values
    hclean

/-- Complete case emission restores every owned scratch register and advances
the wire frontier by exactly the canonical case-schedule size. -/
@[simp] theorem emitCaseFormula_effect
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitCaseFormula stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).effect values =
      Function.update values Work.available
        (values Work.available +
          caseFormulaScheduleSize workCount (values Work.horizon)
            choiceValue) :=
  emitCaseFormula_effect_internal stateCount workCount stateIndex
    inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt values
    hclean

/-- Complete case emission is byte-for-byte the canonical numeric transition
case schedule, not merely a circuit with the same gate count. -/
@[simp] theorem emitCaseFormula_emitted
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitCaseFormula stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).emitted values =
      (caseFormulaSchedule stateCount workCount (values Work.horizon)
        (values Work.configBase) (values Work.reference₀)
        (values Work.available) stateIndex inputSymbolIndex outputSymbolIndex
        choiceValue workSymbolIndexAt).flatMap CircuitCode.RawGate.encode :=
  emitCaseFormula_emitted_internal stateCount workCount stateIndex
    inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt values
    hclean

/-- The clean-entry contract suffices for the forward member stream. -/
theorem emitCaseMembers_requires
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitCaseMembers stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).requires values :=
  emitCaseMembers_requires_internal stateCount workCount stateIndex
    inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt values
    hclean

/-- The forward member stream restores its owned reference scratch and only
retains the final tape and symbol selectors while advancing the wire frontier. -/
@[simp] theorem emitCaseMembers_effect
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitCaseMembers stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).effect values =
      Function.update
        (Function.update
          (Function.update values Work.tapeIndex (workCount + 1))
          Work.symbolIndex outputSymbolIndex) Work.available
        (values Work.available +
          caseFormulaMembersSize workCount (values Work.horizon)
            choiceValue) := by
  rw [emitCaseMembers_effect_internal stateCount workCount stateIndex
    inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt values
    hclean]
  rfl

/-- The forward member stream is exactly the canonical numeric member
schedule in choice, state, input, work-tape, and output order. -/
@[simp] theorem emitCaseMembers_emitted
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitCaseMembers stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).emitted values =
      (caseFormulaMemberGates stateCount workCount (values Work.horizon)
        (values Work.configBase) (values Work.reference₀)
        (values Work.available) stateIndex inputSymbolIndex
        outputSymbolIndex choiceValue workSymbolIndexAt).flatMap
          CircuitCode.RawGate.encode :=
  emitCaseMembers_emitted_internal stateCount workCount stateIndex
    inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt values
    hclean

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
