/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Predecessor.Defs
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Predecessor.Internal

/-!
# Verified direct predecessor-head formula generation

This module exposes the executable predecessor-head generator together with
its exact entry domain, restored work-vector effect, and encoded numeric
schedule. Direction codes zero and one mean left and right; all other codes
mean stay, matching `movedHeadPositionCode`.
-/

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Direct predecessor-head generation is sound on its explicit clean domain. -/
theorem emitPredecessorHeadFormula_sound (stateCount directionCode : ℕ) :
    (emitPredecessorHeadFormula stateCount directionCode).Sound :=
  emitPredecessorHeadFormula_sound_internal stateCount directionCode

/-- The generator's domain is exactly clean owned scratch, a positive horizon,
and an in-range target position. -/
theorem emitPredecessorHeadFormula_requires
    (stateCount directionCode : ℕ) (values : BinaryValues WorkCount) :
    (emitPredecessorHeadFormula stateCount directionCode).requires values ↔
      PredecessorHeadClean values ∧ 0 < values Work.horizon ∧
        values Work.position ≤ values Work.horizon :=
  emitPredecessorHeadFormula_requires_internal stateCount directionCode values

/-- The generator restores every owned scratch register and advances the wire
frontier by exactly the predecessor-head schedule size. -/
theorem emitPredecessorHeadFormula_effect
    (stateCount directionCode : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitPredecessorHeadFormula stateCount directionCode).effect values =
      Function.update values Work.available
        (values Work.available +
          movedHeadPredecessorSize (values Work.horizon)) :=
  emitPredecessorHeadFormula_effect_internal stateCount directionCode values
    hclean hhorizon htarget

/-- The emitted word is exactly the encoded numeric predecessor-head schedule
at the run-time layout, target, and horizon. -/
theorem emitPredecessorHeadFormula_emitted
    (stateCount directionCode : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitPredecessorHeadFormula stateCount directionCode).emitted values =
      (predecessorHeadFormulaSchedule stateCount (values Work.horizon)
        (values Work.configBase) (values Work.available)
        (values Work.tapeIndex) (values Work.position)
        directionCode).flatMap CircuitCode.RawGate.encode :=
  emitPredecessorHeadFormula_emitted_internal stateCount directionCode values
    hclean hhorizon htarget

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
