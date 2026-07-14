/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.MovedHead.Defs
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.MovedHead.Internal

/-!
# Verified direct moved-head formula generation

This module exposes the complete three-direction moved-head generator together
with its clean entry domain, restored work-vector effect, and exact encoded
numeric schedule.
-/

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Complete moved-head formula generation is sound. -/
theorem emitMovedHeadFormula_sound (tm : NTM k) (tape : TapeSlot k) :
    (emitMovedHeadFormula tm tape).Sound :=
  emitMovedHeadFormula_sound_internal tm tape

/-- Clean owned scratch, a positive horizon, an in-range target, and a valid
wire frontier suffice for complete moved-head formula generation. -/
theorem emitMovedHeadFormula_requires (tm : NTM k) (tape : TapeSlot k)
    (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon)
    (havailable : 1 ≤ values Work.available) :
    (emitMovedHeadFormula tm tape).requires values :=
  emitMovedHeadFormula_requires_internal tm tape values hclean hhorizon
    htarget havailable

/-- Moved-head generation restores every owned register and advances only the
wire frontier by the exact numeric schedule size. -/
@[simp] theorem emitMovedHeadFormula_effect (tm : NTM k)
    (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon)
    (havailable : 1 ≤ values Work.available) :
    (emitMovedHeadFormula tm tape).effect values =
      Function.update values Work.available
        (values Work.available +
          movedHeadFormulaScheduleSize (transitionCases tm).length k
            (values Work.horizon) (movedHeadCaseSelectedAt tm tape)
            (effectCaseChoiceAt tm)) :=
  emitMovedHeadFormula_effect_internal tm tape values hclean hhorizon htarget
    havailable

/-- The emitted word is literally the canonical numeric moved-head schedule,
including all three direction members, the false identity, and reverse fold. -/
@[simp] theorem emitMovedHeadFormula_emitted (tm : NTM k)
    (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon)
    (havailable : 1 ≤ values Work.available) :
    (emitMovedHeadFormula tm tape).emitted values =
      (movedHeadFormulaSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k (values Work.horizon)
        (values Work.configBase) (values Work.reference₀)
        (values Work.available) tape.index (values Work.position)
        (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm)
        (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
        (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm)).flatMap
          CircuitCode.RawGate.encode :=
  emitMovedHeadFormula_emitted_internal tm tape values hclean hhorizon
    htarget havailable

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
