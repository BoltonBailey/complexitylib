/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Read.Defs
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Read.Internal

/-!
# Direct-unrolling read-formula generator

A stack-free proof-carrying routine that emits the exact numeric gate schedule
for reading one symbol from a bounded encoded configuration.
-/

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Complete read-formula emission is sound. -/
theorem emitReadFormula_sound (stateCount tapeCount : ℕ) :
    (emitReadFormula stateCount tapeCount).Sound :=
  emitReadFormula_sound_internal stateCount tapeCount

/-- The clean-entry contract suffices for every arithmetic, loop, reference,
and raw-gate leaf in complete read-formula emission. -/
theorem emitReadFormula_requires (stateCount tapeCount : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : ReadFormulaClean values) :
    (emitReadFormula stateCount tapeCount).requires values :=
  emitReadFormula_requires_internal stateCount tapeCount values hclean

/-- Complete read-formula emission restores all owned scratch and only advances
the wire frontier, by four gates per possible head position plus the false
identity gate. -/
@[simp] theorem emitReadFormula_effect (stateCount tapeCount : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : ReadFormulaClean values) :
    (emitReadFormula stateCount tapeCount).effect values =
      Function.update values Work.available
        (values Work.available + (4 * (values Work.horizon + 1) + 1)) :=
  emitReadFormula_effect_internal stateCount tapeCount values hclean

/-- Complete read-formula emission produces exactly the canonical serialized
read-formula schedule at the current horizon and wire frontier. -/
@[simp] theorem emitReadFormula_emitted (stateCount tapeCount : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : ReadFormulaClean values) :
    (emitReadFormula stateCount tapeCount).emitted values =
      (readFormulaSchedule stateCount tapeCount (values Work.horizon)
        (values Work.configBase) (values Work.available)
        (values Work.tapeIndex) (values Work.symbolIndex)).flatMap
          CircuitCode.RawGate.encode :=
  emitReadFormula_emitted_internal stateCount tapeCount values hclean

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
