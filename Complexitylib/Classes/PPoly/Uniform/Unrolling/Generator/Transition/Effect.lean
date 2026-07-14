/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Effect.Defs
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Effect.Internal

/-!
# Direct-unrolling transition-effect generator

Exact contracts for the generated disjunction over a machine's finite
transition table.
-/

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Complete transition-effect emission is sound. -/
theorem emitEffectFormula_sound (tm : NTM k)
    (selects : TransitionEffect tm → Bool) :
    (emitEffectFormula tm selects).Sound :=
  emitEffectFormula_sound_internal tm selects

/-- Clean scratch together with a positive wire frontier suffices for every
leaf routine in complete transition-effect emission. -/
theorem emitEffectFormula_requires (tm : NTM k)
    (selects : TransitionEffect tm → Bool)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (havailable : 1 ≤ values Work.available) :
    (emitEffectFormula tm selects).requires values :=
  emitEffectFormula_requires_internal tm selects values hclean havailable

/-- Complete transition-effect emission restores all owned scratch and
advances only the wire frontier by the exact numeric schedule size. -/
@[simp] theorem emitEffectFormula_effect (tm : NTM k)
    (selects : TransitionEffect tm → Bool)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (havailable : 1 ≤ values Work.available) :
    (emitEffectFormula tm selects).effect values =
      Function.update values Work.available
        (values Work.available +
          effectFormulaScheduleSize (transitionCases tm).length k
            (values Work.horizon) (effectCaseSelectedAt tm selects)
            (effectCaseChoiceAt tm)) :=
  emitEffectFormula_effect_internal tm selects values hclean havailable

/-- Complete transition-effect emission is literally the canonical numeric
raw-gate schedule, including its false identity and reverse connector suffix. -/
@[simp] theorem emitEffectFormula_emitted (tm : NTM k)
    (selects : TransitionEffect tm → Bool)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (havailable : 1 ≤ values Work.available) :
    (emitEffectFormula tm selects).emitted values =
      (effectFormulaSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k (values Work.horizon)
        (values Work.configBase) (values Work.reference₀)
        (values Work.available) (effectCaseSelectedAt tm selects)
        (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
        (effectCaseInputSymbolIndexAt tm) (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm)).flatMap
          CircuitCode.RawGate.encode :=
  emitEffectFormula_emitted_internal tm selects values hclean havailable

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
