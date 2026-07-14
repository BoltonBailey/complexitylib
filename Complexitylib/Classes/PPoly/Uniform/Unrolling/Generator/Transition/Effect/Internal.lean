/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Offset
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Case
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Read
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Effect.Defs
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Arithmetic
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.List

/-!
# Direct-unrolling transition-effect generator -- proof internals
-/

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Scratch invariant while a rolling effect-member output reference moves
backward through the variable-width case stream. -/
private structure EffectConnectorClean
    (values : BinaryValues WorkCount) : Prop where
  reference₁ : values Work.reference₁ = 0
  loop₃ : values Work.loop₃ = 0
  temporary₂ : values Work.temporary₂ = 0
  temporary₃ : values Work.temporary₃ = 0
  emitCounter : values Work.emitCounter = 0
  copyCounter : values Work.copyCounter = 0
  multiplyCounter : values Work.multiplyCounter = 0
  addCounter : values Work.addCounter = 0

private theorem CaseFormulaClean.updateAvailable
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (available : ℕ) :
    CaseFormulaClean (Function.update values Work.available available) := by
  refine
    { toReadFormulaClean :=
        { position := ?_
          loop₀ := ?_
          limit₀ := ?_
          reference₀ := ?_
          reference₁ := ?_
          emitCounter := ?_
          copyCounter := ?_
          multiplyCounter := ?_
          addCounter := ?_
          temporary₀ := ?_
          temporary₁ := ?_
          temporary₂ := ?_ }
      loop₃ := ?_
      temporary₃ := ?_
      polynomialScratch := ?_
      tapeIndex := ?_
      symbolIndex := ?_ }
  all_goals
    simp only [Function.update_apply]
    rw [if_neg (by decide)]
  · exact hclean.position
  · exact hclean.loop₀
  · exact hclean.limit₀
  · exact hclean.reference₀
  · exact hclean.reference₁
  · exact hclean.emitCounter
  · exact hclean.copyCounter
  · exact hclean.multiplyCounter
  · exact hclean.addCounter
  · exact hclean.temporary₀
  · exact hclean.temporary₁
  · exact hclean.temporary₂
  · exact hclean.loop₃
  · exact hclean.temporary₃
  · exact hclean.polynomialScratch
  · exact hclean.tapeIndex
  · exact hclean.symbolIndex

private theorem CaseFormulaClean.effectConnectorClean
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    EffectConnectorClean values :=
  { reference₁ := hclean.reference₁
    loop₃ := hclean.loop₃
    temporary₂ := hclean.temporary₂
    temporary₃ := hclean.temporary₃
    emitCounter := hclean.emitCounter
    copyCounter := hclean.copyCounter
    multiplyCounter := hclean.multiplyCounter
    addCounter := hclean.addCounter }

private theorem EffectConnectorClean.updateReference₀
    (values : BinaryValues WorkCount) (hclean : EffectConnectorClean values)
    (reference : ℕ) :
    EffectConnectorClean
      (Function.update values Work.reference₀ reference) := by
  refine
    { reference₁ := ?_
      loop₃ := ?_
      temporary₂ := ?_
      temporary₃ := ?_
      emitCounter := ?_
      copyCounter := ?_
      multiplyCounter := ?_
      addCounter := ?_ }
  · simpa [Work.reference₀, Work.reference₁] using hclean.reference₁
  · simpa [Work.reference₀, Work.loop₃] using hclean.loop₃
  · simpa [Work.reference₀, Work.temporary₂] using hclean.temporary₂
  · simpa [Work.reference₀, Work.temporary₃] using hclean.temporary₃
  · simpa [Work.reference₀, Work.emitCounter] using hclean.emitCounter
  · simpa [Work.reference₀, Work.copyCounter] using hclean.copyCounter
  · simpa [Work.reference₀, Work.multiplyCounter] using
      hclean.multiplyCounter
  · simpa [Work.reference₀, Work.addCounter] using hclean.addCounter

private theorem EffectConnectorClean.afterReadConnector
    (values : BinaryValues WorkCount) (hclean : EffectConnectorClean values) :
    EffectConnectorClean (emitReadConnector.effect values) := by
  rw [emitReadConnector_effect_internal]
  refine
    { reference₁ := by simp
      loop₃ := ?_
      temporary₂ := ?_
      temporary₃ := ?_
      emitCounter := ?_
      copyCounter := ?_
      multiplyCounter := ?_
      addCounter := ?_ }
  · simpa [Work.available, Work.reference₁, Work.loop₃] using
      hclean.loop₃
  · simpa [Work.available, Work.reference₁, Work.temporary₂] using
      hclean.temporary₂
  · simpa [Work.available, Work.reference₁, Work.temporary₃] using
      hclean.temporary₃
  · simpa [Work.available, Work.reference₁, Work.emitCounter] using
      hclean.emitCounter
  · simpa [Work.available, Work.reference₁, Work.copyCounter] using
      hclean.copyCounter
  · simpa [Work.available, Work.reference₁, Work.multiplyCounter] using
      hclean.multiplyCounter
  · simpa [Work.available, Work.reference₁, Work.addCounter] using
      hclean.addCounter

private theorem emitReadConnector_sound_for_effect :
    emitReadConnector.Sound := by
  apply BinaryRoutine.seqList_sound
  intro member hmember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
  rcases hmember with hmember | hmember | hmember
  · subst member
    exact prepareRecentReference_sound Work.reference₁ 1
  · subst member
    exact BinaryRoutine.emitRawGateStep_sound .or false false Work.emitCounter
      Work.available Work.reference₀ Work.reference₁
  · subst member
    exact BinaryRoutine.clear_sound Work.reference₁

theorem emitEffectCaseAt_sound_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool) (caseIndex : ℕ) :
    (emitEffectCaseAt tm selects caseIndex).Sound := by
  rw [emitEffectCaseAt]
  split
  · exact emitCaseFormula_sound_internal (Fintype.card tm.Q) k
      (effectCaseStateIndexAt tm caseIndex)
      (effectCaseInputSymbolIndexAt tm caseIndex)
      (effectCaseOutputSymbolIndexAt tm caseIndex)
      (effectCaseChoiceAt tm caseIndex)
      (effectCaseWorkSymbolIndexAt tm caseIndex)
  · exact emitConstantGate_sound_internal false

theorem emitEffectCaseAt_requires_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool) (caseIndex : ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitEffectCaseAt tm selects caseIndex).requires values := by
  rw [emitEffectCaseAt]
  split
  · exact emitCaseFormula_requires_internal (Fintype.card tm.Q) k
      (effectCaseStateIndexAt tm caseIndex)
      (effectCaseInputSymbolIndexAt tm caseIndex)
      (effectCaseOutputSymbolIndexAt tm caseIndex)
      (effectCaseChoiceAt tm caseIndex)
      (effectCaseWorkSymbolIndexAt tm caseIndex) values hclean
  · exact emitConstantGate_requires_internal false values
      hclean.emitCounter

@[simp] theorem emitEffectCaseAt_effect_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool) (caseIndex : ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitEffectCaseAt tm selects caseIndex).effect values =
      Function.update values Work.available
        (values Work.available +
          effectFormulaCaseSize k (values Work.horizon)
            (effectCaseSelectedAt tm selects caseIndex)
            (effectCaseChoiceAt tm caseIndex)) := by
  rw [emitEffectCaseAt]
  by_cases hselected : effectCaseSelectedAt tm selects caseIndex
  · rw [if_pos hselected]
    rw [emitCaseFormula_effect_internal (Fintype.card tm.Q) k
      (effectCaseStateIndexAt tm caseIndex)
      (effectCaseInputSymbolIndexAt tm caseIndex)
      (effectCaseOutputSymbolIndexAt tm caseIndex)
      (effectCaseChoiceAt tm caseIndex)
      (effectCaseWorkSymbolIndexAt tm caseIndex) values hclean]
    simp [effectFormulaCaseSize, hselected]
  · rw [if_neg hselected, emitConstantGate_effect_internal]
    simp [effectFormulaCaseSize, hselected]

theorem emitEffectCaseAt_emitted_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool) (caseIndex available : ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (havailable : values Work.available =
      effectFormulaCaseAvailable (transitionCases tm).length k
        (values Work.horizon) available (effectCaseSelectedAt tm selects)
        (effectCaseChoiceAt tm) caseIndex) :
    (emitEffectCaseAt tm selects caseIndex).emitted values =
      (effectFormulaCaseBlock (transitionCases tm).length
        (Fintype.card tm.Q) k (values Work.horizon)
        (values Work.configBase) (values Work.reference₀) available
        (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)
        (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
        (effectCaseOutputSymbolIndexAt tm) (effectCaseWorkSymbolIndexAt tm)
        caseIndex).flatMap CircuitCode.RawGate.encode := by
  rw [emitEffectCaseAt]
  by_cases hselected : effectCaseSelectedAt tm selects caseIndex
  · rw [if_pos hselected]
    rw [emitCaseFormula_emitted_internal (Fintype.card tm.Q) k
      (effectCaseStateIndexAt tm caseIndex)
      (effectCaseInputSymbolIndexAt tm caseIndex)
      (effectCaseOutputSymbolIndexAt tm caseIndex)
      (effectCaseChoiceAt tm caseIndex)
      (effectCaseWorkSymbolIndexAt tm caseIndex) values hclean]
    simp [effectFormulaCaseBlock, hselected, havailable]
  · rw [if_neg hselected,
      emitConstantGate_emitted_internal false values hclean.reference₀]
    simp [effectFormulaCaseBlock, hselected, directInitConstant]

private theorem emitEffectMembersFrom_sound (tm : NTM k)
    (selects : TransitionEffect tm → Bool) (start count : ℕ) :
    (emitEffectMembersFrom tm selects start count).Sound := by
  induction count generalizing start with
  | zero => exact BinaryRoutine.identity_sound
  | succ count ih =>
      exact (emitEffectCaseAt_sound_internal tm selects start).seq
        (ih (start + 1))

theorem emitEffectMembers_sound_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool) :
    (emitEffectMembers tm selects).Sound :=
  emitEffectMembersFrom_sound tm selects 0 (transitionCases tm).length

private theorem emitEffectMembersFrom_requires (tm : NTM k)
    (selects : TransitionEffect tm → Bool) (start count : ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitEffectMembersFrom tm selects start count).requires values := by
  induction count generalizing start values with
  | zero =>
      simp [emitEffectMembersFrom, BinaryRoutine.identity,
        BinaryRoutine.emitBits]
  | succ count ih =>
      rw [emitEffectMembersFrom, BinaryRoutine.seq]
      refine ⟨emitEffectCaseAt_requires_internal tm selects start values
        hclean, ?_⟩
      rw [emitEffectCaseAt_effect_internal tm selects start values hclean]
      exact ih (start + 1) _
        (CaseFormulaClean.updateAvailable values hclean _)

theorem emitEffectMembers_requires_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitEffectMembers tm selects).requires values :=
  emitEffectMembersFrom_requires tm selects 0 (transitionCases tm).length
    values hclean

private theorem emitEffectMembersFrom_effect
    (tm : NTM k) (selects : TransitionEffect tm → Bool)
    (start count base T : ℕ) (values : BinaryValues WorkCount)
    (hclean : CaseFormulaClean values)
    (hbound : start + count ≤ (transitionCases tm).length)
    (hhorizon : values Work.horizon = T)
    (havailable : values Work.available =
      base + prefixSize
        (effectFormulaSizeAt (transitionCases tm).length k T
          (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)) start) :
    (emitEffectMembersFrom tm selects start count).effect values =
      Function.update values Work.available
        (base + prefixSize
          (effectFormulaSizeAt (transitionCases tm).length k T
            (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm))
          (start + count)) := by
  induction count generalizing start values with
  | zero =>
      rw [emitEffectMembersFrom]
      change values = _
      funext i
      by_cases havailableIndex : i = Work.available
      · subst i
        simpa using havailable
      · simp [havailableIndex]
  | succ count ih =>
      let sizeAt := effectFormulaSizeAt (transitionCases tm).length k T
        (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)
      have hindex : start < (transitionCases tm).length := by omega
      have hsizeAt : sizeAt start =
          effectFormulaCaseSize k T
            (effectCaseSelectedAt tm selects start)
            (effectCaseChoiceAt tm start) := by
        simp [sizeAt, effectFormulaSizeAt, hindex]
      let current := (emitEffectCaseAt tm selects start).effect values
      have hcurrent := emitEffectCaseAt_effect_internal tm selects start values
        hclean
      have hcurrentClean : CaseFormulaClean current := by
        dsimp [current]
        rw [hcurrent]
        exact CaseFormulaClean.updateAvailable values hclean _
      have hcurrentHorizon : current Work.horizon = T := by
        dsimp [current]
        rw [hcurrent]
        simpa [Work.available, Work.horizon] using hhorizon
      have hcurrentAvailable : current Work.available =
          base + prefixSize sizeAt (start + 1) := by
        dsimp [current]
        rw [hcurrent]
        simp only [Function.update_apply, Work.available]
        rw [if_pos True.intro]
        change values Work.available + _ = _
        rw [havailable, hhorizon, ← hsizeAt]
        simp [prefixSize]
        dsimp [sizeAt]
        omega
      have htail := ih (start + 1) current hcurrentClean (by omega)
        hcurrentHorizon hcurrentAvailable
      rw [emitEffectMembersFrom, BinaryRoutine.seq]
      change
        (emitEffectMembersFrom tm selects (start + 1) count).effect current = _
      rw [htail]
      dsimp [current]
      rw [hcurrent]
      funext i
      simp only [Function.update_apply]
      split_ifs
      · congr 2
        all_goals omega
      · rfl

@[simp] theorem emitEffectMembers_effect_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitEffectMembers tm selects).effect values =
      Function.update values Work.available
        (values Work.available + prefixSize
          (effectFormulaSizeAt (transitionCases tm).length k
            (values Work.horizon) (effectCaseSelectedAt tm selects)
            (effectCaseChoiceAt tm)) (transitionCases tm).length) := by
  simpa [emitEffectMembers, prefixSize] using
    emitEffectMembersFrom_effect tm selects 0 (transitionCases tm).length
      (values Work.available) (values Work.horizon) values hclean (by omega)
      rfl (by simp [prefixSize])

private theorem emitEffectMembersFrom_emitted
    (tm : NTM k) (selects : TransitionEffect tm → Bool)
    (start count base T configBase choiceWire : ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (hbound : start + count ≤ (transitionCases tm).length)
    (hhorizon : values Work.horizon = T)
    (hconfigBase : values Work.configBase = configBase)
    (hchoiceWire : values Work.reference₀ = choiceWire)
    (havailable : values Work.available =
      base + prefixSize
        (effectFormulaSizeAt (transitionCases tm).length k T
          (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)) start) :
    (emitEffectMembersFrom tm selects start count).emitted values =
      (indexedGateBlocks count fun offset =>
        effectFormulaCaseBlock (transitionCases tm).length
          (Fintype.card tm.Q) k T configBase choiceWire base
          (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)
          (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
          (effectCaseOutputSymbolIndexAt tm) (effectCaseWorkSymbolIndexAt tm)
          (start + offset)).flatMap CircuitCode.RawGate.encode := by
  induction count generalizing start values with
  | zero =>
      simp [emitEffectMembersFrom, BinaryRoutine.identity,
        BinaryRoutine.emitBits, indexedGateBlocks]
  | succ count ih =>
      let sizeAt := effectFormulaSizeAt (transitionCases tm).length k T
        (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)
      have hindex : start < (transitionCases tm).length := by omega
      have hsizeAt : sizeAt start =
          effectFormulaCaseSize k T
            (effectCaseSelectedAt tm selects start)
            (effectCaseChoiceAt tm start) := by
        simp [sizeAt, effectFormulaSizeAt, hindex]
      have hcaseAvailable : values Work.available =
          effectFormulaCaseAvailable (transitionCases tm).length k
            (values Work.horizon) base (effectCaseSelectedAt tm selects)
            (effectCaseChoiceAt tm) start := by
        rw [hhorizon]
        simpa [effectFormulaCaseAvailable, sizeAt] using havailable
      let current := (emitEffectCaseAt tm selects start).effect values
      have hcurrent := emitEffectCaseAt_effect_internal tm selects start values
        hclean
      have hcurrentClean : CaseFormulaClean current := by
        dsimp [current]
        rw [hcurrent]
        exact CaseFormulaClean.updateAvailable values hclean _
      have hcurrentHorizon : current Work.horizon = T := by
        dsimp [current]
        rw [hcurrent]
        simpa [Work.available, Work.horizon] using hhorizon
      have hcurrentConfigBase : current Work.configBase = configBase := by
        dsimp [current]
        rw [hcurrent]
        simpa [Work.available, Work.configBase] using hconfigBase
      have hcurrentChoiceWire : current Work.reference₀ = choiceWire := by
        dsimp [current]
        rw [hcurrent]
        simpa [Work.available, Work.reference₀] using hchoiceWire
      have hcurrentAvailable : current Work.available =
          base + prefixSize sizeAt (start + 1) := by
        dsimp [current]
        rw [hcurrent]
        simp only [Function.update_apply, Work.available]
        rw [if_pos True.intro]
        change values Work.available + _ = _
        rw [havailable, hhorizon, ← hsizeAt]
        simp [prefixSize]
        dsimp [sizeAt]
        omega
      have htail := ih (start + 1) current hcurrentClean (by omega)
        hcurrentHorizon hcurrentConfigBase hcurrentChoiceWire (by
          simpa [sizeAt] using hcurrentAvailable)
      rw [emitEffectMembersFrom, BinaryRoutine.seq]
      change (emitEffectCaseAt tm selects start).emitted values ++
        (emitEffectMembersFrom tm selects (start + 1) count).emitted current = _
      rw [emitEffectCaseAt_emitted_internal tm selects start base values
        hclean hcaseAvailable, htail]
      rw [hhorizon, hconfigBase, hchoiceWire]
      simp only [indexedGateBlocks, List.flatMap_append, Nat.add_zero]
      congr 1
      apply congrArg (List.flatMap CircuitCode.RawGate.encode)
      apply congrArg (indexedGateBlocks count)
      funext offset
      exact congrArg
        (effectFormulaCaseBlock (transitionCases tm).length
          (Fintype.card tm.Q) k T configBase choiceWire base
          (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)
          (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
          (effectCaseOutputSymbolIndexAt tm) (effectCaseWorkSymbolIndexAt tm))
        (by omega)

@[simp] theorem emitEffectMembers_emitted_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitEffectMembers tm selects).emitted values =
      (effectFormulaCaseGates (transitionCases tm).length
        (Fintype.card tm.Q) k (values Work.horizon)
        (values Work.configBase) (values Work.reference₀)
        (values Work.available) (effectCaseSelectedAt tm selects)
        (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
        (effectCaseInputSymbolIndexAt tm) (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm)).flatMap
          CircuitCode.RawGate.encode := by
  simpa [emitEffectMembers, effectFormulaCaseGates, prefixSize] using
    emitEffectMembersFrom_emitted tm selects 0 (transitionCases tm).length
      (values Work.available) (values Work.horizon) (values Work.configBase)
      (values Work.reference₀) values hclean (by omega) rfl rfl rfl
      (by simp [prefixSize])

theorem prepareEffectCaseSize_sound_internal (workCount : ℕ)
    (selected choiceValue : Bool) :
    (prepareEffectCaseSize workCount selected choiceValue).Sound := by
  cases selected <;> simp only [prepareEffectCaseSize]
  · exact BinaryRoutine.set_sound Work.temporary₃ 1
  · apply BinaryRoutine.seqList_sound
    intro member hmember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
    rcases hmember with hmember | hmember | hmember | hmember
    · subst member
      exact BinaryRoutine.set_sound Work.temporary₃
        (6 * workCount + 16 + caseChoiceLiteralSize choiceValue)
    · subst member
      exact BinaryRoutine.set_sound Work.temporary₂ (4 * (workCount + 2))
    · subst member
      exact BinaryRoutine.mulAdd_sound Work.horizon Work.temporary₂
        Work.temporary₃ Work.multiplyCounter Work.addCounter
    · subst member
      exact BinaryRoutine.clear_sound Work.temporary₂

theorem prepareEffectCaseSize_requires_internal (workCount : ℕ)
    (selected choiceValue : Bool) (values : BinaryValues WorkCount)
    (hmultiply : values Work.multiplyCounter = 0)
    (hadd : values Work.addCounter = 0) :
    (prepareEffectCaseSize workCount selected choiceValue).requires values := by
  cases selected
  · simp [prepareEffectCaseSize, BinaryRoutine.set, BinaryRoutine.seq,
      BinaryRoutine.clear, BinaryRoutine.addConst]
  · simp only [prepareEffectCaseSize, BinaryRoutine.seqList,
      BinaryRoutine.seq, BinaryRoutine.set, BinaryRoutine.clear,
      BinaryRoutine.addConst, BinaryRoutine.mulAdd, BinaryRoutine.identity,
      BinaryRoutine.emitBits, true_and]
    refine ⟨?_, True.intro⟩
    refine ⟨by constructor <;> decide, ?_, ?_⟩
    · simpa [Work.temporary₂, Work.temporary₃,
        Work.multiplyCounter] using hmultiply
    · simpa [Work.temporary₂, Work.temporary₃,
        Work.addCounter] using hadd

@[simp] theorem prepareEffectCaseSize_effect_internal (workCount : ℕ)
    (selected choiceValue : Bool) (values : BinaryValues WorkCount)
    (htemporary₂ : values Work.temporary₂ = 0) :
    (prepareEffectCaseSize workCount selected choiceValue).effect values =
      Function.update
        (Function.update values Work.temporary₃
          (effectFormulaCaseSize workCount (values Work.horizon) selected
            choiceValue))
        Work.temporary₂ 0 := by
  cases selected
  · simp only [prepareEffectCaseSize, BinaryRoutine.set, BinaryRoutine.seq,
      BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
      effectFormulaCaseSize]
    funext i
    by_cases htemporary₃Index : i = Work.temporary₃
    · subst i
      simp [Work.temporary₂, Work.temporary₃]
    by_cases htemporary₂Index : i = Work.temporary₂
    · subst i
      simpa [Work.temporary₂, Work.temporary₃] using htemporary₂
    · simp [htemporary₃Index, htemporary₂Index]
  · have hsize :
        6 * workCount + 16 + caseChoiceLiteralSize choiceValue +
            values Work.horizon * (4 * (workCount + 2)) =
          effectFormulaCaseSize workCount (values Work.horizon) true
            choiceValue := by
      cases choiceValue <;>
        simp [effectFormulaCaseSize, caseFormulaScheduleSize,
          caseFormulaMembersSize, caseFormulaMemberCount, caseReadSize,
          caseChoiceLiteralSize] <;>
        ring
    simp only [prepareEffectCaseSize, BinaryRoutine.seqList,
      BinaryRoutine.seq, BinaryRoutine.set, BinaryRoutine.clear,
      BinaryRoutine.addConst, BinaryRoutine.mulAdd, BinaryRoutine.identity,
      BinaryRoutine.emitBits]
    funext i
    by_cases htemporary₃Index : i = Work.temporary₃
    · subst i
      simpa [Work.horizon, Work.temporary₂, Work.temporary₃] using hsize
    by_cases htemporary₂Index : i = Work.temporary₂
    · subst i
      simp [Work.temporary₂, Work.temporary₃]
    · simp [htemporary₃Index, htemporary₂Index]

@[simp] theorem prepareEffectCaseSize_emitted_internal (workCount : ℕ)
    (selected choiceValue : Bool) (values : BinaryValues WorkCount) :
    (prepareEffectCaseSize workCount selected choiceValue).emitted values = [] := by
  cases selected <;>
    simp [prepareEffectCaseSize, BinaryRoutine.seqList, BinaryRoutine.seq,
      BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
      BinaryRoutine.mulAdd, BinaryRoutine.identity, BinaryRoutine.emitBits]

theorem emitPreviousEffectConnector_sound_internal (workCount : ℕ)
    (selected choiceValue : Bool) :
    (emitPreviousEffectConnector workCount selected choiceValue).Sound := by
  apply BinaryRoutine.seqList_sound
  intro member hmember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
  rcases hmember with hmember | hmember | hmember | hmember
  · subst member
    exact prepareEffectCaseSize_sound_internal workCount selected choiceValue
  · subst member
    exact decrementReferenceBy_sound Work.reference₀ Work.temporary₃
      Work.loop₃
  · subst member
    exact emitReadConnector_sound_for_effect
  · subst member
    exact BinaryRoutine.clear_sound Work.temporary₃

theorem emitPreviousEffectConnector_requires_internal (workCount : ℕ)
    (selected choiceValue : Bool) (values : BinaryValues WorkCount)
    (hclean : EffectConnectorClean values)
    (hsize : effectFormulaCaseSize workCount (values Work.horizon) selected
      choiceValue ≤ values Work.reference₀)
    (havailable : 1 ≤ values Work.available) :
    (emitPreviousEffectConnector workCount selected choiceValue).requires
      values := by
  let afterSize :=
    (prepareEffectCaseSize workCount selected choiceValue).effect values
  have hafterSize : afterSize =
      Function.update
        (Function.update values Work.temporary₃
          (effectFormulaCaseSize workCount (values Work.horizon) selected
            choiceValue)) Work.temporary₂ 0 :=
    prepareEffectCaseSize_effect_internal workCount selected choiceValue values
      hclean.temporary₂
  have hprepare :
      (prepareEffectCaseSize workCount selected choiceValue).requires values :=
    prepareEffectCaseSize_requires_internal workCount selected choiceValue
      values hclean.multiplyCounter hclean.addCounter
  have hloopSize : afterSize Work.loop₃ = 0 := by
    rw [hafterSize]
    simpa [Work.temporary₃, Work.temporary₂, Work.loop₃] using
      hclean.loop₃
  have hsizeValue : afterSize Work.temporary₃ ≤
      afterSize Work.reference₀ := by
    rw [hafterSize]
    simpa [Work.temporary₃, Work.temporary₂, Work.reference₀] using
      hsize
  have hdecrement :
      (decrementReferenceBy Work.reference₀ Work.temporary₃
        Work.loop₃).requires afterSize := by
    rw [decrementReferenceBy_requires]
    exact ⟨⟨by decide, by decide, by decide⟩, hloopSize, hsizeValue⟩
  let afterDecrement :=
    (decrementReferenceBy Work.reference₀ Work.temporary₃
      Work.loop₃).effect afterSize
  have hafterDecrement : afterDecrement =
      Function.update
        (Function.update afterSize Work.reference₀
          (afterSize Work.reference₀ - afterSize Work.temporary₃))
        Work.loop₃ 0 :=
    decrementReferenceBy_effect Work.reference₀ Work.temporary₃
      Work.loop₃ afterSize ⟨by decide, by decide, by decide⟩ hloopSize
  have hconnector : emitReadConnector.requires afterDecrement := by
    apply emitReadConnector_requires_internal
    · rw [hafterDecrement, hafterSize]
      simpa [Work.reference₀, Work.temporary₃, Work.temporary₂,
        Work.loop₃, Work.copyCounter] using hclean.copyCounter
    · rw [hafterDecrement, hafterSize]
      simpa [Work.reference₀, Work.temporary₃, Work.temporary₂,
        Work.loop₃, Work.available] using havailable
    · rw [hafterDecrement, hafterSize]
      simpa [Work.reference₀, Work.temporary₃, Work.temporary₂,
        Work.loop₃, Work.emitCounter] using hclean.emitCounter
  simp only [emitPreviousEffectConnector, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.identity, BinaryRoutine.emitBits]
  exact ⟨hprepare, hdecrement, hconnector, trivial, trivial⟩

@[simp] theorem emitPreviousEffectConnector_effect_internal (workCount : ℕ)
    (selected choiceValue : Bool) (values : BinaryValues WorkCount)
    (hclean : EffectConnectorClean values) :
    (emitPreviousEffectConnector workCount selected choiceValue).effect
        values =
      Function.update
        (Function.update values Work.reference₀
          (values Work.reference₀ -
            effectFormulaCaseSize workCount (values Work.horizon) selected
              choiceValue))
        Work.available (values Work.available + 1) := by
  let afterSize :=
    (prepareEffectCaseSize workCount selected choiceValue).effect values
  let afterDecrement :=
    (decrementReferenceBy Work.reference₀ Work.temporary₃
      Work.loop₃).effect afterSize
  have hafterSize : afterSize =
      Function.update
        (Function.update values Work.temporary₃
          (effectFormulaCaseSize workCount (values Work.horizon) selected
            choiceValue)) Work.temporary₂ 0 :=
    prepareEffectCaseSize_effect_internal workCount selected choiceValue values
      hclean.temporary₂
  have hloopSize : afterSize Work.loop₃ = 0 := by
    rw [hafterSize]
    simpa [Work.temporary₃, Work.temporary₂, Work.loop₃] using
      hclean.loop₃
  have hafterDecrement : afterDecrement =
      Function.update
        (Function.update afterSize Work.reference₀
          (afterSize Work.reference₀ - afterSize Work.temporary₃))
        Work.loop₃ 0 :=
    decrementReferenceBy_effect Work.reference₀ Work.temporary₃
      Work.loop₃ afterSize ⟨by decide, by decide, by decide⟩ hloopSize
  rw [emitPreviousEffectConnector]
  change (BinaryRoutine.clear Work.temporary₃).effect
      (emitReadConnector.effect afterDecrement) = _
  rw [emitReadConnector_effect_internal, hafterDecrement, hafterSize]
  simp only [BinaryRoutine.clear]
  have htemporary₂ : values (24 : Fin WorkCount) = 0 := by
    simpa [Work.temporary₂] using hclean.temporary₂
  have htemporary₃ : values (25 : Fin WorkCount) = 0 := by
    simpa [Work.temporary₃] using hclean.temporary₃
  have hreference₁ : values (8 : Fin WorkCount) = 0 := by
    simpa [Work.reference₁] using hclean.reference₁
  funext i
  simp only [Function.update_apply]
  split_ifs <;>
    simp_all [Work.reference₀, Work.reference₁, Work.temporary₂,
      Work.temporary₃, Work.loop₃, Work.available]

@[simp] theorem emitPreviousEffectConnector_emitted_internal (workCount : ℕ)
    (selected choiceValue : Bool) (values : BinaryValues WorkCount)
    (hclean : EffectConnectorClean values) :
    (emitPreviousEffectConnector workCount selected choiceValue).emitted
        values =
      CircuitCode.RawGate.encode
        { op := .or
          input₀ := values Work.reference₀ -
            effectFormulaCaseSize workCount (values Work.horizon) selected
              choiceValue
          input₁ := values Work.available - 1
          negated₀ := false
          negated₁ := false } := by
  let afterSize :=
    (prepareEffectCaseSize workCount selected choiceValue).effect values
  have hafterSize : afterSize =
      Function.update
        (Function.update values Work.temporary₃
          (effectFormulaCaseSize workCount (values Work.horizon) selected
            choiceValue)) Work.temporary₂ 0 :=
    prepareEffectCaseSize_effect_internal workCount selected choiceValue values
      hclean.temporary₂
  have hloopSize : afterSize Work.loop₃ = 0 := by
    rw [hafterSize]
    simpa [Work.temporary₃, Work.temporary₂, Work.loop₃] using
      hclean.loop₃
  simp only [emitPreviousEffectConnector, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [prepareEffectCaseSize_emitted_internal, decrementReferenceBy_emitted,
    decrementReferenceBy_effect Work.reference₀ Work.temporary₃
      Work.loop₃ afterSize ⟨by decide, by decide, by decide⟩ hloopSize,
    emitReadConnector_emitted_internal, hafterSize]
  simp [BinaryRoutine.clear, Work.reference₀, Work.temporary₃,
    Work.temporary₂, Work.loop₃, Work.available]

private theorem EffectConnectorClean.afterPrevious
    (workCount : ℕ) (selected choiceValue : Bool)
    (values : BinaryValues WorkCount) (hclean : EffectConnectorClean values) :
    EffectConnectorClean
      ((emitPreviousEffectConnector workCount selected choiceValue).effect
        values) := by
  rw [emitPreviousEffectConnector_effect_internal workCount selected
    choiceValue values hclean]
  refine
    { reference₁ := ?_
      loop₃ := ?_
      temporary₂ := ?_
      temporary₃ := ?_
      emitCounter := ?_
      copyCounter := ?_
      multiplyCounter := ?_
      addCounter := ?_ }
  · simpa [Work.reference₀, Work.reference₁, Work.available] using
      hclean.reference₁
  · simpa [Work.reference₀, Work.loop₃, Work.available] using
      hclean.loop₃
  · simpa [Work.reference₀, Work.temporary₂, Work.available] using
      hclean.temporary₂
  · simpa [Work.reference₀, Work.temporary₃, Work.available] using
      hclean.temporary₃
  · simpa [Work.reference₀, Work.emitCounter, Work.available] using
      hclean.emitCounter
  · simpa [Work.reference₀, Work.copyCounter, Work.available] using
      hclean.copyCounter
  · simpa [Work.reference₀, Work.multiplyCounter, Work.available] using
      hclean.multiplyCounter
  · simpa [Work.reference₀, Work.addCounter, Work.available] using
      hclean.addCounter

private theorem effectFormulaCaseSize_pos (workCount T : ℕ)
    (selected choiceValue : Bool) :
    1 ≤ effectFormulaCaseSize workCount T selected choiceValue := by
  cases selected
  · simp [effectFormulaCaseSize]
  · simp [effectFormulaCaseSize, caseFormulaScheduleSize,
      caseFormulaMembersSize, caseFormulaMemberCount, caseReadSize]
    omega

private theorem emitPreviousEffectConnectorsCount_requires
    (tm : NTM k) (selects : TransitionEffect tm → Bool) (count base : ℕ)
    (values : BinaryValues WorkCount) (hclean : EffectConnectorClean values)
    (hcount : count + 1 ≤ (transitionCases tm).length) (hbase : 1 ≤ base)
    (hreference : values Work.reference₀ =
      base + prefixSize
        (effectFormulaSizeAt (transitionCases tm).length k
          (values Work.horizon) (effectCaseSelectedAt tm selects)
          (effectCaseChoiceAt tm)) (count + 1) - 1)
    (havailable : 1 ≤ values Work.available) :
    (emitPreviousEffectConnectorsCount tm selects count).requires values := by
  induction count generalizing values with
  | zero =>
      simp [emitPreviousEffectConnectorsCount, BinaryRoutine.identity,
        BinaryRoutine.emitBits]
  | succ count ih =>
      let selected := effectCaseSelectedAt tm selects (count + 1)
      let choiceValue := effectCaseChoiceAt tm (count + 1)
      let sizeAt := effectFormulaSizeAt (transitionCases tm).length k
        (values Work.horizon) (effectCaseSelectedAt tm selects)
        (effectCaseChoiceAt tm)
      have hindex : count + 1 < (transitionCases tm).length := by omega
      have hsizeAt : sizeAt (count + 1) =
          effectFormulaCaseSize k (values Work.horizon) selected
            choiceValue := by
        simp [sizeAt, effectFormulaSizeAt, selected, choiceValue, hindex]
      have hprefix : prefixSize sizeAt (count + 2) =
          prefixSize sizeAt (count + 1) + sizeAt (count + 1) := by
        simp [prefixSize]
      have hsize : effectFormulaCaseSize k (values Work.horizon) selected
          choiceValue ≤ values Work.reference₀ := by
        rw [hreference]
        change _ ≤ base + prefixSize sizeAt (count + 2) - 1
        rw [hprefix, ← hsizeAt]
        omega
      have hhead := emitPreviousEffectConnector_requires_internal k selected
        choiceValue values hclean hsize havailable
      let current :=
        (emitPreviousEffectConnector k selected choiceValue).effect values
      have hcurrent := emitPreviousEffectConnector_effect_internal k selected
        choiceValue values hclean
      have hcurrentClean := hclean.afterPrevious k selected choiceValue values
      have hhorizon : current Work.horizon = values Work.horizon := by
        dsimp [current]
        rw [hcurrent]
        simp [Work.reference₀, Work.available, Work.horizon]
      have hcurrentReference : current Work.reference₀ =
          base + prefixSize sizeAt (count + 1) - 1 := by
        dsimp [current]
        rw [hcurrent]
        simp only [Function.update_apply, Work.reference₀, Work.available]
        rw [if_neg (by decide), if_pos True.intro]
        change values Work.reference₀ - _ = _
        rw [hreference]
        change (base + prefixSize sizeAt (count + 2) - 1) - _ = _
        rw [hprefix, ← hsizeAt]
        omega
      have hcurrentAvailable : 1 ≤ current Work.available := by
        dsimp [current]
        rw [hcurrent]
        simp [Work.reference₀, Work.available]
      rw [emitPreviousEffectConnectorsCount, BinaryRoutine.seq]
      refine ⟨hhead, ih current hcurrentClean (by omega) ?_
        hcurrentAvailable⟩
      rw [hhorizon]
      exact hcurrentReference

private theorem emitPreviousEffectConnectorsCount_effect
    (tm : NTM k) (selects : TransitionEffect tm → Bool) (count base : ℕ)
    (values : BinaryValues WorkCount) (hclean : EffectConnectorClean values)
    (hcount : count + 1 ≤ (transitionCases tm).length) (hbase : 1 ≤ base)
    (hreference : values Work.reference₀ =
      base + prefixSize
        (effectFormulaSizeAt (transitionCases tm).length k
          (values Work.horizon) (effectCaseSelectedAt tm selects)
          (effectCaseChoiceAt tm)) (count + 1) - 1) :
    (emitPreviousEffectConnectorsCount tm selects count).effect values =
      Function.update
        (Function.update values Work.reference₀
          (base + effectFormulaSizeAt (transitionCases tm).length k
            (values Work.horizon) (effectCaseSelectedAt tm selects)
            (effectCaseChoiceAt tm) 0 - 1))
        Work.available (values Work.available + count) := by
  induction count generalizing values with
  | zero =>
      have hreferenceZero : values Work.reference₀ =
          base + effectFormulaSizeAt (transitionCases tm).length k
            (values Work.horizon) (effectCaseSelectedAt tm selects)
            (effectCaseChoiceAt tm) 0 - 1 := by
        simpa [prefixSize] using hreference
      rw [emitPreviousEffectConnectorsCount]
      change values = _
      funext i
      by_cases havailableIndex : i = Work.available
      · subst i
        simp [Work.reference₀, Work.available]
      by_cases hreferenceIndex : i = Work.reference₀
      · subst i
        simpa [Work.reference₀, Work.available] using hreferenceZero
      · simp [havailableIndex, hreferenceIndex]
  | succ count ih =>
      let selected := effectCaseSelectedAt tm selects (count + 1)
      let choiceValue := effectCaseChoiceAt tm (count + 1)
      let sizeAt := effectFormulaSizeAt (transitionCases tm).length k
        (values Work.horizon) (effectCaseSelectedAt tm selects)
        (effectCaseChoiceAt tm)
      have hindex : count + 1 < (transitionCases tm).length := by omega
      have hsizeAt : sizeAt (count + 1) =
          effectFormulaCaseSize k (values Work.horizon) selected
            choiceValue := by
        simp [sizeAt, effectFormulaSizeAt, selected, choiceValue, hindex]
      have hprefix : prefixSize sizeAt (count + 2) =
          prefixSize sizeAt (count + 1) + sizeAt (count + 1) := by
        simp [prefixSize]
      let current :=
        (emitPreviousEffectConnector k selected choiceValue).effect values
      have hcurrent := emitPreviousEffectConnector_effect_internal k selected
        choiceValue values hclean
      have hcurrentClean := hclean.afterPrevious k selected choiceValue values
      have hhorizon : current Work.horizon = values Work.horizon := by
        dsimp [current]
        rw [hcurrent]
        simp [Work.reference₀, Work.available, Work.horizon]
      have hcurrentReference : current Work.reference₀ =
          base + prefixSize sizeAt (count + 1) - 1 := by
        dsimp [current]
        rw [hcurrent]
        simp only [Function.update_apply, Work.reference₀, Work.available]
        rw [if_neg (by decide), if_pos True.intro]
        change values Work.reference₀ - _ = _
        rw [hreference]
        change (base + prefixSize sizeAt (count + 2) - 1) - _ = _
        rw [hprefix, ← hsizeAt]
        omega
      have htail := ih current hcurrentClean (by omega) (by
        rw [hhorizon]
        exact hcurrentReference)
      rw [emitPreviousEffectConnectorsCount, BinaryRoutine.seq]
      change
        (emitPreviousEffectConnectorsCount tm selects count).effect current = _
      rw [htail]
      rw [hhorizon]
      dsimp [current]
      rw [hcurrent]
      funext i
      simp only [Function.update_apply]
      split_ifs <;>
        simp_all [Work.reference₀, Work.available, Work.horizon]
      all_goals omega

private theorem emitPreviousEffectConnectorsCount_emitted
    (tm : NTM k) (selects : TransitionEffect tm → Bool)
    (count nextRank base T : ℕ) (values : BinaryValues WorkCount)
    (hclean : EffectConnectorClean values)
    (hranks : nextRank + count = (transitionCases tm).length)
    (hnextRank : 1 ≤ nextRank) (hbase : 1 ≤ base)
    (hhorizon : values Work.horizon = T)
    (havailable : values Work.available =
      base + prefixSize
        (effectFormulaSizeAt (transitionCases tm).length k T
          (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm))
        (transitionCases tm).length + nextRank + 1)
    (hreference : values Work.reference₀ =
      base + prefixSize
        (effectFormulaSizeAt (transitionCases tm).length k T
          (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm))
        (count + 1) - 1) :
    (emitPreviousEffectConnectorsCount tm selects count).emitted values =
      ((List.range count).map fun offset =>
        indexedRightFoldConnector .or base (transitionCases tm).length
          (effectFormulaSizeAt (transitionCases tm).length k T
            (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm))
          (nextRank + offset)).flatMap CircuitCode.RawGate.encode := by
  induction count generalizing nextRank values with
  | zero =>
      simp [emitPreviousEffectConnectorsCount, BinaryRoutine.identity,
        BinaryRoutine.emitBits]
  | succ count ih =>
      let selected := effectCaseSelectedAt tm selects (count + 1)
      let choiceValue := effectCaseChoiceAt tm (count + 1)
      let sizeAt := effectFormulaSizeAt (transitionCases tm).length k T
        (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)
      have hindex : count + 1 < (transitionCases tm).length := by omega
      have hsizeAt : sizeAt (count + 1) =
          effectFormulaCaseSize k T selected choiceValue := by
        simp [sizeAt, effectFormulaSizeAt, selected, choiceValue, hindex]
      have hprefix : prefixSize sizeAt (count + 2) =
          prefixSize sizeAt (count + 1) + sizeAt (count + 1) := by
        simp [prefixSize]
      let current :=
        (emitPreviousEffectConnector k selected choiceValue).effect values
      have hcurrent := emitPreviousEffectConnector_effect_internal k selected
        choiceValue values hclean
      have hcurrentClean := hclean.afterPrevious k selected choiceValue values
      have hcurrentHorizon : current Work.horizon = T := by
        dsimp [current]
        rw [hcurrent]
        simpa [Work.reference₀, Work.available, Work.horizon] using hhorizon
      have hcurrentAvailable : current Work.available =
          base + prefixSize sizeAt (transitionCases tm).length +
            (nextRank + 1) + 1 := by
        dsimp [current]
        rw [hcurrent]
        simp only [Function.update_apply, Work.reference₀, Work.available]
        rw [if_pos True.intro]
        change values Work.available + 1 = _
        rw [havailable]
        dsimp [sizeAt]
        omega
      have hcurrentReference : current Work.reference₀ =
          base + prefixSize sizeAt (count + 1) - 1 := by
        dsimp [current]
        rw [hcurrent]
        simp only [Function.update_apply, Work.reference₀, Work.available]
        rw [if_neg (by decide), if_pos True.intro]
        change values Work.reference₀ - _ = _
        rw [hreference, hhorizon]
        change (base + prefixSize sizeAt (count + 2) - 1) - _ = _
        rw [hprefix, ← hsizeAt]
        omega
      have htail := ih (nextRank + 1) current hcurrentClean (by omega)
        (by omega) hcurrentHorizon hcurrentAvailable hcurrentReference
      rw [emitPreviousEffectConnectorsCount, BinaryRoutine.seq]
      change
        (emitPreviousEffectConnector k selected choiceValue).emitted values ++
          (emitPreviousEffectConnectorsCount tm selects count).emitted current =
            _
      rw [emitPreviousEffectConnector_emitted_internal k selected choiceValue
        values hclean, htail]
      simp only [List.range_succ_eq_map, List.map_cons, List.map_map,
        List.flatMap_cons]
      have hgate :
          { op := AndOrOp.or
            input₀ := values Work.reference₀ -
              effectFormulaCaseSize k (values Work.horizon) selected
                choiceValue
            input₁ := values Work.available - 1
            negated₀ := false
            negated₁ := false } =
          indexedRightFoldConnector .or base (transitionCases tm).length
            sizeAt nextRank := by
        have hmember :
            (transitionCases tm).length - nextRank - 1 = count := by
          omega
        have hinput₀ : values Work.reference₀ -
              effectFormulaCaseSize k (values Work.horizon) selected
                choiceValue =
            base + prefixSize sizeAt (count + 1) - 1 := by
          rw [hhorizon, hreference]
          change (base + prefixSize sizeAt (count + 2) - 1) - _ = _
          rw [← hsizeAt, hprefix]
          omega
        have hinput₁ : values Work.available - 1 =
            base + prefixSize sizeAt (transitionCases tm).length +
              nextRank := by
          rw [havailable]
          dsimp [sizeAt]
        rw [hinput₀, hinput₁]
        unfold indexedRightFoldConnector reverseMember
        dsimp only
        rw [hmember]
      rw [hgate]
      congr 1
      apply congrArg (List.flatMap CircuitCode.RawGate.encode)
      apply List.map_congr_left
      intro offset hoffset
      exact congrArg
        (indexedRightFoldConnector .or base (transitionCases tm).length
          sizeAt) (by omega)

private theorem emitPreviousEffectConnectorsCount_sound
    (tm : NTM k) (selects : TransitionEffect tm → Bool) (count : ℕ) :
    (emitPreviousEffectConnectorsCount tm selects count).Sound := by
  induction count with
  | zero => exact BinaryRoutine.identity_sound
  | succ count ih =>
      exact
        (emitPreviousEffectConnector_sound_internal k
          (effectCaseSelectedAt tm selects (count + 1))
          (effectCaseChoiceAt tm (count + 1))).seq ih

theorem emitPreviousEffectConnectors_sound_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool) :
    (emitPreviousEffectConnectors tm selects).Sound :=
  emitPreviousEffectConnectorsCount_sound tm selects
    ((transitionCases tm).length - 1)

theorem emitEffectConnectors_requires_internal
    (tm : NTM k) (selects : TransitionEffect tm → Bool)
    (base T : ℕ) (values : BinaryValues WorkCount)
    (hclean : CaseFormulaClean values) (hbase : 1 ≤ base)
    (hhorizon : values Work.horizon = T)
    (havailable : values Work.available =
      base + prefixSize
        (effectFormulaSizeAt (transitionCases tm).length k T
          (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm))
        (transitionCases tm).length + 1) :
    (emitEffectConnectors tm selects).requires values := by
  rw [emitEffectConnectors]
  split_ifs with hempty
  · simp [BinaryRoutine.identity, BinaryRoutine.emitBits]
  · have hlength : (transitionCases tm).length ≠ 0 := by
      intro hzero
      exact hempty (List.isEmpty_iff_length_eq_zero.mpr hzero)
    have hlengthPos : 0 < (transitionCases tm).length := by omega
    let sizeAt := effectFormulaSizeAt (transitionCases tm).length k T
      (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)
    have hlastIndex : (transitionCases tm).length - 1 <
        (transitionCases tm).length := by omega
    have hlastSize : 1 ≤ sizeAt ((transitionCases tm).length - 1) := by
      rw [show sizeAt ((transitionCases tm).length - 1) =
        effectFormulaCaseSize k T
          (effectCaseSelectedAt tm selects
            ((transitionCases tm).length - 1))
          (effectCaseChoiceAt tm ((transitionCases tm).length - 1)) by
          simp [sizeAt, effectFormulaSizeAt, hlastIndex]]
      exact effectFormulaCaseSize_pos k T _ _
    have hprefixPos : 1 ≤
        prefixSize sizeAt (transitionCases tm).length := by
      obtain ⟨caseCount, hcaseCount⟩ := Nat.exists_eq_succ_of_ne_zero hlength
      rw [hcaseCount, prefixSize_succ]
      have hlastSize' : 1 ≤ sizeAt caseCount := by
        simpa [hcaseCount] using hlastSize
      omega
    have havailableTwo : 2 ≤ values Work.available := by
      rw [havailable]
      change 2 ≤ base + prefixSize sizeAt (transitionCases tm).length + 1
      omega
    have hprepare := (prepareRecentReference_requires Work.reference₀ 2
      values (by decide) (by decide) (by decide)).2
        ⟨hclean.copyCounter, havailableTwo⟩
    let prepared :=
      (prepareRecentReference Work.reference₀ 2).effect values
    have hprepared : prepared = Function.update values Work.reference₀
        (values Work.available - 2) :=
      prepareRecentReference_effect Work.reference₀ 2 values
    have hpreparedClean : EffectConnectorClean prepared := by
      rw [hprepared]
      exact EffectConnectorClean.updateReference₀ values
        hclean.effectConnectorClean _
    have hinitial : emitReadConnector.requires prepared := by
      apply emitReadConnector_requires_internal
      · rw [hprepared]
        simpa [Work.reference₀, Work.copyCounter] using hclean.copyCounter
      · rw [hprepared]
        simpa [Work.reference₀, Work.available] using
          show 1 ≤ values Work.available by omega
      · rw [hprepared]
        simpa [Work.reference₀, Work.emitCounter] using hclean.emitCounter
    let current := emitReadConnector.effect prepared
    have hcurrentClean : EffectConnectorClean current :=
      hpreparedClean.afterReadConnector prepared
    have hcurrentHorizon : current Work.horizon = T := by
      dsimp [current]
      rw [emitReadConnector_effect_internal, hprepared]
      simpa [Work.reference₀, Work.available, Work.reference₁,
        Work.horizon] using hhorizon
    have hcurrentReference : current Work.reference₀ =
        base + prefixSize sizeAt (transitionCases tm).length - 1 := by
      dsimp [current]
      rw [emitReadConnector_effect_internal, hprepared]
      simp only [Function.update_apply, Work.available, Work.reference₀,
        Work.reference₁]
      rw [if_neg (by decide), if_neg (by decide), if_pos True.intro]
      change values Work.available - 2 = _
      rw [havailable]
      dsimp [sizeAt]
      omega
    have hcurrentAvailable : 1 ≤ current Work.available := by
      dsimp [current]
      rw [emitReadConnector_effect_internal, hprepared]
      simp [Work.reference₀, Work.available, Work.reference₁]
    have hprevious :
        (emitPreviousEffectConnectors tm selects).requires current := by
      rw [emitPreviousEffectConnectors]
      apply emitPreviousEffectConnectorsCount_requires tm selects
        ((transitionCases tm).length - 1) base current hcurrentClean
        (by omega) hbase
      · rw [show (transitionCases tm).length - 1 + 1 =
          (transitionCases tm).length by omega, hcurrentHorizon]
        simpa [sizeAt] using hcurrentReference
      · exact hcurrentAvailable
    simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
      BinaryRoutine.identity, BinaryRoutine.emitBits]
    exact ⟨hprepare, hinitial, hprevious, trivial, trivial⟩

theorem emitEffectConnectors_effect_internal
    (tm : NTM k) (selects : TransitionEffect tm → Bool)
    (base T : ℕ) (values : BinaryValues WorkCount)
    (hclean : CaseFormulaClean values) (hbase : 1 ≤ base)
    (hhorizon : values Work.horizon = T)
    (havailable : values Work.available =
      base + prefixSize
        (effectFormulaSizeAt (transitionCases tm).length k T
          (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm))
        (transitionCases tm).length + 1) :
    (emitEffectConnectors tm selects).effect values =
      Function.update values Work.available
        (values Work.available + (transitionCases tm).length) := by
  rw [emitEffectConnectors]
  split_ifs with hempty
  · have hlength : (transitionCases tm).length = 0 :=
      List.isEmpty_iff_length_eq_zero.mp hempty
    simp [BinaryRoutine.identity, BinaryRoutine.emitBits, hlength]
  · have hlength : (transitionCases tm).length ≠ 0 := by
      intro hzero
      exact hempty (List.isEmpty_iff_length_eq_zero.mpr hzero)
    have hlengthPos : 0 < (transitionCases tm).length := by omega
    let sizeAt := effectFormulaSizeAt (transitionCases tm).length k T
      (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)
    let prepared :=
      (prepareRecentReference Work.reference₀ 2).effect values
    have hprepared : prepared = Function.update values Work.reference₀
        (values Work.available - 2) :=
      prepareRecentReference_effect Work.reference₀ 2 values
    have hpreparedClean : EffectConnectorClean prepared := by
      rw [hprepared]
      exact EffectConnectorClean.updateReference₀ values
        hclean.effectConnectorClean _
    let current := emitReadConnector.effect prepared
    have hcurrentClean : EffectConnectorClean current :=
      hpreparedClean.afterReadConnector prepared
    have hcurrentHorizon : current Work.horizon = T := by
      dsimp [current]
      rw [emitReadConnector_effect_internal, hprepared]
      simpa [Work.reference₀, Work.available, Work.reference₁,
        Work.horizon] using hhorizon
    have hcurrentReference : current Work.reference₀ =
        base + prefixSize sizeAt (transitionCases tm).length - 1 := by
      dsimp [current]
      rw [emitReadConnector_effect_internal, hprepared]
      simp only [Function.update_apply, Work.available, Work.reference₀,
        Work.reference₁]
      rw [if_neg (by decide), if_neg (by decide), if_pos True.intro]
      change values Work.available - 2 = _
      rw [havailable]
      dsimp [sizeAt]
      omega
    have hprevious := emitPreviousEffectConnectorsCount_effect tm selects
      ((transitionCases tm).length - 1) base current hcurrentClean
      (by omega) hbase (by
        rw [show (transitionCases tm).length - 1 + 1 =
          (transitionCases tm).length by omega, hcurrentHorizon]
        simpa [sizeAt] using hcurrentReference)
    simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
      BinaryRoutine.identity, BinaryRoutine.emitBits]
    change (BinaryRoutine.clear Work.reference₀).effect
      ((emitPreviousEffectConnectors tm selects).effect current) = _
    rw [emitPreviousEffectConnectors, hprevious]
    dsimp [current]
    rw [emitReadConnector_effect_internal, hprepared]
    simp only [BinaryRoutine.clear]
    have hreference₀ : values (7 : Fin WorkCount) = 0 := by
      simpa [Work.reference₀] using hclean.reference₀
    have hreference₁ : values (8 : Fin WorkCount) = 0 := by
      simpa [Work.reference₁] using hclean.reference₁
    funext i
    simp only [Function.update_apply]
    split_ifs <;>
      simp_all [Work.reference₀, Work.reference₁, Work.available,
        sizeAt]
    all_goals omega

theorem emitEffectConnectors_emitted_internal
    (tm : NTM k) (selects : TransitionEffect tm → Bool)
    (base T : ℕ) (values : BinaryValues WorkCount)
    (hclean : CaseFormulaClean values) (hbase : 1 ≤ base)
    (hhorizon : values Work.horizon = T)
    (havailable : values Work.available =
      base + prefixSize
        (effectFormulaSizeAt (transitionCases tm).length k T
          (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm))
        (transitionCases tm).length + 1) :
    (emitEffectConnectors tm selects).emitted values =
      (indexedRightFoldConnectors .or base (transitionCases tm).length
        (effectFormulaSizeAt (transitionCases tm).length k T
          (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm))).flatMap
        CircuitCode.RawGate.encode := by
  rw [emitEffectConnectors]
  split_ifs with hempty
  · have hlength : (transitionCases tm).length = 0 :=
      List.isEmpty_iff_length_eq_zero.mp hempty
    simp [BinaryRoutine.identity, BinaryRoutine.emitBits,
      indexedRightFoldConnectors, hlength]
  · have hlength : (transitionCases tm).length ≠ 0 := by
      intro hzero
      exact hempty (List.isEmpty_iff_length_eq_zero.mpr hzero)
    have hlengthPos : 0 < (transitionCases tm).length := by omega
    let sizeAt := effectFormulaSizeAt (transitionCases tm).length k T
      (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)
    let prepared :=
      (prepareRecentReference Work.reference₀ 2).effect values
    have hprepared : prepared = Function.update values Work.reference₀
        (values Work.available - 2) :=
      prepareRecentReference_effect Work.reference₀ 2 values
    have hpreparedClean : EffectConnectorClean prepared := by
      rw [hprepared]
      exact EffectConnectorClean.updateReference₀ values
        hclean.effectConnectorClean _
    let current := emitReadConnector.effect prepared
    have hcurrentClean : EffectConnectorClean current :=
      hpreparedClean.afterReadConnector prepared
    have hcurrentHorizon : current Work.horizon = T := by
      dsimp [current]
      rw [emitReadConnector_effect_internal, hprepared]
      simpa [Work.reference₀, Work.available, Work.reference₁,
        Work.horizon] using hhorizon
    have hcurrentAvailable : current Work.available =
        base + prefixSize sizeAt (transitionCases tm).length + 1 + 1 := by
      dsimp [current]
      rw [emitReadConnector_effect_internal, hprepared]
      simp only [Function.update_apply, Work.available]
      rw [if_pos True.intro]
      change values Work.available + 1 = _
      rw [havailable]
    have hcurrentReference : current Work.reference₀ =
        base + prefixSize sizeAt (transitionCases tm).length - 1 := by
      dsimp [current]
      rw [emitReadConnector_effect_internal, hprepared]
      simp only [Function.update_apply, Work.available, Work.reference₀,
        Work.reference₁]
      rw [if_neg (by decide), if_neg (by decide), if_pos True.intro]
      change values Work.available - 2 = _
      rw [havailable]
      dsimp [sizeAt]
      omega
    have hprevious := emitPreviousEffectConnectorsCount_emitted tm selects
      ((transitionCases tm).length - 1) 1 base T current hcurrentClean
      (by omega) (by omega) hbase hcurrentHorizon hcurrentAvailable (by
        rw [show (transitionCases tm).length - 1 + 1 =
          (transitionCases tm).length by omega]
        simpa [sizeAt] using hcurrentReference)
    have hinitialGate :
        ({ op := AndOrOp.or
           input₀ := prepared Work.reference₀
           input₁ := prepared Work.available - 1
           negated₀ := false
           negated₁ := false } : CircuitCode.RawGate) =
          indexedRightFoldConnector .or base (transitionCases tm).length
            sizeAt 0 := by
      have hmember : (transitionCases tm).length - 0 - 1 + 1 =
          (transitionCases tm).length := by omega
      have hinput₀ : prepared Work.reference₀ =
          base + prefixSize sizeAt (transitionCases tm).length - 1 := by
        rw [hprepared]
        simp only [Function.update_apply, Work.reference₀]
        rw [if_pos True.intro]
        rw [havailable]
        dsimp [sizeAt]
        omega
      have hinput₁ : prepared Work.available - 1 =
          base + prefixSize sizeAt (transitionCases tm).length := by
        rw [hprepared]
        simp only [Function.update_apply, Work.reference₀, Work.available]
        rw [if_neg (by decide)]
        change values Work.available - 1 = _
        rw [havailable]
        dsimp [sizeAt]
      rw [hinput₀, hinput₁]
      unfold indexedRightFoldConnector reverseMember
      dsimp only
      rw [hmember]
      simp
    simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
      BinaryRoutine.identity, BinaryRoutine.emitBits,
      prepareRecentReference_emitted, BinaryRoutine.clear,
      List.nil_append, List.append_nil]
    change emitReadConnector.emitted prepared ++
      (emitPreviousEffectConnectors tm selects).emitted current = _
    rw [emitReadConnector_emitted_internal, emitPreviousEffectConnectors,
      hprevious, hinitialGate]
    unfold indexedRightFoldConnectors
    obtain ⟨caseCount, hcaseCount⟩ := Nat.exists_eq_succ_of_ne_zero hlength
    rw [hcaseCount, Nat.add_one_sub_one, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.flatMap_cons]
    dsimp [sizeAt]
    rw [hcaseCount]
    congr 1
    apply congrArg (List.flatMap CircuitCode.RawGate.encode)
    apply List.map_congr_left
    intro rank _hrank
    exact congrArg
      (indexedRightFoldConnector .or base (caseCount + 1)
        (effectFormulaSizeAt (caseCount + 1) k T
          (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)))
      (show 1 + rank = Nat.succ rank by omega)

theorem emitEffectConnectors_sound_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool) :
    (emitEffectConnectors tm selects).Sound := by
  rw [emitEffectConnectors]
  split_ifs
  · exact BinaryRoutine.identity_sound
  · apply BinaryRoutine.seqList_sound
    intro member hmember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
    rcases hmember with hmember | hmember | hmember | hmember
    · subst member
      exact prepareRecentReference_sound Work.reference₀ 2
    · subst member
      exact emitReadConnector_sound_for_effect
    · subst member
      exact emitPreviousEffectConnectors_sound_internal tm selects
    · subst member
      exact BinaryRoutine.clear_sound Work.reference₀

theorem emitEffectFormula_sound_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool) :
    (emitEffectFormula tm selects).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil,
    or_false] at hroutine
  rcases hroutine with hroutine | hroutine | hroutine
  · subst routine
    exact emitEffectMembers_sound_internal tm selects
  · subst routine
    exact emitConstantGate_sound_internal false
  · subst routine
    exact emitEffectConnectors_sound_internal tm selects

theorem emitEffectFormula_requires_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (havailable : 1 ≤ values Work.available) :
    (emitEffectFormula tm selects).requires values := by
  let afterMembers := (emitEffectMembers tm selects).effect values
  have hafterMembers : afterMembers = Function.update values Work.available
      (values Work.available + prefixSize
        (effectFormulaSizeAt (transitionCases tm).length k
          (values Work.horizon) (effectCaseSelectedAt tm selects)
          (effectCaseChoiceAt tm)) (transitionCases tm).length) :=
    emitEffectMembers_effect_internal tm selects values hclean
  have hafterMembersClean : CaseFormulaClean afterMembers := by
    rw [hafterMembers]
    exact CaseFormulaClean.updateAvailable values hclean _
  let afterIdentity := (emitConstantGate false).effect afterMembers
  have hafterIdentity : afterIdentity = Function.update afterMembers
      Work.available (afterMembers Work.available + 1) :=
    emitConstantGate_effect_internal false afterMembers
  have hafterIdentityClean : CaseFormulaClean afterIdentity := by
    rw [hafterIdentity]
    exact CaseFormulaClean.updateAvailable afterMembers hafterMembersClean _
  have hidentityRequires : (emitConstantGate false).requires afterMembers :=
    emitConstantGate_requires_internal false afterMembers
      hafterMembersClean.emitCounter
  have hconnectorsRequires :
      (emitEffectConnectors tm selects).requires afterIdentity := by
    apply emitEffectConnectors_requires_internal tm selects
      (values Work.available) (values Work.horizon) afterIdentity
      hafterIdentityClean havailable
    · rw [hafterIdentity, hafterMembers]
      simp [Work.available, Work.horizon]
    · rw [hafterIdentity, hafterMembers]
      simp [Work.available]
  simp only [emitEffectFormula, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  exact ⟨emitEffectMembers_requires_internal tm selects values hclean,
    hidentityRequires, hconnectorsRequires, trivial⟩

theorem emitEffectFormula_effect_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (havailable : 1 ≤ values Work.available) :
    (emitEffectFormula tm selects).effect values =
      Function.update values Work.available
        (values Work.available +
          effectFormulaScheduleSize (transitionCases tm).length k
            (values Work.horizon) (effectCaseSelectedAt tm selects)
            (effectCaseChoiceAt tm)) := by
  let afterMembers := (emitEffectMembers tm selects).effect values
  have hafterMembers : afterMembers = Function.update values Work.available
      (values Work.available + prefixSize
        (effectFormulaSizeAt (transitionCases tm).length k
          (values Work.horizon) (effectCaseSelectedAt tm selects)
          (effectCaseChoiceAt tm)) (transitionCases tm).length) :=
    emitEffectMembers_effect_internal tm selects values hclean
  have hafterMembersClean : CaseFormulaClean afterMembers := by
    rw [hafterMembers]
    exact CaseFormulaClean.updateAvailable values hclean _
  let afterIdentity := (emitConstantGate false).effect afterMembers
  have hafterIdentity : afterIdentity = Function.update afterMembers
      Work.available (afterMembers Work.available + 1) :=
    emitConstantGate_effect_internal false afterMembers
  have hafterIdentityClean : CaseFormulaClean afterIdentity := by
    rw [hafterIdentity]
    exact CaseFormulaClean.updateAvailable afterMembers hafterMembersClean _
  have hconnectors := emitEffectConnectors_effect_internal tm selects
    (values Work.available) (values Work.horizon) afterIdentity
    hafterIdentityClean havailable (by
      rw [hafterIdentity, hafterMembers]
      simp [Work.available, Work.horizon]) (by
      rw [hafterIdentity, hafterMembers]
      simp [Work.available])
  simp only [emitEffectFormula, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  change (emitEffectConnectors tm selects).effect afterIdentity = _
  rw [hconnectors, hafterIdentity, hafterMembers]
  funext i
  simp only [effectFormulaScheduleSize, Function.update_apply]
  split_ifs <;> simp_all [Work.available]
  all_goals omega

theorem emitEffectFormula_emitted_internal (tm : NTM k)
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
          CircuitCode.RawGate.encode := by
  let afterMembers := (emitEffectMembers tm selects).effect values
  have hafterMembers : afterMembers = Function.update values Work.available
      (values Work.available + prefixSize
        (effectFormulaSizeAt (transitionCases tm).length k
          (values Work.horizon) (effectCaseSelectedAt tm selects)
          (effectCaseChoiceAt tm)) (transitionCases tm).length) :=
    emitEffectMembers_effect_internal tm selects values hclean
  have hafterMembersClean : CaseFormulaClean afterMembers := by
    rw [hafterMembers]
    exact CaseFormulaClean.updateAvailable values hclean _
  let afterIdentity := (emitConstantGate false).effect afterMembers
  have hafterIdentity : afterIdentity = Function.update afterMembers
      Work.available (afterMembers Work.available + 1) :=
    emitConstantGate_effect_internal false afterMembers
  have hafterIdentityClean : CaseFormulaClean afterIdentity := by
    rw [hafterIdentity]
    exact CaseFormulaClean.updateAvailable afterMembers hafterMembersClean _
  have hidentityReference : afterMembers Work.reference₀ = 0 := by
    rw [hafterMembers]
    simpa [Work.available, Work.reference₀] using hclean.reference₀
  have hconnectors := emitEffectConnectors_emitted_internal tm selects
    (values Work.available) (values Work.horizon) afterIdentity
    hafterIdentityClean havailable (by
      rw [hafterIdentity, hafterMembers]
      simp [Work.available, Work.horizon]) (by
      rw [hafterIdentity, hafterMembers]
      simp [Work.available])
  simp only [emitEffectFormula, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [emitEffectMembers_emitted_internal tm selects values hclean,
    emitConstantGate_emitted_internal false afterMembers hidentityReference,
    hconnectors]
  unfold effectFormulaSchedule
  simp only [directInitConstant, List.flatMap_append,
    List.flatMap_singleton]
  simp [List.append_assoc]

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
