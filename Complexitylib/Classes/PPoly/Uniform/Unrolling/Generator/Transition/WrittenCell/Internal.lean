/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Initialization
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Offset
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Primitive
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Effect.Internal
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Read
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.WrittenCell.Defs
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.WrittenCell
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Arithmetic
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.List

/-!
# Direct-unrolling written-cell generator -- proof internals

This dependency-independent layer verifies the bounded numeric head test used
on both sides of a written-cell formula. The enclosing effect-formula proof is
intentionally deferred until that generator's public contracts are available.
-/

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

theorem WrittenCellFormulaClean.headAtCurrentCellClean_internal
    {values : BinaryValues WorkCount}
    (hclean : WrittenCellFormulaClean values) :
    HeadAtCurrentCellClean values := by
  refine
    { loop₃ := ?_
      temporary₃ := ?_
      reference₀ := ?_
      emitCounter := ?_
      copyCounter := ?_
      multiplyCounter := ?_
      addCounter := ?_
      temporary₀ := ?_ }
  · simpa [Work.position, Work.loop₃] using hclean.caseClean.loop₃
  · simpa [Work.position, Work.temporary₃] using
      hclean.caseClean.temporary₃
  · simpa [Work.position, Work.reference₀] using
      hclean.caseClean.reference₀
  · simpa [Work.position, Work.emitCounter] using
      hclean.caseClean.emitCounter
  · simpa [Work.position, Work.copyCounter] using
      hclean.caseClean.copyCounter
  · simpa [Work.position, Work.multiplyCounter] using
      hclean.caseClean.multiplyCounter
  · simpa [Work.position, Work.addCounter] using hclean.caseClean.addCounter
  · simpa [Work.position, Work.temporary₀] using
      hclean.caseClean.temporary₀

theorem emitHeadAtCurrentCellGate_sound_internal (stateCount : ℕ) :
    (emitHeadAtCurrentCellGate stateCount).Sound :=
  (emitConstantGate_sound false).branchZero
    (emitHeadReference_sound stateCount false) Work.temporary₃

theorem emitHeadAtCurrentCellGate_requires_internal (stateCount : ℕ)
    (values : BinaryValues WorkCount)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0)
    (hemit : values Work.emitCounter = 0) :
    (emitHeadAtCurrentCellGate stateCount).requires values := by
  by_cases hzero : values Work.temporary₃ = 0
  · simp only [emitHeadAtCurrentCellGate, BinaryRoutine.branchZero, hzero,
      if_true]
    exact emitConstantGate_requires_internal false values hemit
  · simp only [emitHeadAtCurrentCellGate, BinaryRoutine.branchZero, hzero,
      if_false]
    exact emitHeadReference_requires stateCount false values hadd hmultiply
      hemit

@[simp] theorem emitHeadAtCurrentCellGate_effect_internal (stateCount : ℕ)
    (values : BinaryValues WorkCount)
    (htemporary : values Work.temporary₀ = 0)
    (hreference : values Work.reference₀ = 0) :
    (emitHeadAtCurrentCellGate stateCount).effect values =
      Function.update values Work.available (values Work.available + 1) := by
  by_cases hzero : values Work.temporary₃ = 0
  · simp [emitHeadAtCurrentCellGate, BinaryRoutine.branchZero, hzero,
      emitConstantGate, BinaryRoutine.emitRawGateStep]
  · rw [emitHeadAtCurrentCellGate, BinaryRoutine.branchZero]
    simp only [hzero, if_false, emitHeadReference_effect]
    funext i
    simp only [Function.update_apply]
    split_ifs <;>
      simp_all [Work.temporary₀, Work.reference₀, Work.available]

@[simp] theorem emitHeadAtCurrentCellGate_emitted_internal (stateCount : ℕ)
    (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0) :
    (emitHeadAtCurrentCellGate stateCount).emitted values =
      CircuitCode.RawGate.encode
        (if values Work.temporary₃ = 0 then
          CircuitCode.RawGate.constant 0 false
        else
          CircuitCode.RawGate.copy
            (transitionHeadRef stateCount (values Work.horizon)
              (values Work.configBase) (values Work.tapeIndex)
              (values Work.position))) := by
  by_cases hzero : values Work.temporary₃ = 0
  · simp [emitHeadAtCurrentCellGate, BinaryRoutine.branchZero, hzero,
      emitConstantGate, BinaryRoutine.emitRawGateStep,
      CircuitCode.RawGate.constant, hreference]
  · simp [emitHeadAtCurrentCellGate, BinaryRoutine.branchZero, hzero,
      emitHeadReference_emitted]

theorem emitHeadAtCurrentCell_sound_internal (stateCount : ℕ) :
    (emitHeadAtCurrentCell stateCount).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h
  · subst routine
    exact BinaryRoutine.binaryCopy_sound Work.horizon Work.temporary₃
      Work.copyCounter
  · subst routine
    exact BinaryRoutine.addConst_sound Work.temporary₃ 1
  · subst routine
    exact decrementReferenceBy_sound Work.temporary₃ Work.position Work.loop₃
  · subst routine
    exact emitHeadAtCurrentCellGate_sound_internal stateCount
  · subst routine
    exact BinaryRoutine.clear_sound Work.temporary₃

theorem emitHeadAtCurrentCell_requires_internal (stateCount : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : HeadAtCurrentCellClean values)
    (hposition : values Work.position ≤ values Work.horizon + 1) :
    (emitHeadAtCurrentCell stateCount).requires values := by
  let afterCopy :=
    (BinaryRoutine.binaryCopy Work.horizon Work.temporary₃
      Work.copyCounter).effect values
  let afterSucc :=
    (BinaryRoutine.addConst Work.temporary₃ 1).effect afterCopy
  let afterGap :=
    (decrementReferenceBy Work.temporary₃ Work.position
      Work.loop₃).effect afterSucc
  have hafterCopy : afterCopy =
      Function.update values Work.temporary₃ (values Work.horizon) := rfl
  have hafterSucc : afterSucc =
      Function.update afterCopy Work.temporary₃
        (afterCopy Work.temporary₃ + 1) := rfl
  have hloopSucc : afterSucc Work.loop₃ = 0 := by
    rw [hafterSucc, hafterCopy]
    simpa [Work.temporary₃, Work.loop₃] using hclean.loop₃
  have hdistinct : DecrementReferenceDistinct Work.temporary₃ Work.position
      Work.loop₃ :=
    { reference_ne_offset := by decide
      reference_ne_counter := by decide
      offset_ne_counter := by decide }
  have hafterGap : afterGap =
      Function.update
        (Function.update afterSucc Work.temporary₃
          (afterSucc Work.temporary₃ - afterSucc Work.position))
        Work.loop₃ 0 :=
    decrementReferenceBy_effect Work.temporary₃ Work.position Work.loop₃
      afterSucc hdistinct hloopSucc
  have hcopy :
      (BinaryRoutine.binaryCopy Work.horizon Work.temporary₃
        Work.copyCounter).requires values := by
    exact ⟨by decide, by decide, by decide, hclean.copyCounter⟩
  have hgap :
      (decrementReferenceBy Work.temporary₃ Work.position
        Work.loop₃).requires afterSucc := by
    rw [decrementReferenceBy_requires]
    refine ⟨hdistinct, hloopSucc, ?_⟩
    rw [hafterSucc, hafterCopy]
    simpa [Work.horizon, Work.temporary₃, Work.position] using hposition
  have hemitGap : afterGap Work.emitCounter = 0 := by
    rw [hafterGap, hafterSucc, hafterCopy]
    simpa [Work.temporary₃, Work.position, Work.loop₃,
      Work.emitCounter] using hclean.emitCounter
  have haddGap : afterGap Work.addCounter = 0 := by
    rw [hafterGap, hafterSucc, hafterCopy]
    simpa [Work.temporary₃, Work.position, Work.loop₃,
      Work.addCounter] using hclean.addCounter
  have hmultiplyGap : afterGap Work.multiplyCounter = 0 := by
    rw [hafterGap, hafterSucc, hafterCopy]
    simpa [Work.temporary₃, Work.position, Work.loop₃,
      Work.multiplyCounter] using hclean.multiplyCounter
  have hbranch :
      (emitHeadAtCurrentCellGate stateCount).requires afterGap :=
    emitHeadAtCurrentCellGate_requires_internal stateCount afterGap haddGap
      hmultiplyGap hemitGap
  simp only [emitHeadAtCurrentCell, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  exact ⟨hcopy, trivial, hgap, hbranch, trivial, trivial⟩

@[simp] theorem emitHeadAtCurrentCell_effect_internal (stateCount : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : HeadAtCurrentCellClean values) :
    (emitHeadAtCurrentCell stateCount).effect values =
      Function.update values Work.available (values Work.available + 1) := by
  let afterCopy :=
    (BinaryRoutine.binaryCopy Work.horizon Work.temporary₃
      Work.copyCounter).effect values
  let afterSucc :=
    (BinaryRoutine.addConst Work.temporary₃ 1).effect afterCopy
  let afterGap :=
    (decrementReferenceBy Work.temporary₃ Work.position
      Work.loop₃).effect afterSucc
  have hafterCopy : afterCopy =
      Function.update values Work.temporary₃ (values Work.horizon) := rfl
  have hafterSucc : afterSucc =
      Function.update afterCopy Work.temporary₃
        (afterCopy Work.temporary₃ + 1) := rfl
  have hloopSucc : afterSucc Work.loop₃ = 0 := by
    rw [hafterSucc, hafterCopy]
    simpa [Work.temporary₃, Work.loop₃] using hclean.loop₃
  have hdistinct : DecrementReferenceDistinct Work.temporary₃ Work.position
      Work.loop₃ :=
    { reference_ne_offset := by decide
      reference_ne_counter := by decide
      offset_ne_counter := by decide }
  have hafterGap : afterGap =
      Function.update
        (Function.update afterSucc Work.temporary₃
          (afterSucc Work.temporary₃ - afterSucc Work.position))
        Work.loop₃ 0 :=
    decrementReferenceBy_effect Work.temporary₃ Work.position Work.loop₃
      afterSucc hdistinct hloopSucc
  have htemporaryGap : afterGap Work.temporary₀ = 0 := by
    rw [hafterGap, hafterSucc, hafterCopy]
    simpa [Work.temporary₃, Work.position, Work.loop₃,
      Work.temporary₀] using hclean.temporary₀
  have hreferenceGap : afterGap Work.reference₀ = 0 := by
    rw [hafterGap, hafterSucc, hafterCopy]
    simpa [Work.temporary₃, Work.position, Work.loop₃,
      Work.reference₀] using hclean.reference₀
  rw [emitHeadAtCurrentCell]
  change (BinaryRoutine.clear Work.temporary₃).effect
      ((emitHeadAtCurrentCellGate stateCount).effect afterGap) = _
  rw [emitHeadAtCurrentCellGate_effect_internal stateCount afterGap
    htemporaryGap hreferenceGap]
  rw [hafterGap, hafterSucc, hafterCopy]
  simp only [BinaryRoutine.clear]
  have htemporary₃ : values (25 : Fin WorkCount) = 0 := by
    simpa [Work.temporary₃] using hclean.temporary₃
  funext i
  simp only [Function.update_apply]
  split_ifs <;>
    simp_all [Work.temporary₃, Work.position, Work.loop₃,
      Work.available]

@[simp] theorem emitHeadAtCurrentCell_emitted_internal (stateCount : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : HeadAtCurrentCellClean values)
    (hposition : values Work.position ≤ values Work.horizon + 1) :
    (emitHeadAtCurrentCell stateCount).emitted values =
      CircuitCode.RawGate.encode
        (headAtCellFormulaGate stateCount (values Work.horizon)
          (values Work.configBase) (values Work.tapeIndex)
          (values Work.position)) := by
  simp [emitHeadAtCurrentCell, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.binaryCopy, BinaryRoutine.addConst,
    decrementReferenceBy_emitted, BinaryRoutine.clear,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  let afterSucc := Function.update values Work.temporary₃
    (values Work.horizon + 1)
  change (emitHeadAtCurrentCellGate stateCount).emitted
      ((decrementReferenceBy Work.temporary₃ Work.position
        Work.loop₃).effect afterSucc) = _
  have hloop₃ : values (20 : Fin WorkCount) = 0 := by
    simpa [Work.loop₃] using hclean.loop₃
  have hloop : afterSucc Work.loop₃ = 0 := by
    simp [afterSucc, Work.temporary₃, Work.loop₃, hloop₃]
  have hdistinct : DecrementReferenceDistinct Work.temporary₃ Work.position
      Work.loop₃ :=
    { reference_ne_offset := by decide
      reference_ne_counter := by decide
      offset_ne_counter := by decide }
  rw [decrementReferenceBy_effect Work.temporary₃ Work.position Work.loop₃
    afterSucc hdistinct hloop]
  let afterGap :=
    Function.update
      (Function.update afterSucc Work.temporary₃
        (afterSucc Work.temporary₃ - afterSucc Work.position))
      Work.loop₃ 0
  change (emitHeadAtCurrentCellGate stateCount).emitted afterGap = _
  have hreference₀ : values (7 : Fin WorkCount) = 0 := by
    simpa [Work.reference₀] using hclean.reference₀
  have hreference : afterGap Work.reference₀ = 0 := by
    simp [afterGap, afterSucc, Work.temporary₃, Work.position, Work.loop₃,
      Work.reference₀, hreference₀]
  rw [emitHeadAtCurrentCellGate_emitted_internal stateCount afterGap hreference]
  unfold headAtCellFormulaGate
  by_cases hrepresented : values Work.position < values Work.horizon + 1
  · have hrepresented' : values (30 : Fin WorkCount) < values 1 + 1 := by
      simpa [Work.position, Work.horizon] using hrepresented
    have hgap : values (1 : Fin WorkCount) + 1 - values 30 ≠ 0 := by
      omega
    have hhead : values (30 : Fin WorkCount) ≤ values 1 := by
      omega
    simp [hgap, hhead, afterGap, afterSucc, Work.horizon,
      Work.configBase, Work.tapeIndex, Work.position, Work.temporary₃,
      Work.loop₃]
  · have hrepresented' : ¬values (30 : Fin WorkCount) < values 1 + 1 := by
      simpa [Work.position, Work.horizon] using hrepresented
    have hposition' : values (30 : Fin WorkCount) ≤ values 1 + 1 := by
      simpa [Work.position, Work.horizon] using hposition
    have heq : values (30 : Fin WorkCount) = values 1 + 1 := by omega
    simp [afterGap, afterSucc, Work.horizon, Work.position, Work.temporary₃,
      Work.loop₃, heq]

private theorem emitCaseChoice_sound_for_writtenCell (choiceValue : Bool) :
    (emitCaseChoice choiceValue).Sound := by
  cases choiceValue with
  | false =>
      exact (emitCopyGate_sound Work.reference₀ false).seq
        (emitRecentGate_sound .and true true 1 1)
  | true => exact emitCopyGate_sound Work.reference₀ false

private theorem emitCaseRead_sound_for_writtenCell
    (stateCount workCount tapeIndex symbolIndex : ℕ) :
    (emitCaseRead stateCount workCount tapeIndex symbolIndex).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h
  · subst routine
    exact BinaryRoutine.set_sound Work.tapeIndex tapeIndex
  · subst routine
    exact BinaryRoutine.set_sound Work.symbolIndex symbolIndex
  · subst routine
    exact emitReadFormula_sound stateCount (workCount + 2)

private theorem emitCaseReads_sound_for_writtenCell
    (stateCount workCount count start : ℕ) (symbolAt : ℕ → ℕ) :
    (emitCaseReads stateCount workCount count start symbolAt).Sound := by
  induction count generalizing start symbolAt with
  | zero => exact BinaryRoutine.identity_sound
  | succ count ih =>
      exact (emitCaseRead_sound_for_writtenCell stateCount workCount start
        (symbolAt 0)).seq
          (ih (start := start + 1)
            (symbolAt := fun index => symbolAt (index + 1)))

private theorem emitCaseMembers_sound_for_writtenCell
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ) :
    (emitCaseMembers stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h
  · subst routine
    exact emitCaseChoice_sound_for_writtenCell choiceValue
  · subst routine
    exact emitStateReference_sound stateIndex false
  · subst routine
    exact emitCaseRead_sound_for_writtenCell stateCount workCount 0
      inputSymbolIndex
  · subst routine
    exact emitCaseReads_sound_for_writtenCell stateCount workCount workCount 1
      workSymbolIndexAt
  · subst routine
    exact emitCaseRead_sound_for_writtenCell stateCount workCount
      (workCount + 1) outputSymbolIndex

private theorem prepareCaseReadSize_sound_for_writtenCell :
    prepareCaseReadSize.Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h
  · subst routine
    exact BinaryRoutine.set_sound Work.temporary₃ 5
  · subst routine
    exact BinaryRoutine.set_sound Work.temporary₂ 4
  · subst routine
    exact BinaryRoutine.mulAdd_sound Work.horizon Work.temporary₂
      Work.temporary₃ Work.multiplyCounter Work.addCounter
  · subst routine
    exact BinaryRoutine.clear_sound Work.temporary₂

private theorem emitCaseConnector_sound_for_writtenCell :
    emitCaseConnector.Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h
  · subst routine
    exact prepareRecentReference_sound Work.reference₁ 1
  · subst routine
    exact BinaryRoutine.emitRawGateStep_sound .and false false Work.emitCounter
      Work.available Work.reference₀ Work.reference₁
  · subst routine
    exact BinaryRoutine.clear_sound Work.reference₁

private theorem emitPreviousCaseReadConnector_sound_for_writtenCell :
    emitPreviousCaseReadConnector.Sound :=
  (decrementReferenceBy_sound Work.reference₀ Work.temporary₃
    Work.loop₃).seq emitCaseConnector_sound_for_writtenCell

private theorem emitPreviousCaseChoiceConnector_sound_for_writtenCell :
    emitPreviousCaseChoiceConnector.Sound :=
  (BinaryRoutine.binaryPred_sound Work.reference₀).seq
    emitCaseConnector_sound_for_writtenCell

private theorem emitPreviousCaseReadConnectors_sound_for_writtenCell
    (count : ℕ) : (emitPreviousCaseReadConnectors count).Sound := by
  induction count with
  | zero => exact BinaryRoutine.identity_sound
  | succ count ih =>
      exact emitPreviousCaseReadConnector_sound_for_writtenCell.seq ih

private theorem emitCaseFormula_sound_for_writtenCell
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ) :
    (emitCaseFormula stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h | h | h | h | h | h | h
  · subst routine
    exact emitCaseMembers_sound_for_writtenCell stateCount workCount stateIndex
      inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt
  · subst routine
    exact emitConstantGate_sound true
  · subst routine
    exact prepareCaseReadSize_sound_for_writtenCell
  · subst routine
    exact prepareRecentReference_sound Work.reference₀ 2
  · subst routine
    exact emitCaseConnector_sound_for_writtenCell
  · subst routine
    exact emitPreviousCaseReadConnectors_sound_for_writtenCell (workCount + 2)
  · subst routine
    exact emitPreviousCaseChoiceConnector_sound_for_writtenCell
  all_goals
    subst routine
    exact BinaryRoutine.clear_sound _

private theorem emitEffectCaseAt_sound_for_writtenCell (tm : NTM k)
    (selects : TransitionEffect tm → Bool)
    (caseIndex : Fin (transitionCases tm).length) :
    (emitEffectCaseAt tm selects caseIndex).Sound := by
  rw [emitEffectCaseAt]
  split_ifs
  · exact emitCaseFormula_sound_for_writtenCell (Fintype.card tm.Q) k
      (effectCaseStateIndexAt tm caseIndex)
      (effectCaseInputSymbolIndexAt tm caseIndex)
      (effectCaseOutputSymbolIndexAt tm caseIndex)
      (effectCaseChoiceAt tm caseIndex)
      (effectCaseWorkSymbolIndexAt tm caseIndex)
  · exact emitConstantGate_sound false

private theorem emitEffectMembers_sound_for_writtenCell (tm : NTM k)
    (selects : TransitionEffect tm → Bool) :
    (emitEffectMembers tm selects).Sound :=
  emitEffectMembers_sound_internal tm selects

private theorem emitEffectFormula_sound_for_writtenCell (tm : NTM k)
    (selects : TransitionEffect tm → Bool) :
    (emitEffectFormula tm selects).Sound := by
  apply BinaryRoutine.seqList_sound
  intro member hmember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
  rcases hmember with hmember | hmember | hmember
  · subst member
    exact emitEffectMembers_sound_for_writtenCell tm selects
  · subst member
    exact emitConstantGate_sound false
  · subst member
    exact emitEffectConnectors_sound_internal tm selects

theorem emitWrittenCellEffect_sound_internal (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ) :
    (emitWrittenCellEffect tm tape symbol).Sound := by
  rw [emitWrittenCellEffect]
  exact emitEffectFormula_sound_for_writtenCell tm _

theorem emitWrittenCellFormula_sound_internal (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ) :
    (emitWrittenCellFormula tm tape symbol).Sound := by
  apply BinaryRoutine.seqList_sound
  intro member hmember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
  rcases hmember with hmember | hmember | hmember | hmember | hmember |
      hmember | hmember | hmember | hmember | hmember | hmember | hmember |
      hmember | hmember | hmember | hmember | hmember | hmember | hmember |
      hmember | hmember | hmember | hmember | hmember
  · subst member
    exact BinaryRoutine.set_sound Work.tapeIndex tape.toTapeSlot.index.val
  · subst member
    exact BinaryRoutine.set_sound Work.symbolIndex
      (CircuitUnrolling.symbolIndex symbol).val
  · subst member
    exact emitHeadAtCurrentCell_sound_internal (Fintype.card tm.Q)
  · subst member
    exact prepareRecentReference_sound Work.savedOutput 1
  · subst member
    exact BinaryRoutine.binaryCopy_sound Work.position Work.limit₂
      Work.copyCounter
  · subst member
    exact BinaryRoutine.clear_sound Work.position
  · subst member
    exact BinaryRoutine.clear_sound Work.tapeIndex
  · subst member
    exact BinaryRoutine.clear_sound Work.symbolIndex
  · subst member
    exact emitWrittenCellEffect_sound_internal tm tape symbol
  · subst member
    exact BinaryRoutine.binaryCopy_sound Work.limit₂ Work.position
      Work.copyCounter
  · subst member
    exact BinaryRoutine.set_sound Work.tapeIndex tape.toTapeSlot.index.val
  · subst member
    exact BinaryRoutine.set_sound Work.symbolIndex
      (CircuitUnrolling.symbolIndex symbol).val
  · subst member
    exact prepareRecentReference_sound Work.reference₁ 1
  · subst member
    exact BinaryRoutine.emitRawGateStep_sound .and false false Work.emitCounter
      Work.available Work.savedOutput Work.reference₁
  · subst member
    exact BinaryRoutine.clear_sound Work.reference₁
  · subst member
    exact emitHeadAtCurrentCell_sound_internal (Fintype.card tm.Q)
  · subst member
    exact emitRecentGate_sound .and true true 1 1
  · subst member
    exact emitCellReference_sound (Fintype.card tm.Q) (k + 2) false
  · subst member
    exact emitRecentGate_sound .and false false 2 1
  · subst member
    exact emitRecentGate_sound .or false false 5 1
  all_goals
    subst member
    exact BinaryRoutine.clear_sound _

private theorem seqList_append_effect_for_writtenCell
    (first second : List (BinaryRoutine n)) (values : BinaryValues n) :
    (BinaryRoutine.seqList (first ++ second)).effect values =
      (BinaryRoutine.seqList second).effect
        ((BinaryRoutine.seqList first).effect values) := by
  induction first generalizing values with
  | nil =>
      simp [BinaryRoutine.seqList, BinaryRoutine.identity,
        BinaryRoutine.emitBits]
  | cons routine routines ih =>
      simp [BinaryRoutine.seqList, BinaryRoutine.seq, ih]

private theorem seqList_append_emitted_for_writtenCell
    (first second : List (BinaryRoutine n)) (values : BinaryValues n) :
    (BinaryRoutine.seqList (first ++ second)).emitted values =
      (BinaryRoutine.seqList first).emitted values ++
        (BinaryRoutine.seqList second).emitted
          ((BinaryRoutine.seqList first).effect values) := by
  induction first generalizing values with
  | nil =>
      simp [BinaryRoutine.seqList, BinaryRoutine.identity,
        BinaryRoutine.emitBits]
  | cons routine routines ih =>
      simp [BinaryRoutine.seqList, BinaryRoutine.seq, ih,
        List.append_assoc]

private theorem seqList_append_requires_for_writtenCell
    (first second : List (BinaryRoutine n)) (values : BinaryValues n) :
    (BinaryRoutine.seqList (first ++ second)).requires values ↔
      (BinaryRoutine.seqList first).requires values ∧
        (BinaryRoutine.seqList second).requires
          ((BinaryRoutine.seqList first).effect values) := by
  induction first generalizing values with
  | nil =>
      simp [BinaryRoutine.seqList, BinaryRoutine.identity,
        BinaryRoutine.emitBits]
  | cons routine routines ih =>
      simp [BinaryRoutine.seqList, BinaryRoutine.seq, ih, and_assoc]

private theorem seqList_singleton_effect_for_writtenCell
    (routine : BinaryRoutine n) (values : BinaryValues n) :
    (BinaryRoutine.seqList [routine]).effect values = routine.effect values := by
  simp [BinaryRoutine.seqList, BinaryRoutine.seq, BinaryRoutine.identity,
    BinaryRoutine.emitBits]

private theorem seqList_singleton_emitted_for_writtenCell
    (routine : BinaryRoutine n) (values : BinaryValues n) :
    (BinaryRoutine.seqList [routine]).emitted values =
      routine.emitted values := by
  simp [BinaryRoutine.seqList, BinaryRoutine.seq, BinaryRoutine.identity,
    BinaryRoutine.emitBits]

private theorem seqList_singleton_requires_for_writtenCell
    (routine : BinaryRoutine n) (values : BinaryValues n) :
    (BinaryRoutine.seqList [routine]).requires values ↔
      routine.requires values := by
  simp [BinaryRoutine.seqList, BinaryRoutine.seq, BinaryRoutine.identity,
    BinaryRoutine.emitBits]

private def emitWrittenCellPrefix (stateCount tapeIndex symbolIndex : ℕ) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [BinaryRoutine.set Work.tapeIndex tapeIndex,
      BinaryRoutine.set Work.symbolIndex symbolIndex,
      emitHeadAtCurrentCell stateCount,
      prepareRecentReference Work.savedOutput 1,
      BinaryRoutine.binaryCopy Work.position Work.limit₂ Work.copyCounter,
      BinaryRoutine.clear Work.position,
      BinaryRoutine.clear Work.tapeIndex,
      BinaryRoutine.clear Work.symbolIndex]

private def emitWrittenCellFinish
    (stateCount tapeCount tapeIndex symbolIndex : ℕ) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [BinaryRoutine.binaryCopy Work.limit₂ Work.position Work.copyCounter,
      BinaryRoutine.set Work.tapeIndex tapeIndex,
      BinaryRoutine.set Work.symbolIndex symbolIndex,
      prepareRecentReference Work.reference₁ 1,
      BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
        Work.available Work.savedOutput Work.reference₁,
      BinaryRoutine.clear Work.reference₁,
      emitHeadAtCurrentCell stateCount,
      emitRecentGate .and true true 1 1,
      emitCellReference stateCount tapeCount,
      emitRecentGate .and false false 2 1,
      emitRecentGate .or false false 5 1,
      BinaryRoutine.clear Work.savedOutput,
      BinaryRoutine.clear Work.limit₂,
      BinaryRoutine.clear Work.tapeIndex,
      BinaryRoutine.clear Work.symbolIndex]

private def writtenCellPrefixRoutines
    (stateCount tapeIndex symbolIndex : ℕ) :
    List (BinaryRoutine WorkCount) :=
  [BinaryRoutine.set Work.tapeIndex tapeIndex,
    BinaryRoutine.set Work.symbolIndex symbolIndex,
    emitHeadAtCurrentCell stateCount,
    prepareRecentReference Work.savedOutput 1,
    BinaryRoutine.binaryCopy Work.position Work.limit₂ Work.copyCounter,
    BinaryRoutine.clear Work.position,
    BinaryRoutine.clear Work.tapeIndex,
    BinaryRoutine.clear Work.symbolIndex]

private def writtenCellFinishRoutines
    (stateCount tapeCount tapeIndex symbolIndex : ℕ) :
    List (BinaryRoutine WorkCount) :=
  [BinaryRoutine.binaryCopy Work.limit₂ Work.position Work.copyCounter,
    BinaryRoutine.set Work.tapeIndex tapeIndex,
    BinaryRoutine.set Work.symbolIndex symbolIndex,
    prepareRecentReference Work.reference₁ 1,
    BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
      Work.available Work.savedOutput Work.reference₁,
    BinaryRoutine.clear Work.reference₁,
    emitHeadAtCurrentCell stateCount,
    emitRecentGate .and true true 1 1,
    emitCellReference stateCount tapeCount,
    emitRecentGate .and false false 2 1,
    emitRecentGate .or false false 5 1,
    BinaryRoutine.clear Work.savedOutput,
    BinaryRoutine.clear Work.limit₂,
    BinaryRoutine.clear Work.tapeIndex,
    BinaryRoutine.clear Work.symbolIndex]

private theorem emitWrittenCellPrefix_eq_seqList
    (stateCount tapeIndex symbolIndex : ℕ) :
    emitWrittenCellPrefix stateCount tapeIndex symbolIndex =
      BinaryRoutine.seqList
        (writtenCellPrefixRoutines stateCount tapeIndex symbolIndex) := rfl

private theorem emitWrittenCellFinish_eq_seqList
    (stateCount tapeCount tapeIndex symbolIndex : ℕ) :
    emitWrittenCellFinish stateCount tapeCount tapeIndex symbolIndex =
      BinaryRoutine.seqList
        (writtenCellFinishRoutines stateCount tapeCount tapeIndex
          symbolIndex) := rfl

private theorem emitWrittenCellFormula_eq_seqList
    (tm : NTM k) (tape : WritableSlot k) (symbol : Γ) :
    emitWrittenCellFormula tm tape symbol =
      BinaryRoutine.seqList
        (writtenCellPrefixRoutines (Fintype.card tm.Q)
            tape.toTapeSlot.index.val
            (CircuitUnrolling.symbolIndex symbol).val ++
          ([emitWrittenCellEffect tm tape symbol] ++
            writtenCellFinishRoutines (Fintype.card tm.Q) (k + 2)
              tape.toTapeSlot.index.val
              (CircuitUnrolling.symbolIndex symbol).val)) := rfl

private theorem emitWrittenCellFormula_requires_iff_decompose
    (tm : NTM k) (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount) :
    (emitWrittenCellFormula tm tape symbol).requires values ↔
      (emitWrittenCellPrefix (Fintype.card tm.Q) tape.toTapeSlot.index.val
          (CircuitUnrolling.symbolIndex symbol).val).requires values ∧
        (emitWrittenCellEffect tm tape symbol).requires
          ((emitWrittenCellPrefix (Fintype.card tm.Q)
            tape.toTapeSlot.index.val
            (CircuitUnrolling.symbolIndex symbol).val).effect values) ∧
        (emitWrittenCellFinish (Fintype.card tm.Q) (k + 2)
          tape.toTapeSlot.index.val
          (CircuitUnrolling.symbolIndex symbol).val).requires
            ((emitWrittenCellEffect tm tape symbol).effect
              ((emitWrittenCellPrefix (Fintype.card tm.Q)
                tape.toTapeSlot.index.val
                (CircuitUnrolling.symbolIndex symbol).val).effect values)) := by
  rw [emitWrittenCellFormula_eq_seqList,
    seqList_append_requires_for_writtenCell,
    seqList_append_requires_for_writtenCell]
  rw [← emitWrittenCellPrefix_eq_seqList,
    ← emitWrittenCellFinish_eq_seqList]
  rw [seqList_singleton_requires_for_writtenCell,
    seqList_singleton_effect_for_writtenCell]

private theorem emitWrittenCellFormula_effect_decompose
    (tm : NTM k) (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount) :
    (emitWrittenCellFormula tm tape symbol).effect values =
      (emitWrittenCellFinish (Fintype.card tm.Q) (k + 2)
        tape.toTapeSlot.index.val
        (CircuitUnrolling.symbolIndex symbol).val).effect
          ((emitWrittenCellEffect tm tape symbol).effect
            ((emitWrittenCellPrefix (Fintype.card tm.Q)
              tape.toTapeSlot.index.val
              (CircuitUnrolling.symbolIndex symbol).val).effect values)) := by
  rw [emitWrittenCellFormula_eq_seqList,
    seqList_append_effect_for_writtenCell,
    seqList_append_effect_for_writtenCell]
  rw [← emitWrittenCellPrefix_eq_seqList,
    ← emitWrittenCellFinish_eq_seqList]
  rw [seqList_singleton_effect_for_writtenCell]

private theorem emitWrittenCellFormula_emitted_decompose
    (tm : NTM k) (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount) :
    (emitWrittenCellFormula tm tape symbol).emitted values =
      (emitWrittenCellPrefix (Fintype.card tm.Q) tape.toTapeSlot.index.val
          (CircuitUnrolling.symbolIndex symbol).val).emitted values ++
        (emitWrittenCellEffect tm tape symbol).emitted
            ((emitWrittenCellPrefix (Fintype.card tm.Q)
              tape.toTapeSlot.index.val
              (CircuitUnrolling.symbolIndex symbol).val).effect values) ++
        (emitWrittenCellFinish (Fintype.card tm.Q) (k + 2)
          tape.toTapeSlot.index.val
          (CircuitUnrolling.symbolIndex symbol).val).emitted
            ((emitWrittenCellEffect tm tape symbol).effect
              ((emitWrittenCellPrefix (Fintype.card tm.Q)
                tape.toTapeSlot.index.val
                (CircuitUnrolling.symbolIndex symbol).val).effect values)) := by
  rw [emitWrittenCellFormula_eq_seqList,
    seqList_append_emitted_for_writtenCell,
    seqList_append_emitted_for_writtenCell]
  rw [← emitWrittenCellPrefix_eq_seqList,
    ← emitWrittenCellFinish_eq_seqList]
  rw [seqList_singleton_emitted_for_writtenCell,
    seqList_singleton_effect_for_writtenCell]
  rw [List.append_assoc]

private def writtenCellSelectedValues (values : BinaryValues WorkCount)
    (tapeIndex symbolIndex : ℕ) : BinaryValues WorkCount :=
  Function.update (Function.update values Work.tapeIndex tapeIndex)
    Work.symbolIndex symbolIndex

private theorem writtenCellSelectedValues_eq_effect
    (values : BinaryValues WorkCount) (tapeIndex symbolIndex : ℕ) :
    writtenCellSelectedValues values tapeIndex symbolIndex =
      (BinaryRoutine.set Work.symbolIndex symbolIndex).effect
        ((BinaryRoutine.set Work.tapeIndex tapeIndex).effect values) := by
  simp [writtenCellSelectedValues, BinaryRoutine.set, BinaryRoutine.seq,
    BinaryRoutine.clear, BinaryRoutine.addConst, Work.tapeIndex,
    Work.symbolIndex]

private theorem HeadAtCurrentCellClean.writtenCellSelectedValues
    (values : BinaryValues WorkCount) (tapeIndex symbolIndex : ℕ)
    (hclean : HeadAtCurrentCellClean values) :
    HeadAtCurrentCellClean
      (writtenCellSelectedValues values tapeIndex symbolIndex) := by
  refine
    { loop₃ := ?_
      temporary₃ := ?_
      reference₀ := ?_
      emitCounter := ?_
      copyCounter := ?_
      multiplyCounter := ?_
      addCounter := ?_
      temporary₀ := ?_ }
  · simpa [writtenCellSelectedValues, Work.tapeIndex, Work.symbolIndex] using
      hclean.loop₃
  · simpa [writtenCellSelectedValues, Work.tapeIndex, Work.symbolIndex] using
      hclean.temporary₃
  · simpa [writtenCellSelectedValues, Work.tapeIndex, Work.symbolIndex] using
      hclean.reference₀
  · simpa [writtenCellSelectedValues, Work.tapeIndex, Work.symbolIndex] using
      hclean.emitCounter
  · simpa [writtenCellSelectedValues, Work.tapeIndex, Work.symbolIndex] using
      hclean.copyCounter
  · simpa [writtenCellSelectedValues, Work.tapeIndex, Work.symbolIndex] using
      hclean.multiplyCounter
  · simpa [writtenCellSelectedValues, Work.tapeIndex, Work.symbolIndex] using
      hclean.addCounter
  · simpa [writtenCellSelectedValues, Work.tapeIndex, Work.symbolIndex] using
      hclean.temporary₀

private def writtenCellEffectStartValues (values : BinaryValues WorkCount) :
    BinaryValues WorkCount :=
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update values Work.available
              (values Work.available + 1)) Work.savedOutput
              (values Work.available)) Work.limit₂ (values Work.position))
          Work.position 0) Work.tapeIndex 0) Work.symbolIndex 0

private theorem emitWrittenCellPrefix_effect
    (stateCount tapeIndex symbolIndex : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : WrittenCellFormulaClean values) :
    (emitWrittenCellPrefix stateCount tapeIndex symbolIndex).effect values =
      writtenCellEffectStartValues values := by
  let selected := writtenCellSelectedValues values tapeIndex symbolIndex
  have hselected : selected =
      (BinaryRoutine.set Work.symbolIndex symbolIndex).effect
        ((BinaryRoutine.set Work.tapeIndex tapeIndex).effect values) :=
    writtenCellSelectedValues_eq_effect values tapeIndex symbolIndex
  have hheadClean : HeadAtCurrentCellClean selected :=
    HeadAtCurrentCellClean.writtenCellSelectedValues values tapeIndex symbolIndex
      hclean.headAtCurrentCellClean_internal
  simp only [emitWrittenCellPrefix, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [← hselected,
    emitHeadAtCurrentCell_effect_internal stateCount selected hheadClean,
    prepareRecentReference_effect]
  simp [selected, writtenCellSelectedValues, writtenCellEffectStartValues,
    BinaryRoutine.binaryCopy, BinaryRoutine.clear, Work.available,
    Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
    Work.symbolIndex]
  funext i
  simp only [Function.update_apply]
  split_ifs <;> omega

private theorem emitWrittenCellPrefix_emitted
    (stateCount tapeIndex symbolIndex : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : WrittenCellFormulaClean values)
    (hposition : values Work.position ≤ values Work.horizon + 1) :
    (emitWrittenCellPrefix stateCount tapeIndex symbolIndex).emitted values =
      CircuitCode.RawGate.encode
        (headAtCellFormulaGate stateCount (values Work.horizon)
          (values Work.configBase) tapeIndex (values Work.position)) := by
  let selected := writtenCellSelectedValues values tapeIndex symbolIndex
  have hselected : selected =
      (BinaryRoutine.set Work.symbolIndex symbolIndex).effect
        ((BinaryRoutine.set Work.tapeIndex tapeIndex).effect values) :=
    writtenCellSelectedValues_eq_effect values tapeIndex symbolIndex
  have hheadClean : HeadAtCurrentCellClean selected :=
    HeadAtCurrentCellClean.writtenCellSelectedValues values tapeIndex symbolIndex
      hclean.headAtCurrentCellClean_internal
  have hpositionSelected :
      selected Work.position ≤ selected Work.horizon + 1 := by
    simpa [selected, writtenCellSelectedValues, Work.tapeIndex,
      Work.symbolIndex, Work.position, Work.horizon] using hposition
  simp only [emitWrittenCellPrefix, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [← hselected,
    emitHeadAtCurrentCell_emitted_internal stateCount selected hheadClean
      hpositionSelected,
    emitHeadAtCurrentCell_effect_internal stateCount selected hheadClean,
    prepareRecentReference_emitted]
  simp [BinaryRoutine.binaryCopy, BinaryRoutine.set, BinaryRoutine.seq,
    BinaryRoutine.clear, BinaryRoutine.addConst,
    writtenCellSelectedValues, selected, Work.horizon, Work.configBase,
    Work.tapeIndex, Work.symbolIndex, Work.position]

private theorem emitWrittenCellPrefix_requires
    (stateCount tapeIndex symbolIndex : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : WrittenCellFormulaClean values)
    (hposition : values Work.position ≤ values Work.horizon + 1) :
    (emitWrittenCellPrefix stateCount tapeIndex symbolIndex).requires
      values := by
  let selected := writtenCellSelectedValues values tapeIndex symbolIndex
  have hselected : selected =
      (BinaryRoutine.set Work.symbolIndex symbolIndex).effect
        ((BinaryRoutine.set Work.tapeIndex tapeIndex).effect values) :=
    writtenCellSelectedValues_eq_effect values tapeIndex symbolIndex
  have hheadClean : HeadAtCurrentCellClean selected :=
    HeadAtCurrentCellClean.writtenCellSelectedValues values tapeIndex symbolIndex
      hclean.headAtCurrentCellClean_internal
  have hpositionSelected :
      selected Work.position ≤ selected Work.horizon + 1 := by
    simpa [selected, writtenCellSelectedValues, Work.tapeIndex,
      Work.symbolIndex, Work.position, Work.horizon] using hposition
  have hhead := emitHeadAtCurrentCell_requires_internal stateCount selected
    hheadClean hpositionSelected
  let afterHead := Function.update selected Work.available
    (selected Work.available + 1)
  have hafterHead :
      (emitHeadAtCurrentCell stateCount).effect selected = afterHead :=
    emitHeadAtCurrentCell_effect_internal stateCount selected hheadClean
  have hprepare :
      (prepareRecentReference Work.savedOutput 1).requires afterHead := by
    apply (prepareRecentReference_requires Work.savedOutput 1 afterHead
      (by decide) (by decide) (by decide)).2
    refine ⟨?_, ?_⟩
    · simpa [afterHead, Work.available, Work.copyCounter] using
        hheadClean.copyCounter
    · simp [afterHead, Work.available]
  let afterPrepare := Function.update afterHead Work.savedOutput
    (afterHead Work.available - 1)
  have hafterPrepare :
      (prepareRecentReference Work.savedOutput 1).effect afterHead =
        afterPrepare := by
    rw [prepareRecentReference_effect]
  have hcopyPosition :
      (BinaryRoutine.binaryCopy Work.position Work.limit₂
        Work.copyCounter).requires afterPrepare := by
    refine ⟨by decide, by decide, by decide, ?_⟩
    simpa [afterPrepare, afterHead, selected, writtenCellSelectedValues,
      Work.savedOutput, Work.available, Work.copyCounter] using
      hheadClean.copyCounter
  simp only [emitWrittenCellPrefix, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [← hselected, hafterHead, hafterPrepare]
  exact ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, hhead, hprepare,
    hcopyPosition, trivial, trivial, trivial, trivial⟩

private theorem writtenCellEffectStartValues_caseClean
    (values : BinaryValues WorkCount)
    (hclean : WrittenCellFormulaClean values) :
    CaseFormulaClean (writtenCellEffectStartValues values) := by
  let start := writtenCellEffectStartValues values
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
  · simp [writtenCellEffectStartValues, Work.position,
      Work.tapeIndex, Work.symbolIndex]
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.loop₀] using hclean.caseClean.loop₀
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.limit₀] using hclean.caseClean.limit₀
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.reference₀] using hclean.caseClean.reference₀
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.reference₁] using hclean.caseClean.reference₁
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.emitCounter] using hclean.caseClean.emitCounter
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.copyCounter] using hclean.caseClean.copyCounter
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.multiplyCounter] using
      hclean.caseClean.multiplyCounter
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.addCounter] using hclean.caseClean.addCounter
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.temporary₀] using hclean.caseClean.temporary₀
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.temporary₁] using hclean.caseClean.temporary₁
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.temporary₂] using hclean.caseClean.temporary₂
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.loop₃] using hclean.caseClean.loop₃
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.temporary₃] using hclean.caseClean.temporary₃
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.polynomialScratch] using
      hclean.caseClean.polynomialScratch
  · simp [writtenCellEffectStartValues, Work.tapeIndex,
      Work.symbolIndex]
  · simp [writtenCellEffectStartValues, Work.symbolIndex]

private theorem CaseFormulaClean.updateAvailable_for_writtenCell
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

theorem emitWrittenCellEffect_requires_internal (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (havailable : 1 ≤ values Work.available) :
    (emitWrittenCellEffect tm tape symbol).requires values := by
  simpa [emitWrittenCellEffect] using
    emitEffectFormula_requires_internal tm
      (fun effect => decide ((effect.write tape).toΓ = symbol)) values
      hclean havailable

@[simp] theorem emitWrittenCellEffect_effect_internal (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (havailable : 1 ≤ values Work.available) :
    (emitWrittenCellEffect tm tape symbol).effect values =
      Function.update values Work.available
        (values Work.available +
          writtenCellEffectSize (transitionCases tm).length k
            (values Work.horizon)
            (writtenCellEffectSelectedAt tm tape symbol)
            (effectCaseChoiceAt tm)) := by
  simpa [emitWrittenCellEffect, writtenCellEffectSize,
    writtenCellEffectSelectedAt] using
      emitEffectFormula_effect_internal tm
        (fun effect => decide ((effect.write tape).toΓ = symbol)) values
        hclean havailable

@[simp] theorem emitWrittenCellEffect_emitted_internal (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (havailable : 1 ≤ values Work.available) :
    (emitWrittenCellEffect tm tape symbol).emitted values =
      (effectFormulaSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k (values Work.horizon)
        (values Work.configBase) (values Work.reference₀)
        (values Work.available) (writtenCellEffectSelectedAt tm tape symbol)
        (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
        (effectCaseInputSymbolIndexAt tm) (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm)).flatMap
          CircuitCode.RawGate.encode := by
  simpa [emitWrittenCellEffect, writtenCellEffectSelectedAt] using
    emitEffectFormula_emitted_internal tm
      (fun effect => decide ((effect.write tape).toΓ = symbol)) values
      hclean havailable

private theorem writtenCellLeftAnd_effect
    (values : BinaryValues WorkCount)
    (hreference₁ : values Work.reference₁ = 0) :
    (BinaryRoutine.clear Work.reference₁).effect
        ((BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
          Work.available Work.savedOutput Work.reference₁).effect
          ((prepareRecentReference Work.reference₁ 1).effect values)) =
      Function.update values Work.available (values Work.available + 1) := by
  rw [prepareRecentReference_effect]
  simp [BinaryRoutine.emitRawGateStep, BinaryRoutine.clear,
    Work.available, Work.reference₁]
  have hreference₁' : values 8 = 0 := by
    simpa [Work.reference₁] using hreference₁
  funext i
  simp only [Function.update_apply]
  split_ifs <;> simp_all

private theorem writtenCellLeftAnd_emitted
    (values : BinaryValues WorkCount) :
    (prepareRecentReference Work.reference₁ 1).emitted values ++
        (BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
          Work.available Work.savedOutput Work.reference₁).emitted
          ((prepareRecentReference Work.reference₁ 1).effect values) ++
        (BinaryRoutine.clear Work.reference₁).emitted
          ((BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
            Work.available Work.savedOutput Work.reference₁).effect
            ((prepareRecentReference Work.reference₁ 1).effect values)) =
      CircuitCode.RawGate.encode
        { op := .and
          input₀ := values Work.savedOutput
          input₁ := values Work.available - 1
          negated₀ := false
          negated₁ := false } := by
  simp [prepareRecentReference_effect, prepareRecentReference_emitted,
    BinaryRoutine.emitRawGateStep, BinaryRoutine.clear, Work.savedOutput,
    Work.reference₁]

private theorem writtenCellLeftAnd_emitted_append
    (values : BinaryValues WorkCount) (tail : List Bool) :
    (prepareRecentReference Work.reference₁ 1).emitted values ++
        ((BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
          Work.available Work.savedOutput Work.reference₁).emitted
          ((prepareRecentReference Work.reference₁ 1).effect values) ++
        ((BinaryRoutine.clear Work.reference₁).emitted
          ((BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
            Work.available Work.savedOutput Work.reference₁).effect
            ((prepareRecentReference Work.reference₁ 1).effect values)) ++
          tail)) =
      CircuitCode.RawGate.encode
          { op := .and
            input₀ := values Work.savedOutput
            input₁ := values Work.available - 1
            negated₀ := false
            negated₁ := false } ++ tail := by
  rw [← List.append_assoc, ← List.append_assoc,
    writtenCellLeftAnd_emitted values]

private theorem writtenCellLeftAnd_requires
    (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0)
    (havailable : 1 ≤ values Work.available)
    (hemit : values Work.emitCounter = 0) :
    (prepareRecentReference Work.reference₁ 1).requires values ∧
      (BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
        Work.available Work.savedOutput Work.reference₁).requires
        ((prepareRecentReference Work.reference₁ 1).effect values) ∧
      (BinaryRoutine.clear Work.reference₁).requires
        ((BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
          Work.available Work.savedOutput Work.reference₁).effect
          ((prepareRecentReference Work.reference₁ 1).effect values)) := by
  have hprepare := (prepareRecentReference_requires Work.reference₁ 1 values
    (by decide) (by decide) (by decide)).2 ⟨hcopy, havailable⟩
  refine ⟨hprepare, ?_, trivial⟩
  rw [prepareRecentReference_effect]
  change CircuitCode.Machine.RawGateStepDistinct 9 5 26 8 ∧
    Function.update values 8 (values 5 - 1) 9 = 0
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide⟩, ?_⟩
  simpa [Work.emitCounter, Work.reference₁] using hemit

set_option maxHeartbeats 800000 in
private theorem emitWrittenCellFinish_effect
    (stateCount tapeCount tapeIndex symbolIndex : ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitWrittenCellFinish stateCount tapeCount tapeIndex symbolIndex).effect
        values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.position (values Work.limit₂))
            Work.available (values Work.available + 6)) Work.savedOutput 0)
        Work.limit₂ 0 := by
  let restored := Function.update values Work.position (values Work.limit₂)
  let selected := Function.update
    (Function.update restored Work.tapeIndex tapeIndex)
    Work.symbolIndex symbolIndex
  let afterLeft := Function.update selected Work.available
    (selected Work.available + 1)
  have hrestore :
      (BinaryRoutine.binaryCopy Work.limit₂ Work.position
        Work.copyCounter).effect values = restored := rfl
  have hselect :
      (BinaryRoutine.set Work.symbolIndex symbolIndex).effect
          ((BinaryRoutine.set Work.tapeIndex tapeIndex).effect restored) =
        selected := by
    simp [selected, BinaryRoutine.set, BinaryRoutine.seq,
      BinaryRoutine.clear, BinaryRoutine.addConst, Work.tapeIndex,
      Work.symbolIndex]
  have hreference₁ : selected Work.reference₁ = 0 := by
    simpa [selected, restored, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.reference₁] using hclean.reference₁
  have hleft :
      (BinaryRoutine.clear Work.reference₁).effect
          ((BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
            Work.available Work.savedOutput Work.reference₁).effect
            ((prepareRecentReference Work.reference₁ 1).effect selected)) =
        afterLeft := by
    rw [writtenCellLeftAnd_effect selected hreference₁]
  have hheadClean : HeadAtCurrentCellClean afterLeft := by
    refine
      { loop₃ := ?_
        temporary₃ := ?_
        reference₀ := ?_
        emitCounter := ?_
        copyCounter := ?_
        multiplyCounter := ?_
        addCounter := ?_
        temporary₀ := ?_ }
    · simpa [afterLeft, selected, restored, Work.available, Work.position,
        Work.tapeIndex, Work.symbolIndex, Work.loop₃] using hclean.loop₃
    · simpa [afterLeft, selected, restored, Work.available, Work.position,
        Work.tapeIndex, Work.symbolIndex, Work.temporary₃] using
        hclean.temporary₃
    · simpa [afterLeft, selected, restored, Work.available, Work.position,
        Work.tapeIndex, Work.symbolIndex, Work.reference₀] using
        hclean.reference₀
    · simpa [afterLeft, selected, restored, Work.available, Work.position,
        Work.tapeIndex, Work.symbolIndex, Work.emitCounter] using
        hclean.emitCounter
    · simpa [afterLeft, selected, restored, Work.available, Work.position,
        Work.tapeIndex, Work.symbolIndex, Work.copyCounter] using
        hclean.copyCounter
    · simpa [afterLeft, selected, restored, Work.available, Work.position,
        Work.tapeIndex, Work.symbolIndex, Work.multiplyCounter] using
        hclean.multiplyCounter
    · simpa [afterLeft, selected, restored, Work.available, Work.position,
        Work.tapeIndex, Work.symbolIndex, Work.addCounter] using
        hclean.addCounter
    · simpa [afterLeft, selected, restored, Work.available, Work.position,
        Work.tapeIndex, Work.symbolIndex, Work.temporary₀] using
        hclean.temporary₀
  have hreference₀Value : values 7 = 0 := by
    simpa [Work.reference₀] using hclean.reference₀
  have hreference₁Value : values 8 = 0 := by
    simpa [Work.reference₁] using hclean.reference₁
  have htemporary₀Value : values 22 = 0 := by
    simpa [Work.temporary₀] using hclean.temporary₀
  have htemporary₁Value : values 23 = 0 := by
    simpa [Work.temporary₁] using hclean.temporary₁
  have htemporary₂Value : values 24 = 0 := by
    simpa [Work.temporary₂] using hclean.temporary₂
  have htapeIndexValue : values 29 = 0 := by
    simpa [Work.tapeIndex] using hclean.tapeIndex
  have hsymbolIndexValue : values 31 = 0 := by
    simpa [Work.symbolIndex] using hclean.symbolIndex
  simp only [emitWrittenCellFinish, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [hrestore, hselect, hleft,
    emitHeadAtCurrentCell_effect_internal stateCount afterLeft hheadClean,
    emitRecentGate_effect, emitCellReference_effect, emitRecentGate_effect,
    emitRecentGate_effect]
  simp [BinaryRoutine.clear, afterLeft, selected, restored,
    Work.available, Work.position, Work.tapeIndex, Work.symbolIndex,
    Work.savedOutput, Work.limit₂, Work.reference₀, Work.reference₁,
    Work.temporary₀, Work.temporary₁, Work.temporary₂]
  funext i
  simp only [Function.update_apply]
  split_ifs <;>
    simp_all [Work.available, Work.position, Work.tapeIndex, Work.symbolIndex,
      Work.savedOutput, Work.limit₂, Work.reference₁]

private theorem emitWrittenCellFinish_emitted
    (stateCount tapeCount tapeIndex symbolIndex base effectSize : ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (hposition : values Work.limit₂ ≤ values Work.horizon + 1)
    (havailable : values Work.available = base + effectSize + 1)
    (hsavedOutput : values Work.savedOutput = base) :
    (emitWrittenCellFinish stateCount tapeCount tapeIndex symbolIndex).emitted
        values =
      (writtenCellSuffixGates stateCount tapeCount (values Work.horizon)
        (values Work.configBase) base tapeIndex (values Work.limit₂)
        symbolIndex effectSize).flatMap CircuitCode.RawGate.encode := by
  let restored := Function.update values Work.position (values Work.limit₂)
  let selected := Function.update
    (Function.update restored Work.tapeIndex tapeIndex)
    Work.symbolIndex symbolIndex
  let afterLeft := Function.update selected Work.available
    (selected Work.available + 1)
  have hrestore :
      (BinaryRoutine.binaryCopy Work.limit₂ Work.position
        Work.copyCounter).effect values = restored := rfl
  have hselect :
      (BinaryRoutine.set Work.symbolIndex symbolIndex).effect
          ((BinaryRoutine.set Work.tapeIndex tapeIndex).effect restored) =
        selected := by
    simp [selected, BinaryRoutine.set, BinaryRoutine.seq,
      BinaryRoutine.clear, BinaryRoutine.addConst, Work.tapeIndex,
      Work.symbolIndex]
  have hreference₁ : selected Work.reference₁ = 0 := by
    simpa [selected, restored, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.reference₁] using hclean.reference₁
  have hleftEffect :
      (BinaryRoutine.clear Work.reference₁).effect
          ((BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
            Work.available Work.savedOutput Work.reference₁).effect
            ((prepareRecentReference Work.reference₁ 1).effect selected)) =
        afterLeft := by
    rw [writtenCellLeftAnd_effect selected hreference₁]
  have hheadClean : HeadAtCurrentCellClean afterLeft := by
    refine
      { loop₃ := ?_
        temporary₃ := ?_
        reference₀ := ?_
        emitCounter := ?_
        copyCounter := ?_
        multiplyCounter := ?_
        addCounter := ?_
        temporary₀ := ?_ }
    all_goals
      simp [afterLeft, selected, restored, Work.available, Work.position,
        Work.tapeIndex, Work.symbolIndex] at *
      first | exact hclean.loop₃ | exact hclean.temporary₃ |
        exact hclean.reference₀ | exact hclean.emitCounter |
        exact hclean.copyCounter | exact hclean.multiplyCounter |
        exact hclean.addCounter | exact hclean.temporary₀
  have hpositionLeft :
      afterLeft Work.position ≤ afterLeft Work.horizon + 1 := by
    simpa [afterLeft, selected, restored, Work.available, Work.position,
      Work.tapeIndex, Work.symbolIndex, Work.horizon] using hposition
  have hheadEffect :
      (emitHeadAtCurrentCell stateCount).effect afterLeft =
        Function.update afterLeft Work.available
          (afterLeft Work.available + 1) :=
    emitHeadAtCurrentCell_effect_internal stateCount afterLeft hheadClean
  have havailableValue : values 5 = base + effectSize + 1 := by
    simpa [Work.available] using havailable
  have hsavedOutputValue : values 26 = base := by
    simpa [Work.savedOutput] using hsavedOutput
  have hrightInput :
      base + (effectSize + 5) - 2 = base + (effectSize + 3) := by
    omega
  have hfinalInput :
      base + (effectSize + 6) - 5 = base + (effectSize + 1) := by
    omega
  simp only [emitWrittenCellFinish, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [hrestore, hselect]
  rw [writtenCellLeftAnd_emitted_append selected, hleftEffect]
  rw [emitHeadAtCurrentCell_emitted_internal stateCount afterLeft hheadClean
    hpositionLeft, hheadEffect]
  simp [writtenCellSuffixGates, writtenCellSuffixGate, indexedGateBlocks,
    writtenCellLeftAndGate, writtenCellNegatedHeadGate,
    writtenCellOldValueGate, writtenCellRightAndGate,
    writtenCellFinalOrGate, emitRecentGate_effect,
    emitCellReference_effect, BinaryRoutine.binaryCopy, BinaryRoutine.set,
    BinaryRoutine.seq, BinaryRoutine.addConst, BinaryRoutine.clear, afterLeft,
    selected, restored, havailableValue, hsavedOutputValue, hrightInput,
    hfinalInput, Work.available,
    Work.position, Work.horizon, Work.configBase, CircuitCode.RawGate.copy,
    Nat.add_assoc,
    Work.tapeIndex, Work.symbolIndex, Work.savedOutput, Work.limit₂,
    Work.reference₀, Work.reference₁, Work.temporary₀, Work.temporary₁,
    Work.temporary₂]

private theorem emitWrittenCellFinish_requires
    (stateCount tapeCount tapeIndex symbolIndex : ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (hposition : values Work.limit₂ ≤ values Work.horizon + 1)
    (havailable : 1 ≤ values Work.available) :
    (emitWrittenCellFinish stateCount tapeCount tapeIndex symbolIndex).requires
      values := by
  let restored := Function.update values Work.position (values Work.limit₂)
  let selected := Function.update
    (Function.update restored Work.tapeIndex tapeIndex)
    Work.symbolIndex symbolIndex
  let afterLeft := Function.update selected Work.available
    (selected Work.available + 1)
  have hrestore :
      (BinaryRoutine.binaryCopy Work.limit₂ Work.position
        Work.copyCounter).effect values = restored := rfl
  have hselect :
      (BinaryRoutine.set Work.symbolIndex symbolIndex).effect
          ((BinaryRoutine.set Work.tapeIndex tapeIndex).effect restored) =
        selected := by
    simp [selected, BinaryRoutine.set, BinaryRoutine.seq,
      BinaryRoutine.clear, BinaryRoutine.addConst, Work.tapeIndex,
      Work.symbolIndex]
  have hcopyRestore :
      (BinaryRoutine.binaryCopy Work.limit₂ Work.position
        Work.copyCounter).requires values :=
    ⟨by decide, by decide, by decide, hclean.copyCounter⟩
  have hreference₁ : selected Work.reference₁ = 0 := by
    simpa [selected, restored, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.reference₁] using hclean.reference₁
  have hcopySelected : selected Work.copyCounter = 0 := by
    simpa [selected, restored, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.copyCounter] using hclean.copyCounter
  have hemitSelected : selected Work.emitCounter = 0 := by
    simpa [selected, restored, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.emitCounter] using hclean.emitCounter
  have havailableSelected : 1 ≤ selected Work.available := by
    simpa [selected, restored, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.available] using havailable
  have hleft := writtenCellLeftAnd_requires selected hcopySelected
    havailableSelected hemitSelected
  have hleftEffect :
      (BinaryRoutine.clear Work.reference₁).effect
          ((BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
            Work.available Work.savedOutput Work.reference₁).effect
            ((prepareRecentReference Work.reference₁ 1).effect selected)) =
        afterLeft := by
    rw [writtenCellLeftAnd_effect selected hreference₁]
  have hheadClean : HeadAtCurrentCellClean afterLeft := by
    refine
      { loop₃ := ?_
        temporary₃ := ?_
        reference₀ := ?_
        emitCounter := ?_
        copyCounter := ?_
        multiplyCounter := ?_
        addCounter := ?_
        temporary₀ := ?_ }
    all_goals
      simp [afterLeft, selected, restored, Work.available, Work.position,
        Work.tapeIndex, Work.symbolIndex] at *
      first | exact hclean.loop₃ | exact hclean.temporary₃ |
        exact hclean.reference₀ | exact hclean.emitCounter |
        exact hclean.copyCounter | exact hclean.multiplyCounter |
        exact hclean.addCounter | exact hclean.temporary₀
  have hpositionLeft :
      afterLeft Work.position ≤ afterLeft Work.horizon + 1 := by
    simpa [afterLeft, selected, restored, Work.available, Work.position,
      Work.tapeIndex, Work.symbolIndex, Work.horizon] using hposition
  have hhead := emitHeadAtCurrentCell_requires_internal stateCount afterLeft
    hheadClean hpositionLeft
  let afterHead := Function.update afterLeft Work.available
    (afterLeft Work.available + 1)
  have hheadEffect :
      (emitHeadAtCurrentCell stateCount).effect afterLeft = afterHead :=
    emitHeadAtCurrentCell_effect_internal stateCount afterLeft hheadClean
  have hcopy0 : values 10 = 0 := by
    simpa [Work.copyCounter] using hclean.copyCounter
  have hemit0 : values 9 = 0 := by
    simpa [Work.emitCounter] using hclean.emitCounter
  have hnegated :
      (emitRecentGate .and true true 1 1).requires afterHead := by
    apply (emitRecentGate_requires .and true true 1 1 afterHead).2
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [afterHead, afterLeft, Work.available] using hcopySelected
    · simp [afterHead, afterLeft, selected, restored, Work.available]
    · simp [afterHead, afterLeft, selected, restored, Work.available]
    · simpa [afterHead, afterLeft, Work.available] using hemitSelected
  let afterNegated :=
    (emitRecentGate .and true true 1 1).effect afterHead
  have hcell :
      (emitCellReference stateCount tapeCount).requires afterNegated := by
    apply emitCellReference_requires stateCount tapeCount false afterNegated
    all_goals
      simp [afterNegated, emitRecentGate_effect, afterHead, afterLeft,
        selected, restored, Work.available, Work.position, Work.tapeIndex,
        Work.symbolIndex, Work.reference₀, Work.reference₁,
        Work.copyCounter, Work.addCounter, Work.multiplyCounter,
        Work.emitCounter]
      first | exact hclean.copyCounter | exact hclean.addCounter |
        exact hclean.multiplyCounter | exact hclean.emitCounter
  let afterCell := (emitCellReference stateCount tapeCount).effect afterNegated
  have hright :
      (emitRecentGate .and false false 2 1).requires afterCell := by
    apply (emitRecentGate_requires .and false false 2 1 afterCell).2
    simp [afterCell, emitCellReference_effect, afterNegated,
      emitRecentGate_effect, afterHead, afterLeft, selected, restored,
      Work.available, Work.position, Work.tapeIndex, Work.symbolIndex,
      Work.reference₀, Work.reference₁, Work.temporary₀,
      Work.temporary₁, Work.temporary₂, Work.copyCounter,
      Work.emitCounter, hcopy0, hemit0]
  let afterRight := (emitRecentGate .and false false 2 1).effect afterCell
  have hfinal :
      (emitRecentGate .or false false 5 1).requires afterRight := by
    apply (emitRecentGate_requires .or false false 5 1 afterRight).2
    simp [afterRight, emitRecentGate_effect, afterCell,
      emitCellReference_effect, afterNegated, afterHead, afterLeft, selected,
      restored, Work.available, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.reference₀, Work.reference₁,
      Work.temporary₀, Work.temporary₁, Work.temporary₂,
      Work.copyCounter, Work.emitCounter, hcopy0, hemit0]
  simp only [emitWrittenCellFinish, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [hrestore, hselect, hleftEffect, hheadEffect]
  exact ⟨hcopyRestore, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩,
    hleft.1, hleft.2.1, hleft.2.2, hhead, hnegated, hcell, hright,
    hfinal, trivial, trivial, trivial, trivial, trivial⟩

set_option maxHeartbeats 800000 in
theorem emitWrittenCellFormula_requires_internal (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount)
    (hclean : WrittenCellFormulaClean values)
    (hposition : values Work.position ≤ values Work.horizon + 1) :
    (emitWrittenCellFormula tm tape symbol).requires values := by
  let tapeIndex := tape.toTapeSlot.index.val
  let symbolIndex := (CircuitUnrolling.symbolIndex symbol).val
  let start := writtenCellEffectStartValues values
  let effectSize := writtenCellEffectSize (transitionCases tm).length k
    (values Work.horizon) (writtenCellEffectSelectedAt tm tape symbol)
    (effectCaseChoiceAt tm)
  let afterEffect := Function.update start Work.available
    (start Work.available + effectSize)
  have hprefix := emitWrittenCellPrefix_requires (Fintype.card tm.Q)
    tapeIndex symbolIndex values hclean hposition
  have hprefixEffect :
      (emitWrittenCellPrefix (Fintype.card tm.Q) tapeIndex
        symbolIndex).effect values = start := by
    simpa [start] using emitWrittenCellPrefix_effect (Fintype.card tm.Q)
      tapeIndex symbolIndex values hclean
  have hstartClean : CaseFormulaClean start := by
    simpa [start] using writtenCellEffectStartValues_caseClean values hclean
  have hstartAvailable : 1 ≤ start Work.available := by
    simp [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex]
  have heffectRequires :
      (emitWrittenCellEffect tm tape symbol).requires start :=
    emitWrittenCellEffect_requires_internal tm tape symbol start hstartClean
      hstartAvailable
  have heffectEffect :
      (emitWrittenCellEffect tm tape symbol).effect start = afterEffect := by
    simpa [afterEffect, effectSize, start, writtenCellEffectStartValues,
      Work.available, Work.horizon] using
        emitWrittenCellEffect_effect_internal tm tape symbol start hstartClean
          hstartAvailable
  have hafterEffectClean : CaseFormulaClean afterEffect :=
    CaseFormulaClean.updateAvailable_for_writtenCell start hstartClean _
  have hfinishPosition :
      afterEffect Work.limit₂ ≤ afterEffect Work.horizon + 1 := by
    simpa [afterEffect, start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.horizon] using hposition
  have hfinishAvailable : 1 ≤ afterEffect Work.available := by
    simp [afterEffect, start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex]
    omega
  have hfinish := emitWrittenCellFinish_requires (Fintype.card tm.Q)
    (k + 2) tapeIndex symbolIndex afterEffect hafterEffectClean
      hfinishPosition hfinishAvailable
  apply (emitWrittenCellFormula_requires_iff_decompose tm tape symbol
    values).2
  refine ⟨?_, ?_, ?_⟩
  · simpa [tapeIndex, symbolIndex] using hprefix
  · rw [show
      (emitWrittenCellPrefix (Fintype.card tm.Q)
        tape.toTapeSlot.index.val
        (CircuitUnrolling.symbolIndex symbol).val).effect values = start by
          simpa [tapeIndex, symbolIndex] using hprefixEffect]
    exact heffectRequires
  · rw [show
      (emitWrittenCellPrefix (Fintype.card tm.Q)
        tape.toTapeSlot.index.val
        (CircuitUnrolling.symbolIndex symbol).val).effect values = start by
          simpa [tapeIndex, symbolIndex] using hprefixEffect]
    rw [heffectEffect]
    simpa [tapeIndex, symbolIndex] using hfinish

set_option maxHeartbeats 800000 in
theorem emitWrittenCellFormula_effect_internal (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount)
    (hclean : WrittenCellFormulaClean values) :
    (emitWrittenCellFormula tm tape symbol).effect values =
      Function.update values Work.available
        (values Work.available +
          writtenCellScheduleSize (transitionCases tm).length k
            (values Work.horizon)
            (writtenCellEffectSelectedAt tm tape symbol)
            (effectCaseChoiceAt tm)) := by
  let tapeIndex := tape.toTapeSlot.index.val
  let symbolIndex := (CircuitUnrolling.symbolIndex symbol).val
  let start := writtenCellEffectStartValues values
  let effectSize := writtenCellEffectSize (transitionCases tm).length k
    (values Work.horizon) (writtenCellEffectSelectedAt tm tape symbol)
    (effectCaseChoiceAt tm)
  let afterEffect := Function.update start Work.available
    (start Work.available + effectSize)
  have hprefixEffect :
      (emitWrittenCellPrefix (Fintype.card tm.Q) tapeIndex
        symbolIndex).effect values = start := by
    simpa [start] using emitWrittenCellPrefix_effect (Fintype.card tm.Q)
      tapeIndex symbolIndex values hclean
  have hstartClean : CaseFormulaClean start := by
    simpa [start] using writtenCellEffectStartValues_caseClean values hclean
  have hstartAvailable : 1 ≤ start Work.available := by
    simp [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex]
  have heffectEffect :
      (emitWrittenCellEffect tm tape symbol).effect start = afterEffect := by
    simpa [afterEffect, effectSize, start, writtenCellEffectStartValues,
      Work.available, Work.horizon] using
        emitWrittenCellEffect_effect_internal tm tape symbol start hstartClean
          hstartAvailable
  have hafterEffectClean : CaseFormulaClean afterEffect :=
    CaseFormulaClean.updateAvailable_for_writtenCell start hstartClean _
  have hsavedOutputValue : values 26 = 0 := by
    simpa [Work.savedOutput] using hclean.savedOutput
  have hlimit₂Value : values 19 = 0 := by
    simpa [Work.limit₂] using hclean.limit₂
  have htapeIndexValue : values 29 = 0 := by
    simpa [Work.position, Work.tapeIndex] using hclean.caseClean.tapeIndex
  have hsymbolIndexValue : values 31 = 0 := by
    simpa [Work.position, Work.symbolIndex] using
      hclean.caseClean.symbolIndex
  rw [emitWrittenCellFormula_effect_decompose]
  rw [show
    (emitWrittenCellPrefix (Fintype.card tm.Q)
      tape.toTapeSlot.index.val
      (CircuitUnrolling.symbolIndex symbol).val).effect values = start by
        simpa [tapeIndex, symbolIndex] using hprefixEffect]
  rw [heffectEffect]
  rw [emitWrittenCellFinish_effect (Fintype.card tm.Q) (k + 2)
    tape.toTapeSlot.index.val
    (CircuitUnrolling.symbolIndex symbol).val afterEffect hafterEffectClean]
  funext i
  by_cases havailableIndex : i = Work.available
  · subst i
    simp [afterEffect, start, writtenCellEffectStartValues,
      writtenCellScheduleSize, effectSize, Work.available, Work.position,
      Work.tapeIndex, Work.symbolIndex, Work.savedOutput, Work.limit₂]
    omega
  · by_cases hsavedOutputIndex : i = Work.savedOutput
    · subst i
      simpa [afterEffect, start, writtenCellEffectStartValues,
        Work.available, Work.position, Work.tapeIndex, Work.symbolIndex,
        Work.savedOutput, Work.limit₂] using hsavedOutputValue.symm
    · by_cases hlimit₂Index : i = Work.limit₂
      · subst i
        simpa [afterEffect, start, writtenCellEffectStartValues,
          Work.available, Work.position, Work.tapeIndex, Work.symbolIndex,
          Work.savedOutput, Work.limit₂] using hlimit₂Value.symm
      · by_cases hpositionIndex : i = Work.position
        · subst i
          simp [afterEffect, start, writtenCellEffectStartValues,
            Work.available, Work.position, Work.tapeIndex, Work.symbolIndex,
            Work.savedOutput, Work.limit₂]
        · by_cases htapeIndex : i = Work.tapeIndex
          · subst i
            simpa [afterEffect, start, writtenCellEffectStartValues,
              Work.available, Work.position, Work.tapeIndex, Work.symbolIndex,
              Work.savedOutput, Work.limit₂] using htapeIndexValue.symm
          · by_cases hsymbolIndex : i = Work.symbolIndex
            · subst i
              simpa [afterEffect, start, writtenCellEffectStartValues,
                Work.available, Work.position, Work.tapeIndex,
                Work.symbolIndex, Work.savedOutput, Work.limit₂] using
                hsymbolIndexValue.symm
            · simp [afterEffect, start, writtenCellEffectStartValues,
                writtenCellScheduleSize, Function.update_apply,
                havailableIndex, hsavedOutputIndex, hlimit₂Index,
                hpositionIndex, htapeIndex, hsymbolIndex]

set_option maxHeartbeats 800000 in
theorem emitWrittenCellFormula_emitted_internal (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount)
    (hclean : WrittenCellFormulaClean values)
    (hposition : values Work.position ≤ values Work.horizon + 1) :
    (emitWrittenCellFormula tm tape symbol).emitted values =
      (writtenCellSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k (values Work.horizon)
        (values Work.configBase) (values Work.reference₀)
        (values Work.available) tape.toTapeSlot.index.val
        (values Work.position) (CircuitUnrolling.symbolIndex symbol).val
        (writtenCellEffectSelectedAt tm tape symbol) (effectCaseChoiceAt tm)
        (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
        (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm)).flatMap
          CircuitCode.RawGate.encode := by
  let tapeIndex := tape.toTapeSlot.index.val
  let symbolIndex := (CircuitUnrolling.symbolIndex symbol).val
  let start := writtenCellEffectStartValues values
  let effectSize := writtenCellEffectSize (transitionCases tm).length k
    (values Work.horizon) (writtenCellEffectSelectedAt tm tape symbol)
    (effectCaseChoiceAt tm)
  let afterEffect := Function.update start Work.available
    (start Work.available + effectSize)
  have hprefixEffect :
      (emitWrittenCellPrefix (Fintype.card tm.Q) tapeIndex
        symbolIndex).effect values = start := by
    simpa [start] using emitWrittenCellPrefix_effect (Fintype.card tm.Q)
      tapeIndex symbolIndex values hclean
  have hprefixEmitted :
      (emitWrittenCellPrefix (Fintype.card tm.Q) tapeIndex
        symbolIndex).emitted values =
        CircuitCode.RawGate.encode
          (headAtCellFormulaGate (Fintype.card tm.Q)
            (values Work.horizon) (values Work.configBase) tapeIndex
            (values Work.position)) :=
    emitWrittenCellPrefix_emitted (Fintype.card tm.Q) tapeIndex symbolIndex
      values hclean hposition
  have hstartClean : CaseFormulaClean start := by
    simpa [start] using writtenCellEffectStartValues_caseClean values hclean
  have hstartAvailable : 1 ≤ start Work.available := by
    simp [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex]
  have heffectEffect :
      (emitWrittenCellEffect tm tape symbol).effect start = afterEffect := by
    simpa [afterEffect, effectSize, start, writtenCellEffectStartValues,
      Work.available, Work.horizon] using
        emitWrittenCellEffect_effect_internal tm tape symbol start hstartClean
          hstartAvailable
  have heffectEmitted :
      (emitWrittenCellEffect tm tape symbol).emitted start =
        (effectFormulaSchedule (transitionCases tm).length
          (Fintype.card tm.Q) k (values Work.horizon)
          (values Work.configBase) (values Work.reference₀)
          (values Work.available + 1)
          (writtenCellEffectSelectedAt tm tape symbol)
          (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
          (effectCaseInputSymbolIndexAt tm)
          (effectCaseOutputSymbolIndexAt tm)
          (effectCaseWorkSymbolIndexAt tm)).flatMap
            CircuitCode.RawGate.encode := by
    simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.horizon, Work.configBase, Work.reference₀] using
        emitWrittenCellEffect_emitted_internal tm tape symbol start hstartClean
          hstartAvailable
  have hafterEffectClean : CaseFormulaClean afterEffect :=
    CaseFormulaClean.updateAvailable_for_writtenCell start hstartClean _
  have hfinishPosition :
      afterEffect Work.limit₂ ≤ afterEffect Work.horizon + 1 := by
    simpa [afterEffect, start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.horizon] using hposition
  have hfinishAvailable :
      afterEffect Work.available = values Work.available + effectSize + 1 := by
    simp [afterEffect, start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex]
    omega
  have hfinishSaved : afterEffect Work.savedOutput = values Work.available := by
    simp [afterEffect, start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex]
  have hfinishEmitted := emitWrittenCellFinish_emitted
    (Fintype.card tm.Q) (k + 2) tapeIndex symbolIndex
    (values Work.available) effectSize afterEffect hafterEffectClean
    hfinishPosition hfinishAvailable hfinishSaved
  rw [emitWrittenCellFormula_emitted_decompose]
  rw [show
    (emitWrittenCellPrefix (Fintype.card tm.Q)
      tape.toTapeSlot.index.val
      (CircuitUnrolling.symbolIndex symbol).val).effect values = start by
        simpa [tapeIndex, symbolIndex] using hprefixEffect]
  rw [heffectEffect]
  rw [show
    (emitWrittenCellPrefix (Fintype.card tm.Q)
      tape.toTapeSlot.index.val
      (CircuitUnrolling.symbolIndex symbol).val).emitted values =
        CircuitCode.RawGate.encode
          (headAtCellFormulaGate (Fintype.card tm.Q)
            (values Work.horizon) (values Work.configBase)
            tape.toTapeSlot.index.val (values Work.position)) by
        simpa [tapeIndex, symbolIndex] using hprefixEmitted]
  rw [heffectEmitted]
  rw [show
    (emitWrittenCellFinish (Fintype.card tm.Q) (k + 2)
      tape.toTapeSlot.index.val
      (CircuitUnrolling.symbolIndex symbol).val).emitted afterEffect =
        (writtenCellSuffixGates (Fintype.card tm.Q) (k + 2)
          (afterEffect Work.horizon) (afterEffect Work.configBase)
          (values Work.available) tape.toTapeSlot.index.val
          (afterEffect Work.limit₂)
          (CircuitUnrolling.symbolIndex symbol).val effectSize).flatMap
            CircuitCode.RawGate.encode by
        simpa [tapeIndex, symbolIndex] using hfinishEmitted]
  simp [writtenCellSchedule, afterEffect, start,
    writtenCellEffectStartValues, effectSize, Work.available,
    Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
    Work.symbolIndex, Work.horizon, Work.configBase, List.append_assoc]

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
