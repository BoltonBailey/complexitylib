/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Initialization
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Offset
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Case.Defs
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Read
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Case
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Arithmetic
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.List

/-!
# Direct-unrolling transition-case generator -- proof internals
-/

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

theorem emitCaseChoice_sound_internal (choiceValue : Bool) :
    (emitCaseChoice choiceValue).Sound := by
  cases choiceValue with
  | false =>
      exact (emitCopyGate_sound Work.reference₀ false).seq
        (emitRecentGate_sound .and true true 1 1)
  | true => exact emitCopyGate_sound Work.reference₀ false

theorem emitCaseRead_sound_internal
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

private theorem emitCaseReads_sound
    (stateCount workCount count start : ℕ) (symbolAt : ℕ → ℕ) :
    (emitCaseReads stateCount workCount count start symbolAt).Sound := by
  induction count generalizing start symbolAt with
  | zero => exact BinaryRoutine.identity_sound
  | succ count ih =>
      exact (emitCaseRead_sound_internal stateCount workCount start
        (symbolAt 0)).seq
          (ih (start := start + 1)
            (symbolAt := fun index => symbolAt (index + 1)))

theorem emitCaseMembers_sound_internal
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ) :
    (emitCaseMembers stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h
  · subst routine
    exact emitCaseChoice_sound_internal choiceValue
  · subst routine
    exact emitStateReference_sound stateIndex false
  · subst routine
    exact emitCaseRead_sound_internal stateCount workCount 0 inputSymbolIndex
  · subst routine
    exact emitCaseReads_sound stateCount workCount workCount 1
      workSymbolIndexAt
  · subst routine
    exact emitCaseRead_sound_internal stateCount workCount (workCount + 1)
      outputSymbolIndex

theorem prepareCaseReadSize_sound_internal : prepareCaseReadSize.Sound := by
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

theorem emitCaseConnector_sound_internal : emitCaseConnector.Sound := by
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

theorem emitPreviousCaseReadConnector_sound_internal :
    emitPreviousCaseReadConnector.Sound :=
  (decrementReferenceBy_sound Work.reference₀ Work.temporary₃
    Work.loop₃).seq emitCaseConnector_sound_internal

theorem emitPreviousCaseChoiceConnector_sound_internal :
    emitPreviousCaseChoiceConnector.Sound :=
  (BinaryRoutine.binaryPred_sound Work.reference₀).seq
    emitCaseConnector_sound_internal

private theorem emitPreviousCaseReadConnectors_sound (count : ℕ) :
    (emitPreviousCaseReadConnectors count).Sound := by
  induction count with
  | zero => exact BinaryRoutine.identity_sound
  | succ count ih =>
      exact emitPreviousCaseReadConnector_sound_internal.seq ih

theorem emitCaseFormula_sound_internal
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ) :
    (emitCaseFormula stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h | h | h | h | h | h | h
  · subst routine
    exact emitCaseMembers_sound_internal stateCount workCount stateIndex
      inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt
  · subst routine
    exact emitConstantGate_sound true
  · subst routine
    exact prepareCaseReadSize_sound_internal
  · subst routine
    exact prepareRecentReference_sound Work.reference₀ 2
  · subst routine
    exact emitCaseConnector_sound_internal
  · subst routine
    exact emitPreviousCaseReadConnectors_sound (workCount + 2)
  · subst routine
    exact emitPreviousCaseChoiceConnector_sound_internal
  all_goals
    subst routine
    exact BinaryRoutine.clear_sound _

private theorem emitCopyGate_reference₀_requires
    (values : BinaryValues WorkCount)
    (hemit : values Work.emitCounter = 0) :
    (emitCopyGate Work.reference₀).requires values := by
  change CircuitCode.Machine.RawGateStepDistinct 9 5 7 7 ∧ values 9 = 0
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide⟩, ?_⟩
  simpa [Work.emitCounter] using hemit

private def caseReadStartValues (values : BinaryValues WorkCount)
    (tapeIndex symbolIndex : ℕ) : BinaryValues WorkCount :=
  Function.update
    (Function.update values Work.tapeIndex tapeIndex)
    Work.symbolIndex symbolIndex

private theorem caseReadStartValues_eq_effect
    (values : BinaryValues WorkCount) (tapeIndex symbolIndex : ℕ) :
    ((BinaryRoutine.set Work.symbolIndex symbolIndex).effect
      ((BinaryRoutine.set Work.tapeIndex tapeIndex).effect values)) =
        caseReadStartValues values tapeIndex symbolIndex := by
  simp [caseReadStartValues, BinaryRoutine.set, BinaryRoutine.seq,
    BinaryRoutine.clear, BinaryRoutine.addConst, Work.tapeIndex,
    Work.symbolIndex]

private theorem ReadFormulaClean.caseReadStartValues
    (values : BinaryValues WorkCount) (tapeIndex symbolIndex : ℕ)
    (hclean : ReadFormulaClean values) :
    ReadFormulaClean (caseReadStartValues values tapeIndex symbolIndex) := by
  refine
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
  · simpa [caseReadStartValues, Work.tapeIndex, Work.symbolIndex] using
      hclean.position
  · simpa [caseReadStartValues, Work.tapeIndex, Work.symbolIndex] using
      hclean.loop₀
  · simpa [caseReadStartValues, Work.tapeIndex, Work.symbolIndex] using
      hclean.limit₀
  · simpa [caseReadStartValues, Work.tapeIndex, Work.symbolIndex] using
      hclean.reference₀
  · simpa [caseReadStartValues, Work.tapeIndex, Work.symbolIndex] using
      hclean.reference₁
  · simpa [caseReadStartValues, Work.tapeIndex, Work.symbolIndex] using
      hclean.emitCounter
  · simpa [caseReadStartValues, Work.tapeIndex, Work.symbolIndex] using
      hclean.copyCounter
  · simpa [caseReadStartValues, Work.tapeIndex, Work.symbolIndex] using
      hclean.multiplyCounter
  · simpa [caseReadStartValues, Work.tapeIndex, Work.symbolIndex] using
      hclean.addCounter
  · simpa [caseReadStartValues, Work.tapeIndex, Work.symbolIndex] using
      hclean.temporary₀
  · simpa [caseReadStartValues, Work.tapeIndex, Work.symbolIndex] using
      hclean.temporary₁
  · simpa [caseReadStartValues, Work.tapeIndex, Work.symbolIndex] using
      hclean.temporary₂

private theorem ReadFormulaClean.updateAvailable
    (values : BinaryValues WorkCount) (amount : ℕ)
    (hclean : ReadFormulaClean values) :
    ReadFormulaClean (Function.update values Work.available amount) := by
  rcases hclean with
    ⟨hposition, hloop, hlimit, hreference₀, hreference₁, hemit,
      hcopy, hmultiply, hadd, htemporary₀, htemporary₁, htemporary₂⟩
  constructor <;>
    simp_all [Work.available, Work.position, Work.loop₀, Work.limit₀,
      Work.reference₀, Work.reference₁, Work.emitCounter,
      Work.copyCounter, Work.multiplyCounter, Work.addCounter,
      Work.temporary₀, Work.temporary₁, Work.temporary₂]

private theorem ReadFormulaClean.updateReference₀Zero
    (values : BinaryValues WorkCount) (hclean : ReadFormulaClean values) :
    ReadFormulaClean (Function.update values Work.reference₀ 0) := by
  rcases hclean with
    ⟨hposition, hloop, hlimit, _hreference₀, hreference₁, hemit,
      hcopy, hmultiply, hadd, htemporary₀, htemporary₁, htemporary₂⟩
  constructor <;>
    simp_all [Work.reference₀, Work.position, Work.loop₀, Work.limit₀,
      Work.reference₁, Work.emitCounter, Work.copyCounter,
      Work.multiplyCounter, Work.addCounter, Work.temporary₀,
      Work.temporary₁, Work.temporary₂]

theorem emitCaseChoice_effect_internal (choiceValue : Bool)
    (values : BinaryValues WorkCount)
    (hreference₀ : values Work.reference₀ = 0)
    (hreference₁ : values Work.reference₁ = 0) :
    (emitCaseChoice choiceValue).effect values =
      Function.update values Work.available
        (values Work.available + caseChoiceLiteralSize choiceValue) := by
  cases choiceValue with
  | true =>
      simpa [emitCaseChoice, caseChoiceLiteralSize] using
        emitCopyGate_effect_internal Work.reference₀ false values
  | false =>
      simp only [emitCaseChoice, Bool.false_eq_true, ↓reduceIte,
        BinaryRoutine.seq]
      rw [emitCopyGate_effect_internal, emitRecentGate_effect]
      funext i
      simp only [Function.update_apply]
      split_ifs <;>
        simp_all [caseChoiceLiteralSize, Work.available, Work.reference₀,
          Work.reference₁]

theorem emitCaseChoice_emitted_internal (choiceValue : Bool)
    (values : BinaryValues WorkCount) :
    (emitCaseChoice choiceValue).emitted values =
      (caseChoiceLiteralSchedule (values Work.available)
        (values Work.reference₀) choiceValue).flatMap
          CircuitCode.RawGate.encode := by
  cases choiceValue with
  | true =>
      simp [emitCaseChoice, caseChoiceLiteralSchedule,
        emitCopyGate_emitted_internal]
  | false =>
      simp only [emitCaseChoice, Bool.false_eq_true, ↓reduceIte,
        BinaryRoutine.seq]
      rw [emitCopyGate_emitted_internal, emitCopyGate_effect_internal,
        emitRecentGate_emitted]
      simp [caseChoiceLiteralSchedule, CircuitCode.RawGate.copy,
        Work.available, Work.reference₀]

theorem emitCaseChoice_requires_internal (choiceValue : Bool)
    (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0)
    (hemit : values Work.emitCounter = 0) :
    (emitCaseChoice choiceValue).requires values := by
  cases choiceValue with
  | true => exact emitCopyGate_reference₀_requires values hemit
  | false =>
      rw [emitCaseChoice, BinaryRoutine.seq]
      refine ⟨emitCopyGate_reference₀_requires values hemit, ?_⟩
      rw [emitCopyGate_effect_internal]
      apply (emitRecentGate_requires .and true true 1 1 _).2
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [Work.available, Work.copyCounter] using hcopy
      · simp [Work.available]
      · simp [Work.available]
      · have hemit' : values 9 = 0 := by
          simpa [Work.emitCounter] using hemit
        simp [Work.available, Work.emitCounter, hemit']

theorem emitCaseRead_effect_internal
    (stateCount workCount tapeIndex symbolIndex : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : ReadFormulaClean values) :
    (emitCaseRead stateCount workCount tapeIndex symbolIndex).effect values =
      Function.update (caseReadStartValues values tapeIndex symbolIndex)
        Work.available
        (values Work.available + caseReadSize (values Work.horizon)) := by
  simp only [emitCaseRead, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [caseReadStartValues_eq_effect]
  rw [emitReadFormula_effect stateCount (workCount + 2) _
    (ReadFormulaClean.caseReadStartValues values tapeIndex symbolIndex hclean)]
  simp [caseReadStartValues, caseReadSize, Work.available, Work.horizon,
    Work.tapeIndex, Work.symbolIndex]

theorem emitCaseRead_emitted_internal
    (stateCount workCount tapeIndex symbolIndex : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : ReadFormulaClean values) :
    (emitCaseRead stateCount workCount tapeIndex symbolIndex).emitted values =
      (readFormulaSchedule stateCount (workCount + 2)
        (values Work.horizon) (values Work.configBase)
        (values Work.available) tapeIndex symbolIndex).flatMap
          CircuitCode.RawGate.encode := by
  have htape :
      (BinaryRoutine.set Work.tapeIndex tapeIndex).emitted values = [] := by
    rfl
  have hsymbol :
      (BinaryRoutine.set Work.symbolIndex symbolIndex).emitted
        ((BinaryRoutine.set Work.tapeIndex tapeIndex).effect values) = [] := by
    rfl
  simp only [emitCaseRead, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [htape, hsymbol]
  simp only [List.nil_append, List.append_nil]
  rw [caseReadStartValues_eq_effect]
  rw [emitReadFormula_emitted stateCount (workCount + 2) _
    (ReadFormulaClean.caseReadStartValues values tapeIndex symbolIndex hclean)]
  simp [caseReadStartValues, Work.horizon, Work.configBase, Work.available,
    Work.tapeIndex, Work.symbolIndex]

theorem emitCaseRead_requires_internal
    (stateCount workCount tapeIndex symbolIndex : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : ReadFormulaClean values) :
    (emitCaseRead stateCount workCount tapeIndex symbolIndex).requires
      values := by
  have htape :
      (BinaryRoutine.set Work.tapeIndex tapeIndex).requires values :=
    ⟨trivial, trivial⟩
  have hsymbol :
      (BinaryRoutine.set Work.symbolIndex symbolIndex).requires
        ((BinaryRoutine.set Work.tapeIndex tapeIndex).effect values) :=
    ⟨trivial, trivial⟩
  have hread :
      (emitReadFormula stateCount (workCount + 2)).requires
        (caseReadStartValues values tapeIndex symbolIndex) :=
    emitReadFormula_requires stateCount (workCount + 2) _
      (ReadFormulaClean.caseReadStartValues values tapeIndex symbolIndex hclean)
  simp only [emitCaseRead, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [caseReadStartValues_eq_effect]
  exact ⟨htape, hsymbol, hread, trivial⟩

theorem prepareCaseReadSize_effect_internal
    (values : BinaryValues WorkCount) :
    prepareCaseReadSize.effect values =
      Function.update
        (Function.update values Work.temporary₃
          (caseReadSize (values Work.horizon))) Work.temporary₂ 0 := by
  simp [prepareCaseReadSize, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
    BinaryRoutine.mulAdd, BinaryRoutine.identity, BinaryRoutine.emitBits,
    caseReadSize, Work.horizon, Work.temporary₂, Work.temporary₃,
    Work.multiplyCounter, Work.addCounter]
  funext i
  simp only [Function.update_apply]
  split_ifs <;> omega

theorem prepareCaseReadSize_emitted_internal
    (values : BinaryValues WorkCount) :
    prepareCaseReadSize.emitted values = [] := by
  simp [prepareCaseReadSize, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
    BinaryRoutine.mulAdd, BinaryRoutine.identity, BinaryRoutine.emitBits]

theorem prepareCaseReadSize_requires_internal
    (values : BinaryValues WorkCount)
    (hmultiply : values Work.multiplyCounter = 0)
    (hadd : values Work.addCounter = 0) :
    prepareCaseReadSize.requires values := by
  simp only [prepareCaseReadSize, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  refine ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, ?_, trivial,
    trivial⟩
  change TM.BinaryMulAddDistinct 1 24 25 12 13 ∧
    (Function.update
        (Function.update
          ((BinaryRoutine.set Work.temporary₃ 5).effect values)
          Work.temporary₂ 0) Work.temporary₂ 4) 12 = 0 ∧
    (Function.update
        (Function.update
          ((BinaryRoutine.set Work.temporary₃ 5).effect values)
          Work.temporary₂ 0) Work.temporary₂ 4) 13 = 0
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩, ?_, ?_⟩
  · simpa [Work.temporary₂, Work.multiplyCounter] using hmultiply
  · simpa [Work.temporary₂, Work.addCounter] using hadd

theorem emitCaseConnector_effect_internal
    (values : BinaryValues WorkCount) :
    emitCaseConnector.effect values =
      Function.update
        (Function.update values Work.available (values Work.available + 1))
        Work.reference₁ 0 := by
  simp [emitCaseConnector, BinaryRoutine.seqList, BinaryRoutine.seq,
    prepareRecentReference_effect, BinaryRoutine.emitRawGateStep,
    BinaryRoutine.clear, BinaryRoutine.identity, BinaryRoutine.emitBits,
    Work.available, Work.reference₁]
  funext i
  simp only [Function.update_apply]
  split_ifs <;> rfl

theorem emitCaseConnector_emitted_internal
    (values : BinaryValues WorkCount) :
    emitCaseConnector.emitted values =
      CircuitCode.RawGate.encode
        { op := .and
          input₀ := values Work.reference₀
          input₁ := values Work.available - 1
          negated₀ := false
          negated₁ := false } := by
  simp [emitCaseConnector, BinaryRoutine.seqList, BinaryRoutine.seq,
    prepareRecentReference_effect, prepareRecentReference_emitted,
    BinaryRoutine.emitRawGateStep, BinaryRoutine.clear,
    BinaryRoutine.identity, BinaryRoutine.emitBits, Work.available,
    Work.reference₀, Work.reference₁]

theorem emitCaseConnector_requires_internal
    (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0)
    (havailable : 1 ≤ values Work.available)
    (hemit : values Work.emitCounter = 0) :
    emitCaseConnector.requires values := by
  have hprepare := (prepareRecentReference_requires Work.reference₁ 1 values
    (by decide) (by decide) (by decide)).2 ⟨hcopy, havailable⟩
  have hdistinct : CircuitCode.Machine.RawGateStepDistinct Work.emitCounter
      Work.available Work.reference₀ Work.reference₁ := by
    exact ⟨by decide, by decide, by decide, by decide, by decide⟩
  simp only [emitCaseConnector, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  refine ⟨hprepare, ⟨hdistinct, ?_⟩, trivial, trivial⟩
  rw [prepareRecentReference_effect]
  simpa [Work.reference₁, Work.emitCounter] using hemit

theorem emitPreviousCaseReadConnector_effect_internal
    (values : BinaryValues WorkCount)
    (hloop : values Work.loop₃ = 0) :
    emitPreviousCaseReadConnector.effect values =
      Function.update
        (Function.update
          (Function.update values Work.reference₀
            (values Work.reference₀ - values Work.temporary₃))
          Work.available (values Work.available + 1)) Work.reference₁ 0 := by
  change emitCaseConnector.effect
      ((decrementReferenceBy Work.reference₀ Work.temporary₃
        Work.loop₃).effect values) = _
  rw [decrementReferenceBy_effect Work.reference₀ Work.temporary₃ Work.loop₃
      values ⟨by decide, by decide, by decide⟩ hloop,
    emitCaseConnector_effect_internal]
  funext i
  simp only [Function.update_apply]
  split_ifs <;>
    simp_all [Work.reference₀, Work.reference₁, Work.available,
      Work.temporary₃, Work.loop₃]

theorem emitPreviousCaseReadConnector_emitted_internal
    (values : BinaryValues WorkCount)
    (hloop : values Work.loop₃ = 0) :
    emitPreviousCaseReadConnector.emitted values =
      CircuitCode.RawGate.encode
        { op := .and
          input₀ := values Work.reference₀ - values Work.temporary₃
          input₁ := values Work.available - 1
          negated₀ := false
          negated₁ := false } := by
  change
    (decrementReferenceBy Work.reference₀ Work.temporary₃
        Work.loop₃).emitted values ++
      emitCaseConnector.emitted
        ((decrementReferenceBy Work.reference₀ Work.temporary₃
          Work.loop₃).effect values) = _
  rw [decrementReferenceBy_emitted,
    decrementReferenceBy_effect Work.reference₀ Work.temporary₃ Work.loop₃
      values ⟨by decide, by decide, by decide⟩ hloop,
    emitCaseConnector_emitted_internal]
  simp [Work.reference₀, Work.available, Work.temporary₃, Work.loop₃]

theorem emitPreviousCaseReadConnector_requires_internal
    (values : BinaryValues WorkCount)
    (hloop : values Work.loop₃ = 0)
    (hoffset : values Work.temporary₃ ≤ values Work.reference₀)
    (hcopy : values Work.copyCounter = 0)
    (havailable : 1 ≤ values Work.available)
    (hemit : values Work.emitCounter = 0) :
    emitPreviousCaseReadConnector.requires values := by
  rw [emitPreviousCaseReadConnector, BinaryRoutine.seq]
  have hdecrement := (decrementReferenceBy_requires Work.reference₀
    Work.temporary₃ Work.loop₃ values).2
      ⟨⟨by decide, by decide, by decide⟩, hloop, hoffset⟩
  refine ⟨hdecrement, ?_⟩
  rw [decrementReferenceBy_effect Work.reference₀ Work.temporary₃ Work.loop₃
    values ⟨by decide, by decide, by decide⟩ hloop]
  apply emitCaseConnector_requires_internal
  · simpa [Work.reference₀, Work.loop₃, Work.copyCounter] using hcopy
  · simpa [Work.reference₀, Work.loop₃, Work.available] using
      havailable
  · simpa [Work.reference₀, Work.loop₃, Work.emitCounter] using hemit

theorem emitPreviousCaseChoiceConnector_effect_internal
    (values : BinaryValues WorkCount) :
    emitPreviousCaseChoiceConnector.effect values =
      Function.update
        (Function.update
          (Function.update values Work.reference₀
            (values Work.reference₀ - 1)) Work.available
          (values Work.available + 1)) Work.reference₁ 0 := by
  rw [emitPreviousCaseChoiceConnector, BinaryRoutine.seq,
    emitCaseConnector_effect_internal]
  simp [BinaryRoutine.binaryPred, Work.reference₀, Work.available,
    Work.reference₁]

theorem emitPreviousCaseChoiceConnector_emitted_internal
    (values : BinaryValues WorkCount) :
    emitPreviousCaseChoiceConnector.emitted values =
      CircuitCode.RawGate.encode
        { op := .and
          input₀ := values Work.reference₀ - 1
          input₁ := values Work.available - 1
          negated₀ := false
          negated₁ := false } := by
  change (BinaryRoutine.binaryPred Work.reference₀).emitted values ++
      emitCaseConnector.emitted
        ((BinaryRoutine.binaryPred Work.reference₀).effect values) = _
  rw [emitCaseConnector_emitted_internal]
  simp [BinaryRoutine.binaryPred, Work.reference₀, Work.available]

theorem emitPreviousCaseChoiceConnector_requires_internal
    (values : BinaryValues WorkCount)
    (hreference : 1 ≤ values Work.reference₀)
    (hcopy : values Work.copyCounter = 0)
    (havailable : 1 ≤ values Work.available)
    (hemit : values Work.emitCounter = 0) :
    emitPreviousCaseChoiceConnector.requires values := by
  rw [emitPreviousCaseChoiceConnector, BinaryRoutine.seq]
  refine ⟨?_, ?_⟩
  · exact hreference
  rw [show (BinaryRoutine.binaryPred Work.reference₀).effect values =
      Function.update values Work.reference₀
        (values Work.reference₀ - 1) by rfl]
  apply emitCaseConnector_requires_internal
  · simpa [Work.reference₀, Work.copyCounter] using hcopy
  · simpa [Work.reference₀, Work.available] using havailable
  · simpa [Work.reference₀, Work.emitCounter] using hemit

private theorem emitPreviousCaseReadConnectors_effect
    (count : ℕ) (values : BinaryValues WorkCount)
    (hloop : values Work.loop₃ = 0)
    (hreference₁ : values Work.reference₁ = 0) :
    (emitPreviousCaseReadConnectors count).effect values =
      Function.update
        (Function.update
          (Function.update values Work.reference₀
            (values Work.reference₀ - values Work.temporary₃ * count))
          Work.available (values Work.available + count))
        Work.reference₁ 0 := by
  induction count generalizing values with
  | zero =>
      funext i
      simp only [emitPreviousCaseReadConnectors, BinaryRoutine.identity,
        BinaryRoutine.emitBits, Nat.mul_zero, Nat.sub_zero, Nat.add_zero,
        Function.update_apply]
      split_ifs <;> simp_all [Work.reference₁]
  | succ count ih =>
      rw [emitPreviousCaseReadConnectors]
      change (emitPreviousCaseReadConnectors count).effect
        (emitPreviousCaseReadConnector.effect values) = _
      rw [emitPreviousCaseReadConnector_effect_internal values hloop]
      let current := Function.update
        (Function.update
          (Function.update values Work.reference₀
            (values Work.reference₀ - values Work.temporary₃))
          Work.available (values Work.available + 1)) Work.reference₁ 0
      have hloopCurrent : current Work.loop₃ = 0 := by
        have hloop' : values 20 = 0 := by
          simpa [Work.loop₃] using hloop
        simpa [current, Work.reference₀, Work.available,
          Work.reference₁, Work.loop₃] using hloop'
      have hreferenceCurrent : current Work.reference₁ = 0 := by
        simp [current]
      rw [ih current hloopCurrent hreferenceCurrent]
      funext i
      simp only [current, Function.update_apply]
      split_ifs <;>
        simp_all [Work.reference₀, Work.available, Work.reference₁,
          Work.temporary₃, Nat.mul_succ, Nat.sub_sub, Nat.add_assoc]
      all_goals omega

private theorem emitPreviousCaseReadConnectors_emitted
    (count : ℕ) (values : BinaryValues WorkCount)
    (hloop : values Work.loop₃ = 0)
    (hreference₁ : values Work.reference₁ = 0) :
    (emitPreviousCaseReadConnectors count).emitted values =
      (indexedGateBlocks count fun rank =>
        [{ op := .and
           input₀ := values Work.reference₀ -
             values Work.temporary₃ * (rank + 1)
           input₁ := values Work.available + rank - 1
           negated₀ := false
           negated₁ := false }]).flatMap CircuitCode.RawGate.encode := by
  induction count generalizing values with
  | zero =>
      simp [emitPreviousCaseReadConnectors, BinaryRoutine.identity,
        BinaryRoutine.emitBits, indexedGateBlocks]
  | succ count ih =>
      rw [emitPreviousCaseReadConnectors]
      change emitPreviousCaseReadConnector.emitted values ++
        (emitPreviousCaseReadConnectors count).emitted
          (emitPreviousCaseReadConnector.effect values) = _
      rw [emitPreviousCaseReadConnector_emitted_internal values hloop,
        emitPreviousCaseReadConnector_effect_internal values hloop]
      let current := Function.update
        (Function.update
          (Function.update values Work.reference₀
            (values Work.reference₀ - values Work.temporary₃))
          Work.available (values Work.available + 1)) Work.reference₁ 0
      have hloopCurrent : current Work.loop₃ = 0 := by
        have hloop' : values 20 = 0 := by
          simpa [Work.loop₃] using hloop
        simpa [current, Work.reference₀, Work.available,
          Work.reference₁, Work.loop₃] using hloop'
      have hreferenceCurrent : current Work.reference₁ = 0 := by
        simp [current]
      rw [ih current hloopCurrent hreferenceCurrent]
      simp only [indexedGateBlocks, List.flatMap_append]
      simp
      apply congrArg (List.flatMap CircuitCode.RawGate.encode)
      apply congrArg (indexedGateBlocks count)
      funext rank
      simp [current, Work.reference₀, Work.available, Work.reference₁,
        Work.temporary₃, Nat.mul_succ, Nat.sub_sub,
        Nat.add_left_comm, Nat.add_comm]
      omega

private theorem emitPreviousCaseReadConnectors_requires
    (count : ℕ) (values : BinaryValues WorkCount)
    (hloop : values Work.loop₃ = 0)
    (hreference₁ : values Work.reference₁ = 0)
    (hcopy : values Work.copyCounter = 0)
    (hemit : values Work.emitCounter = 0)
    (havailable : 1 ≤ values Work.available)
    (hoffset : ∀ rank, rank < count →
      values Work.temporary₃ * (rank + 1) ≤
        values Work.reference₀) :
    (emitPreviousCaseReadConnectors count).requires values := by
  induction count generalizing values with
  | zero =>
      simp [emitPreviousCaseReadConnectors, BinaryRoutine.identity,
        BinaryRoutine.emitBits]
  | succ count ih =>
      rw [emitPreviousCaseReadConnectors, BinaryRoutine.seq]
      have hfirstOffset :
          values Work.temporary₃ ≤ values Work.reference₀ := by
        simpa using hoffset 0 (by omega)
      refine ⟨emitPreviousCaseReadConnector_requires_internal values hloop
        hfirstOffset hcopy havailable hemit, ?_⟩
      rw [emitPreviousCaseReadConnector_effect_internal values hloop]
      let current := Function.update
        (Function.update
          (Function.update values Work.reference₀
            (values Work.reference₀ - values Work.temporary₃))
          Work.available (values Work.available + 1)) Work.reference₁ 0
      apply ih current
      · simpa [current, Work.reference₀, Work.available, Work.reference₁,
          Work.loop₃] using hloop
      · simp [current]
      · simpa [current, Work.reference₀, Work.available, Work.reference₁,
          Work.copyCounter] using hcopy
      · simpa [current, Work.reference₀, Work.available, Work.reference₁,
          Work.emitCounter] using hemit
      · simp [current, Work.reference₀, Work.available, Work.reference₁]
      · intro rank hrank
        simp only [current, Function.update_apply]
        simp [Work.reference₀, Work.available, Work.reference₁,
          Work.temporary₃]
        have hnext := hoffset (rank + 1) (by omega)
        apply Nat.le_sub_of_add_le
        calc
          values Work.temporary₃ * (rank + 1) +
                values Work.temporary₃ =
              values Work.temporary₃ * (rank + 1 + 1) := by ring
          _ ≤ values Work.reference₀ := hnext

private theorem emitIndexedCaseReads_effect_succ
    (stateCount workCount count start : ℕ) (symbolAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : ReadFormulaClean values) :
    (emitCaseReads stateCount workCount (count + 1) start
        symbolAt).effect values =
      Function.update
        (caseReadStartValues values (start + count) (symbolAt count))
        Work.available
        (values Work.available +
          caseReadSize (values Work.horizon) * (count + 1)) := by
  induction count generalizing start symbolAt values with
  | zero =>
      simp only [emitCaseReads, BinaryRoutine.seq,
        BinaryRoutine.identity, BinaryRoutine.emitBits, Nat.add_zero]
      rw [emitCaseRead_effect_internal stateCount workCount start
        (symbolAt 0) values hclean]
      funext i
      simp [caseReadStartValues, Work.available, Work.horizon,
        Work.tapeIndex, Work.symbolIndex]
  | succ count ih =>
      rw [emitCaseReads]
      simp only [BinaryRoutine.seq]
      rw [emitCaseRead_effect_internal stateCount workCount start
        (symbolAt 0) values hclean]
      let current := Function.update
        (caseReadStartValues values start (symbolAt 0)) Work.available
          (values Work.available + caseReadSize (values Work.horizon))
      have hcurrent : ReadFormulaClean current :=
        ReadFormulaClean.updateAvailable
          (caseReadStartValues values start (symbolAt 0))
          (values Work.available + caseReadSize (values Work.horizon))
          (ReadFormulaClean.caseReadStartValues values start (symbolAt 0)
            hclean)
      rw [ih (start := start + 1)
        (symbolAt := fun index => symbolAt (index + 1))
        (values := current) hcurrent]
      funext i
      simp only [current, caseReadStartValues, Function.update_apply]
      split_ifs <;>
        simp_all [Work.available, Work.horizon, Work.tapeIndex,
          Work.symbolIndex, Nat.mul_succ] <;> omega

private theorem emitIndexedCaseReads_effect_zero
    (stateCount workCount start : ℕ) (symbolAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) :
    (emitCaseReads stateCount workCount 0 start symbolAt).effect
      values = values := by
  simp [emitCaseReads, BinaryRoutine.identity, BinaryRoutine.emitBits]

set_option maxHeartbeats 800000 in
private theorem emitIndexedCaseReads_requires
    (stateCount workCount count start : ℕ) (symbolAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : ReadFormulaClean values) :
    (emitCaseReads stateCount workCount count start symbolAt).requires
      values := by
  induction count generalizing start symbolAt values with
  | zero =>
      simp [emitCaseReads, BinaryRoutine.identity,
        BinaryRoutine.emitBits]
  | succ count ih =>
      rw [emitCaseReads]
      simp only [BinaryRoutine.seq]
      have hhead := emitCaseRead_requires_internal stateCount workCount start
        (symbolAt 0) values hclean
      refine ⟨hhead, ?_⟩
      rw [emitCaseRead_effect_internal stateCount workCount start
        (symbolAt 0) values hclean]
      apply ih (start := start + 1)
        (symbolAt := fun index => symbolAt (index + 1))
      exact ReadFormulaClean.updateAvailable
        (caseReadStartValues values start (symbolAt 0))
        (values Work.available + caseReadSize (values Work.horizon))
        (ReadFormulaClean.caseReadStartValues values start (symbolAt 0)
          hclean)

private theorem emitIndexedCaseReads_emitted
    (stateCount workCount count start : ℕ) (symbolAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : ReadFormulaClean values) :
    (emitCaseReads stateCount workCount count start symbolAt).emitted
        values =
      (indexedGateBlocks count fun index =>
        readFormulaSchedule stateCount (workCount + 2)
          (values Work.horizon) (values Work.configBase)
          (values Work.available +
            caseReadSize (values Work.horizon) * index)
          (start + index) (symbolAt index)).flatMap
            CircuitCode.RawGate.encode := by
  induction count generalizing start symbolAt values with
  | zero =>
      simp [emitCaseReads, BinaryRoutine.identity,
        BinaryRoutine.emitBits, indexedGateBlocks]
  | succ count ih =>
      rw [emitCaseReads]
      simp only [BinaryRoutine.seq]
      rw [emitCaseRead_emitted_internal stateCount workCount start
          (symbolAt 0) values hclean,
        emitCaseRead_effect_internal stateCount workCount start
          (symbolAt 0) values hclean]
      let current := Function.update
        (caseReadStartValues values start (symbolAt 0)) Work.available
          (values Work.available + caseReadSize (values Work.horizon))
      have hcurrent : ReadFormulaClean current :=
        ReadFormulaClean.updateAvailable
          (caseReadStartValues values start (symbolAt 0))
          (values Work.available + caseReadSize (values Work.horizon))
          (ReadFormulaClean.caseReadStartValues values start (symbolAt 0)
            hclean)
      rw [ih (start := start + 1)
        (symbolAt := fun index => symbolAt (index + 1))
        (values := current) hcurrent]
      simp only [indexedGateBlocks, List.flatMap_append]
      simp [current, caseReadStartValues, Work.horizon, Work.configBase,
        Work.available, Work.tapeIndex, Work.symbolIndex, Nat.mul_add,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem emitCaseMembers_effect_internal
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitCaseMembers stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).effect values =
      Function.update
        (caseReadStartValues values (workCount + 1) outputSymbolIndex)
        Work.available
        (values Work.available +
          caseFormulaMembersSize workCount (values Work.horizon)
            choiceValue) := by
  rw [emitCaseMembers]
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [emitCaseChoice_effect_internal choiceValue values hclean.reference₀
      hclean.reference₁,
    emitStateReference_effect]
  let afterState := Function.update
    (Function.update
      (Function.update values Work.available
        (values Work.available + caseChoiceLiteralSize choiceValue))
      Work.available
      ((Function.update values Work.available
        (values Work.available + caseChoiceLiteralSize choiceValue))
          Work.available + 1)) Work.reference₀ 0
  have hafterState : ReadFormulaClean afterState :=
    ReadFormulaClean.updateReference₀Zero _
      (ReadFormulaClean.updateAvailable _ _
        (ReadFormulaClean.updateAvailable values _ hclean.toReadFormulaClean))
  rw [emitCaseRead_effect_internal stateCount workCount 0 inputSymbolIndex
    afterState hafterState]
  let afterInput := Function.update
    (caseReadStartValues afterState 0 inputSymbolIndex) Work.available
      (afterState Work.available + caseReadSize (afterState Work.horizon))
  have hafterInput : ReadFormulaClean afterInput :=
    ReadFormulaClean.updateAvailable _ _
      (ReadFormulaClean.caseReadStartValues afterState 0 inputSymbolIndex
        hafterState)
  have hreference₀ : values 7 = 0 := by
    simpa [Work.reference₀] using hclean.reference₀
  simp only [id_eq]
  cases workCount with
  | zero =>
      rw [emitIndexedCaseReads_effect_zero]
      rw [emitCaseRead_effect_internal stateCount 0 1 outputSymbolIndex
        afterInput hafterInput]
      funext i
      simp only [afterInput, afterState, caseReadStartValues,
        caseFormulaMembersSize, caseChoiceLiteralSize, caseReadSize,
        Work.available, Work.horizon, Work.reference₀, Work.tapeIndex,
        Work.symbolIndex, Function.update_apply]
      split_ifs <;> simp_all
      all_goals omega
  | succ workCount =>
      rw [emitIndexedCaseReads_effect_succ stateCount (workCount + 1)
        workCount 1 workSymbolIndexAt afterInput hafterInput]
      let afterWork := Function.update
        (caseReadStartValues afterInput (1 + workCount)
          (workSymbolIndexAt workCount)) Work.available
        (afterInput Work.available +
          caseReadSize (afterInput Work.horizon) * (workCount + 1))
      have hafterWork : ReadFormulaClean afterWork :=
        ReadFormulaClean.updateAvailable _ _
          (ReadFormulaClean.caseReadStartValues afterInput (1 + workCount)
            (workSymbolIndexAt workCount) hafterInput)
      rw [emitCaseRead_effect_internal stateCount (workCount + 1)
        (workCount + 2) outputSymbolIndex afterWork hafterWork]
      funext i
      simp only [afterWork, afterInput, afterState, caseReadStartValues,
        caseFormulaMembersSize, caseChoiceLiteralSize, caseReadSize,
        Work.available, Work.horizon, Work.reference₀, Work.tapeIndex,
        Work.symbolIndex, Nat.mul_succ, Function.update_apply]
      split_ifs <;> simp_all
      all_goals first
        | omega
        | cases choiceValue <;> norm_num at * <;> ring

theorem emitCaseMembers_requires_internal
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitCaseMembers stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).requires values := by
  rw [emitCaseMembers]
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  refine ⟨emitCaseChoice_requires_internal choiceValue values
    hclean.copyCounter hclean.emitCounter, ?_⟩
  rw [emitCaseChoice_effect_internal choiceValue values hclean.reference₀
    hclean.reference₁]
  let afterChoice := Function.update values Work.available
    (values Work.available + caseChoiceLiteralSize choiceValue)
  have hafterChoice : ReadFormulaClean afterChoice :=
    ReadFormulaClean.updateAvailable values _ hclean.toReadFormulaClean
  refine ⟨emitStateReference_requires stateIndex false afterChoice
    hafterChoice.addCounter hafterChoice.emitCounter, ?_⟩
  rw [emitStateReference_effect]
  have hafterState : ReadFormulaClean
      (Function.update
        (Function.update afterChoice Work.available
          (afterChoice Work.available + 1)) Work.reference₀ 0) :=
    ReadFormulaClean.updateReference₀Zero _
      (ReadFormulaClean.updateAvailable afterChoice _ hafterChoice)
  refine ⟨emitCaseRead_requires_internal stateCount workCount 0
    inputSymbolIndex _ hafterState, ?_⟩
  rw [emitCaseRead_effect_internal stateCount workCount 0 inputSymbolIndex
    _ hafterState]
  let afterState := Function.update
    (Function.update afterChoice Work.available
      (afterChoice Work.available + 1)) Work.reference₀ 0
  have hafterInput : ReadFormulaClean
      (Function.update (caseReadStartValues afterState 0 inputSymbolIndex)
        Work.available
        (afterState Work.available + caseReadSize (afterState Work.horizon))) :=
    ReadFormulaClean.updateAvailable _ _
      (ReadFormulaClean.caseReadStartValues afterState 0 inputSymbolIndex
        hafterState)
  refine ⟨emitIndexedCaseReads_requires stateCount workCount workCount 1
    workSymbolIndexAt _ hafterInput, ?_⟩
  cases workCount with
  | zero =>
      rw [emitIndexedCaseReads_effect_zero]
      constructor
      · apply emitCaseRead_requires_internal
        simpa only [afterState] using hafterInput
      · trivial
  | succ workCount =>
      rw [emitIndexedCaseReads_effect_succ stateCount (workCount + 1)
        workCount 1 workSymbolIndexAt _ hafterInput]
      constructor
      · apply emitCaseRead_requires_internal
        exact ReadFormulaClean.updateAvailable _ _
          (ReadFormulaClean.caseReadStartValues _ (1 + workCount)
            (workSymbolIndexAt workCount) hafterInput)
      · trivial

theorem emitCaseMembers_emitted_internal
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitCaseMembers stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).emitted values =
      (caseFormulaMemberGates stateCount workCount (values Work.horizon)
        (values Work.configBase) (values Work.reference₀)
        (values Work.available) stateIndex inputSymbolIndex
        outputSymbolIndex choiceValue workSymbolIndexAt).flatMap
          CircuitCode.RawGate.encode := by
  rw [emitCaseMembers]
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [emitCaseChoice_emitted_internal choiceValue values,
    emitCaseChoice_effect_internal choiceValue values hclean.reference₀
      hclean.reference₁]
  let afterChoice := Function.update values Work.available
    (values Work.available + caseChoiceLiteralSize choiceValue)
  have hafterChoice : ReadFormulaClean afterChoice :=
    ReadFormulaClean.updateAvailable values _ hclean.toReadFormulaClean
  rw [emitStateReference_emitted, emitStateReference_effect]
  have hafterState : ReadFormulaClean
      (Function.update
        (Function.update afterChoice Work.available
          (afterChoice Work.available + 1)) Work.reference₀ 0) :=
    ReadFormulaClean.updateReference₀Zero _
      (ReadFormulaClean.updateAvailable afterChoice _ hafterChoice)
  rw [emitCaseRead_emitted_internal stateCount workCount 0 inputSymbolIndex
      _ hafterState,
    emitCaseRead_effect_internal stateCount workCount 0 inputSymbolIndex
      _ hafterState]
  let afterState := Function.update
    (Function.update afterChoice Work.available
      (afterChoice Work.available + 1)) Work.reference₀ 0
  have hafterInput : ReadFormulaClean
      (Function.update (caseReadStartValues afterState 0 inputSymbolIndex)
        Work.available
        (afterState Work.available + caseReadSize (afterState Work.horizon))) :=
    ReadFormulaClean.updateAvailable _ _
      (ReadFormulaClean.caseReadStartValues afterState 0 inputSymbolIndex
        hafterState)
  rw [emitIndexedCaseReads_emitted stateCount workCount workCount 1
    workSymbolIndexAt _ hafterInput]
  cases workCount with
  | zero =>
      rw [emitIndexedCaseReads_effect_zero]
      rw [emitCaseRead_emitted_internal stateCount 0 1 outputSymbolIndex _
        (by simpa only [afterState] using hafterInput)]
      simp only [List.append_nil]
      simp [caseFormulaMemberGates, caseWorkReadGates,
        caseInputReadAvailable, caseOutputReadAvailable,
        caseChoiceLiteralSize, indexedGateBlocks, List.flatMap_append,
        afterChoice, caseReadStartValues, Work.available,
        Work.horizon, Work.configBase, Work.reference₀, Work.tapeIndex,
        Work.symbolIndex]
  | succ workCount =>
      rw [emitIndexedCaseReads_effect_succ stateCount (workCount + 1)
        workCount 1 workSymbolIndexAt _ hafterInput]
      let afterInput := Function.update
        (caseReadStartValues afterState 0 inputSymbolIndex) Work.available
        (afterState Work.available + caseReadSize (afterState Work.horizon))
      have hafterWork : ReadFormulaClean
          (Function.update
            (caseReadStartValues afterInput (1 + workCount)
              (workSymbolIndexAt workCount)) Work.available
            (afterInput Work.available +
              caseReadSize (afterInput Work.horizon) * (workCount + 1))) :=
        ReadFormulaClean.updateAvailable _ _
          (ReadFormulaClean.caseReadStartValues afterInput (1 + workCount)
            (workSymbolIndexAt workCount) hafterInput)
      rw [emitCaseRead_emitted_internal stateCount (workCount + 1)
        (workCount + 2) outputSymbolIndex _
          (by simpa only [afterInput, afterState] using hafterWork)]
      simp only [List.append_nil]
      simp [caseFormulaMemberGates, caseWorkReadGates,
        caseInputReadAvailable, caseWorkReadAvailable,
        caseOutputReadAvailable, caseChoiceLiteralSize,
        List.flatMap_append, afterState, afterChoice, caseReadStartValues,
        Work.available, Work.horizon, Work.configBase, Work.reference₀,
        Work.tapeIndex, Work.symbolIndex, Nat.mul_succ,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private def caseFormulaConnectorStartValues
    (values : BinaryValues WorkCount) (workCount outputSymbolIndex : ℕ)
    (choiceValue : Bool) : BinaryValues WorkCount :=
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (caseReadStartValues values (workCount + 1) outputSymbolIndex)
            Work.temporary₃ (caseReadSize (values Work.horizon)))
          Work.temporary₂ 0) Work.reference₀
        (values Work.available +
          caseFormulaMembersSize workCount (values Work.horizon) choiceValue -
          1)) Work.available
      (values Work.available +
        caseFormulaMembersSize workCount (values Work.horizon) choiceValue + 2))
    Work.reference₁ 0

private theorem caseFormulaConnectorStart_effect
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    emitCaseConnector.effect
        ((prepareRecentReference Work.reference₀ 2).effect
          (prepareCaseReadSize.effect
            ((emitConstantGate true).effect
              ((emitCaseMembers stateCount workCount stateIndex
                inputSymbolIndex outputSymbolIndex choiceValue
                workSymbolIndexAt).effect values)))) =
      caseFormulaConnectorStartValues values workCount outputSymbolIndex
        choiceValue := by
  rw [emitCaseMembers_effect_internal stateCount workCount stateIndex
      inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt values
      hclean,
    emitConstantGate_effect_internal, prepareCaseReadSize_effect_internal,
    prepareRecentReference_effect, emitCaseConnector_effect_internal]
  funext i
  simp only [caseFormulaConnectorStartValues, caseReadStartValues,
    Work.horizon, Work.available, Work.reference₀, Work.reference₁, Work.temporary₂,
    Work.temporary₃, Work.tapeIndex, Work.symbolIndex,
    Function.update_apply]
  split_ifs <;> simp_all

theorem emitCaseFormula_effect_internal
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitCaseFormula stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).effect values =
      Function.update values Work.available
        (values Work.available +
          caseFormulaScheduleSize workCount (values Work.horizon)
            choiceValue) := by
  simp only [emitCaseFormula, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [caseFormulaConnectorStart_effect stateCount workCount stateIndex
    inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt values
    hclean]
  let beforeReads := caseFormulaConnectorStartValues values workCount
    outputSymbolIndex choiceValue
  have hloop : beforeReads Work.loop₃ = 0 := by
    have hloop' : values 20 = 0 := by
      simpa [Work.loop₃] using hclean.loop₃
    simpa [beforeReads, caseFormulaConnectorStartValues,
      caseReadStartValues, Work.available, Work.reference₀, Work.reference₁,
      Work.loop₃, Work.temporary₂, Work.temporary₃, Work.tapeIndex,
      Work.symbolIndex] using hloop'
  have hreference₁ : beforeReads Work.reference₁ = 0 := by
    simp [beforeReads, caseFormulaConnectorStartValues]
  rw [emitPreviousCaseReadConnectors_effect (workCount + 2) beforeReads
    hloop hreference₁]
  rw [emitPreviousCaseChoiceConnector_effect_internal]
  have hreference₀' : values 7 = 0 := by
    simpa [Work.reference₀] using hclean.reference₀
  have hreference₁' : values 8 = 0 := by
    simpa [Work.reference₁] using hclean.reference₁
  have htemporary₃' : values 25 = 0 := by
    simpa [Work.temporary₃] using hclean.temporary₃
  have htemporary₂' : values 24 = 0 := by
    simpa [Work.temporary₂] using hclean.temporary₂
  have htapeIndex' : values 29 = 0 := by
    simpa [Work.tapeIndex] using hclean.tapeIndex
  have hsymbolIndex' : values 31 = 0 := by
    simpa [Work.symbolIndex] using hclean.symbolIndex
  funext i
  simp only [beforeReads, caseFormulaConnectorStartValues,
    BinaryRoutine.clear, caseReadStartValues, caseFormulaScheduleSize,
    caseFormulaMembersSize, caseFormulaMemberCount, caseReadSize,
    Work.horizon, Work.available, Work.reference₀, Work.reference₁,
    Work.temporary₂, Work.temporary₃, Work.tapeIndex,
    Work.symbolIndex, WorkCount]
  simp_rw [Function.update_apply]
  split_ifs <;> simp_all [Nat.mul_succ] <;> try omega
  all_goals simp_rw [Function.update_apply]
  all_goals split_ifs <;> simp_all

theorem emitCaseFormula_requires_internal
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitCaseFormula stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).requires values := by
  simp only [emitCaseFormula, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  refine ⟨emitCaseMembers_requires_internal stateCount workCount stateIndex
    inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt values
    hclean, ?_⟩
  refine ⟨?_, ?_⟩
  · apply emitConstantGate_requires_internal
    rw [emitCaseMembers_effect_internal stateCount workCount stateIndex
      inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt values
      hclean]
    simpa [Work.tapeIndex, Work.symbolIndex, Work.available,
      Work.emitCounter] using hclean.emitCounter
  refine ⟨?_, ?_⟩
  · apply prepareCaseReadSize_requires_internal
    · rw [emitConstantGate_effect_internal,
        emitCaseMembers_effect_internal stateCount workCount stateIndex
          inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt
          values hclean]
      simpa [Work.tapeIndex, Work.symbolIndex, Work.available,
        Work.multiplyCounter] using hclean.multiplyCounter
    · rw [emitConstantGate_effect_internal,
        emitCaseMembers_effect_internal stateCount workCount stateIndex
          inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt
          values hclean]
      simpa [Work.tapeIndex, Work.symbolIndex, Work.available,
        Work.addCounter] using hclean.addCounter
  refine ⟨?_, ?_⟩
  · apply (prepareRecentReference_requires Work.reference₀ 2 _
      (by decide) (by decide) (by decide)).2
    constructor
    · rw [prepareCaseReadSize_effect_internal,
        emitConstantGate_effect_internal,
        emitCaseMembers_effect_internal stateCount workCount stateIndex
          inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt
          values hclean]
      simpa [Work.temporary₂, Work.temporary₃, Work.tapeIndex,
        Work.symbolIndex, Work.available, Work.copyCounter] using
        hclean.copyCounter
    · rw [prepareCaseReadSize_effect_internal,
        emitConstantGate_effect_internal,
        emitCaseMembers_effect_internal stateCount workCount stateIndex
          inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt
          values hclean]
      cases choiceValue <;>
        simp [caseFormulaMembersSize, caseChoiceLiteralSize, caseReadSize,
          Work.temporary₂, Work.temporary₃, Work.available] <;> omega
  refine ⟨?_, ?_⟩
  · apply emitCaseConnector_requires_internal
    · rw [prepareRecentReference_effect,
        prepareCaseReadSize_effect_internal,
        emitConstantGate_effect_internal,
        emitCaseMembers_effect_internal stateCount workCount stateIndex
          inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt
          values hclean]
      simpa [Work.reference₀, Work.temporary₂, Work.temporary₃,
        Work.tapeIndex, Work.symbolIndex, Work.available,
        Work.copyCounter] using hclean.copyCounter
    · rw [prepareRecentReference_effect,
        prepareCaseReadSize_effect_internal,
        emitConstantGate_effect_internal,
        emitCaseMembers_effect_internal stateCount workCount stateIndex
          inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt
          values hclean]
      cases choiceValue <;>
        simp [caseFormulaMembersSize, caseChoiceLiteralSize, caseReadSize,
          Work.reference₀, Work.temporary₂, Work.temporary₃,
          Work.available]
    · rw [prepareRecentReference_effect,
        prepareCaseReadSize_effect_internal,
        emitConstantGate_effect_internal,
        emitCaseMembers_effect_internal stateCount workCount stateIndex
          inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt
          values hclean]
      simpa [Work.reference₀, Work.temporary₂, Work.temporary₃,
        Work.tapeIndex, Work.symbolIndex, Work.available,
        Work.emitCounter] using hclean.emitCounter
  rw [caseFormulaConnectorStart_effect stateCount workCount stateIndex
    inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt values
    hclean]
  let beforeReads := caseFormulaConnectorStartValues values workCount
    outputSymbolIndex choiceValue
  have hloop : beforeReads Work.loop₃ = 0 := by
    simpa [beforeReads, caseFormulaConnectorStartValues,
      caseReadStartValues, Work.loop₃, Work.available, Work.reference₀,
      Work.reference₁, Work.temporary₂, Work.temporary₃,
      Work.tapeIndex, Work.symbolIndex] using hclean.loop₃
  have hreference₁ : beforeReads Work.reference₁ = 0 := by
    simp [beforeReads, caseFormulaConnectorStartValues]
  have hbeforeAvailable : beforeReads Work.available =
      values Work.available +
        caseFormulaMembersSize workCount (values Work.horizon) choiceValue +
          2 := by
    simp [beforeReads, caseFormulaConnectorStartValues, caseReadStartValues,
      Work.available, Work.reference₀, Work.reference₁,
      Work.temporary₂, Work.temporary₃, Work.tapeIndex,
      Work.symbolIndex]
  have hbeforeReference₀ : beforeReads Work.reference₀ =
      values Work.available +
        caseFormulaMembersSize workCount (values Work.horizon) choiceValue -
          1 := by
    simp [beforeReads, caseFormulaConnectorStartValues, caseReadStartValues,
      Work.available, Work.reference₀, Work.reference₁,
      Work.temporary₂, Work.temporary₃, Work.tapeIndex,
      Work.symbolIndex]
  have hbeforeTemporary₃ : beforeReads Work.temporary₃ =
      caseReadSize (values Work.horizon) := by
    simp [beforeReads, caseFormulaConnectorStartValues, caseReadStartValues,
      Work.available, Work.reference₀, Work.reference₁,
      Work.temporary₂, Work.temporary₃, Work.tapeIndex,
      Work.symbolIndex]
  have hbeforeCopy : beforeReads Work.copyCounter = 0 := by
    simpa [beforeReads, caseFormulaConnectorStartValues,
      caseReadStartValues, Work.available, Work.reference₀,
      Work.reference₁, Work.temporary₂, Work.temporary₃,
      Work.tapeIndex, Work.symbolIndex, Work.copyCounter] using
      hclean.copyCounter
  have hbeforeEmit : beforeReads Work.emitCounter = 0 := by
    simpa [beforeReads, caseFormulaConnectorStartValues,
      caseReadStartValues, Work.available, Work.reference₀,
      Work.reference₁, Work.temporary₂, Work.temporary₃,
      Work.tapeIndex, Work.symbolIndex, Work.emitCounter] using
      hclean.emitCounter
  refine ⟨emitPreviousCaseReadConnectors_requires (workCount + 2)
    beforeReads hloop hreference₁ ?_ ?_ ?_ ?_, ?_⟩
  · exact hbeforeCopy
  · exact hbeforeEmit
  · rw [hbeforeAvailable]
    omega
  · intro rank hrank
    rw [hbeforeReference₀, hbeforeTemporary₃]
    have hrankle : rank + 1 ≤ workCount + 2 := by omega
    calc
      caseReadSize (values Work.horizon) * (rank + 1) ≤
          caseReadSize (values Work.horizon) * (workCount + 2) :=
        Nat.mul_le_mul_left _ hrankle
      _ ≤ values Work.available +
          caseFormulaMembersSize workCount (values Work.horizon)
            choiceValue - 1 := by
        rw [caseFormulaMembersSize, Nat.mul_comm
          (caseReadSize (values Work.horizon)) (workCount + 2)]
        cases choiceValue <;> simp [caseChoiceLiteralSize] <;> omega
  rw [emitPreviousCaseReadConnectors_effect (workCount + 2) beforeReads
    hloop hreference₁]
  refine ⟨emitPreviousCaseChoiceConnector_requires_internal _ ?_ ?_ ?_ ?_,
    ⟨trivial, trivial, trivial, trivial, trivial⟩⟩
  · have hremaining : beforeReads Work.reference₀ -
        beforeReads Work.temporary₃ * (workCount + 2) =
          values Work.available + caseChoiceLiteralSize choiceValue := by
      rw [hbeforeReference₀, hbeforeTemporary₃,
        caseFormulaMembersSize, Nat.mul_comm
          (caseReadSize (values Work.horizon)) (workCount + 2)]
      cases choiceValue <;> simp [caseChoiceLiteralSize] <;> omega
    simpa [Work.reference₀, Work.reference₁, Work.available,
      hremaining] using show
        1 ≤ beforeReads Work.reference₀ -
          beforeReads Work.temporary₃ * (workCount + 2) by
        rw [hremaining]
        cases choiceValue <;> simp [caseChoiceLiteralSize]
  · simpa [Work.reference₀, Work.reference₁, Work.available,
      Work.copyCounter] using hbeforeCopy
  · simpa [Work.reference₀, Work.reference₁, Work.available] using
      show 1 ≤ beforeReads Work.available + (workCount + 2) by
        rw [hbeforeAvailable]
        omega
  · simpa [Work.reference₀, Work.reference₁, Work.available,
      Work.emitCounter] using hbeforeEmit

private theorem prefixSize_caseFormulaSizeAt_two_add
    (workCount T : ℕ) (choiceValue : Bool) (offset : ℕ)
    (hoffset : 2 + offset ≤ caseFormulaMemberCount workCount) :
    prefixSize (caseFormulaSizeAt workCount T choiceValue) (2 + offset) =
      caseChoiceLiteralSize choiceValue + 1 + offset * caseReadSize T := by
  induction offset with
  | zero => simp [prefixSize, caseFormulaSizeAt]
  | succ offset ih =>
      rw [show 2 + (offset + 1) = (2 + offset) + 1 by omega,
        prefixSize_succ_internal, ih (by omega)]
      have hindex : 2 + offset < caseFormulaMemberCount workCount := by
        omega
      have hneOne : 2 + offset ≠ 1 := by omega
      simp [caseFormulaSizeAt, hindex, hneOne, Nat.add_mul,
        Nat.add_assoc]

private theorem getElem_indexedCaseConnectorBlocks
    (count : ℕ) (gateAt : ℕ → CircuitCode.RawGate)
    (index : ℕ) (hindex : index < count) :
    (indexedGateBlocks count fun rank => [gateAt rank])[index]'(by
      rw [length_indexedGateBlocks count 1 _ (by simp)]
      omega) = gateAt index := by
  have hget := getElem_indexedGateBlocks count 1
    (fun rank => [gateAt rank]) (by simp) index 0 hindex (by omega)
  simpa using hget

private theorem initialCaseConnector_eq
    (workCount T available : ℕ) (choiceValue : Bool) :
    ({ op := .and
       input₀ := available + caseFormulaMembersSize workCount T choiceValue - 1
       input₁ := available + caseFormulaMembersSize workCount T choiceValue
       negated₀ := false
       negated₁ := false } : CircuitCode.RawGate) =
      indexedRightFoldConnector .and available
        (caseFormulaMemberCount workCount)
        (caseFormulaSizeAt workCount T choiceValue) 0 := by
  unfold indexedRightFoldConnector reverseMember
  dsimp only
  have hcount : caseFormulaMemberCount workCount - 0 - 1 + 1 =
      caseFormulaMemberCount workCount := by
    simp [caseFormulaMemberCount]
  have hcountForm : caseFormulaMemberCount workCount =
      2 + (workCount + 2) := by
    simp only [caseFormulaMemberCount]
    omega
  rw [hcount, hcountForm,
    prefixSize_caseFormulaSizeAt_two_add workCount T choiceValue
      (workCount + 2) (by
        simp only [caseFormulaMemberCount]
        omega)]
  simp [caseFormulaMembersSize]

private theorem middleCaseConnector_eq
    (workCount T available : ℕ) (choiceValue : Bool)
    (rank : ℕ) (hrank : rank < workCount + 2) :
    ({ op := .and
       input₀ := available +
         caseFormulaMembersSize workCount T choiceValue - 1 -
           caseReadSize T * (rank + 1)
       input₁ := available +
         caseFormulaMembersSize workCount T choiceValue + 2 + rank - 1
       negated₀ := false
       negated₁ := false } : CircuitCode.RawGate) =
      indexedRightFoldConnector .and available
        (caseFormulaMemberCount workCount)
        (caseFormulaSizeAt workCount T choiceValue) (rank + 1) := by
  unfold indexedRightFoldConnector reverseMember
  dsimp only
  have hmember : caseFormulaMemberCount workCount - (rank + 1) - 1 + 1 =
      2 + (workCount + 1 - rank) := by
    simp [caseFormulaMemberCount]
    omega
  rw [hmember,
    prefixSize_caseFormulaSizeAt_two_add workCount T choiceValue
      (workCount + 1 - rank) (by
        simp only [caseFormulaMemberCount]
        omega)]
  have hcountForm : caseFormulaMemberCount workCount =
      2 + (workCount + 2) := by
    simp only [caseFormulaMemberCount]
    omega
  rw [hcountForm, prefixSize_caseFormulaSizeAt_two_add workCount T choiceValue
    (workCount + 2) (by
      simp only [caseFormulaMemberCount]
      omega)]
  have hsplit : workCount + 2 =
      (workCount + 1 - rank) + (rank + 1) := by omega
  rw [caseFormulaMembersSize, hsplit, Nat.add_mul]
  rw [Nat.mul_comm (caseReadSize T) (rank + 1)]
  simp only [CircuitCode.RawGate.mk.injEq]
  constructor
  all_goals cases choiceValue <;>
    simp [caseChoiceLiteralSize, caseFormulaMemberCount] at * <;> omega

private theorem lastCaseConnector_eq
    (workCount T available : ℕ) (choiceValue : Bool) :
    ({ op := .and
       input₀ := available +
         caseFormulaMembersSize workCount T choiceValue - 1 -
           caseReadSize T * (workCount + 2) - 1
       input₁ := available +
         caseFormulaMembersSize workCount T choiceValue + 2 +
           (workCount + 2) - 1
       negated₀ := false
       negated₁ := false } : CircuitCode.RawGate) =
      indexedRightFoldConnector .and available
        (caseFormulaMemberCount workCount)
        (caseFormulaSizeAt workCount T choiceValue) (workCount + 3) := by
  unfold indexedRightFoldConnector reverseMember
  dsimp only
  have hmember : caseFormulaMemberCount workCount - (workCount + 3) - 1 + 1 =
      1 := by
    simp [caseFormulaMemberCount]
  rw [hmember]
  have hcountForm : caseFormulaMemberCount workCount =
      2 + (workCount + 2) := by
    simp only [caseFormulaMemberCount]
    omega
  rw [hcountForm, prefixSize_caseFormulaSizeAt_two_add workCount T choiceValue
    (workCount + 2) (by
      simp only [caseFormulaMemberCount]
      omega)]
  simp [prefixSize, caseFormulaSizeAt, caseFormulaMembersSize]
  rw [Nat.mul_comm (caseReadSize T) (workCount + 2)]
  constructor
  · cases choiceValue <;> simp [caseChoiceLiteralSize] <;> omega
  · omega

private theorem caseConnectorGates_eq
    (workCount T available : ℕ) (choiceValue : Bool) :
    (([({ op := .and
          input₀ := available +
            caseFormulaMembersSize workCount T choiceValue - 1
          input₁ := available +
            caseFormulaMembersSize workCount T choiceValue
          negated₀ := false
          negated₁ := false } : CircuitCode.RawGate)] ++
      indexedGateBlocks (workCount + 2) fun rank =>
        [({ op := .and
            input₀ := available +
              caseFormulaMembersSize workCount T choiceValue - 1 -
                caseReadSize T * (rank + 1)
            input₁ := available +
              caseFormulaMembersSize workCount T choiceValue + 2 + rank - 1
            negated₀ := false
            negated₁ := false } : CircuitCode.RawGate)]) ++
      [({ op := .and
          input₀ := available +
            caseFormulaMembersSize workCount T choiceValue - 1 -
              caseReadSize T * (workCount + 2) - 1
          input₁ := available +
            caseFormulaMembersSize workCount T choiceValue + 2 +
              (workCount + 2) - 1
          negated₀ := false
          negated₁ := false } : CircuitCode.RawGate)]) =
      indexedRightFoldConnectors .and available
        (caseFormulaMemberCount workCount)
        (caseFormulaSizeAt workCount T choiceValue) := by
  apply List.ext_getElem
  · simp [length_indexedGateBlocks, length_indexedRightFoldConnectors,
      caseFormulaMemberCount]
  · intro index hleft hright
    have hindex : index < workCount + 4 := by
      simpa [length_indexedRightFoldConnectors,
        caseFormulaMemberCount] using hright
    by_cases hzero : index = 0
    · subst index
      rw [List.getElem_append_left (by
        simp [length_indexedGateBlocks])]
      rw [List.getElem_append_left (by simp)]
      simp only [List.getElem_cons_zero]
      exact (initialCaseConnector_eq workCount T available choiceValue).trans
        (getElem_indexedRightFoldConnectors .and available
          (caseFormulaMemberCount workCount)
          (caseFormulaSizeAt workCount T choiceValue)
          ⟨0, by simp [caseFormulaMemberCount]⟩).symm
    · by_cases hmiddle : index < workCount + 3
      · rw [List.getElem_append_left (by
          simp [length_indexedGateBlocks]
          omega)]
        rw [List.getElem_append_right (by simp; omega)]
        have hrank : index - 1 < workCount + 2 := by omega
        simp only [List.length_singleton]
        rw [getElem_indexedCaseConnectorBlocks (workCount + 2) (fun rank =>
          ({ op := .and
             input₀ := available +
               caseFormulaMembersSize workCount T choiceValue - 1 -
                 caseReadSize T * (rank + 1)
             input₁ := available +
               caseFormulaMembersSize workCount T choiceValue + 2 + rank - 1
             negated₀ := false
             negated₁ := false } : CircuitCode.RawGate)) (index - 1)
          hrank]
        have hindexEq : index - 1 + 1 = index := by omega
        rw [middleCaseConnector_eq workCount T available choiceValue
          (index - 1) hrank, hindexEq]
        exact (getElem_indexedRightFoldConnectors .and available
          (caseFormulaMemberCount workCount)
          (caseFormulaSizeAt workCount T choiceValue)
          ⟨index, by simpa [caseFormulaMemberCount] using hindex⟩).symm
      · have hlast : index = workCount + 3 := by omega
        subst index
        rw [List.getElem_append_right (by
          simp [length_indexedGateBlocks])]
        simpa [length_indexedGateBlocks] using
          (lastCaseConnector_eq workCount T available choiceValue).trans
          (getElem_indexedRightFoldConnectors .and available
            (caseFormulaMemberCount workCount)
            (caseFormulaSizeAt workCount T choiceValue)
            ⟨workCount + 3, by simp [caseFormulaMemberCount]⟩).symm

private theorem encode_cons_append_singleton
    (first last : CircuitCode.RawGate) (middle : CircuitCode.RawCircuit) :
    first.encode ++ (middle.flatMap CircuitCode.RawGate.encode ++
      last.encode) =
      (([first] ++ middle) ++ [last]).flatMap
        CircuitCode.RawGate.encode := by
  simp [List.flatMap_append]

theorem emitCaseFormula_emitted_internal
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitCaseFormula stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).emitted values =
      (caseFormulaSchedule stateCount workCount (values Work.horizon)
        (values Work.configBase) (values Work.reference₀)
        (values Work.available) stateIndex inputSymbolIndex outputSymbolIndex
        choiceValue workSymbolIndexAt).flatMap CircuitCode.RawGate.encode := by
  simp only [emitCaseFormula, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [emitCaseMembers_emitted_internal stateCount workCount stateIndex
    inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt values
    hclean]
  have hreference :
      (emitCaseMembers stateCount workCount stateIndex inputSymbolIndex
        outputSymbolIndex choiceValue workSymbolIndexAt).effect values
          Work.reference₀ = 0 := by
    rw [emitCaseMembers_effect_internal stateCount workCount stateIndex
      inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt values
      hclean]
    simpa [caseReadStartValues, Work.tapeIndex, Work.symbolIndex,
      Work.available, Work.reference₀] using hclean.reference₀
  rw [emitConstantGate_emitted_internal true _ hreference,
    prepareCaseReadSize_emitted_internal, prepareRecentReference_emitted,
    emitCaseConnector_emitted_internal]
  rw [caseFormulaConnectorStart_effect stateCount workCount stateIndex
    inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt values
    hclean]
  let beforeReads := caseFormulaConnectorStartValues values workCount
    outputSymbolIndex choiceValue
  have hloop : beforeReads Work.loop₃ = 0 := by
    simpa [beforeReads, caseFormulaConnectorStartValues,
      caseReadStartValues, Work.loop₃, Work.available, Work.reference₀,
      Work.reference₁, Work.temporary₂, Work.temporary₃,
      Work.tapeIndex, Work.symbolIndex] using hclean.loop₃
  have hreference₁ : beforeReads Work.reference₁ = 0 := by
    simp [beforeReads, caseFormulaConnectorStartValues]
  rw [emitPreviousCaseReadConnectors_emitted (workCount + 2) beforeReads
    hloop hreference₁,
    emitPreviousCaseReadConnectors_effect (workCount + 2) beforeReads hloop
      hreference₁,
    emitPreviousCaseChoiceConnector_emitted_internal]
  simp only [BinaryRoutine.clear, List.append_nil]
  rw [caseFormulaSchedule, List.flatMap_append,
    List.flatMap_append, List.flatMap_singleton]
  simp only [List.nil_append, List.append_assoc]
  apply congrArg₂ List.append rfl
  simp only [directInitConstant]
  apply congrArg₂ List.append rfl
  rw [encode_cons_append_singleton]
  apply congrArg (List.flatMap CircuitCode.RawGate.encode)
  convert caseConnectorGates_eq workCount (values Work.horizon)
    (values Work.available) choiceValue using 1
  all_goals simp [beforeReads, caseFormulaConnectorStartValues, caseReadStartValues,
    caseFormulaMembersSize, caseReadSize, Work.horizon, Work.available,
    Work.reference₀, Work.reference₁, Work.temporary₂,
    Work.temporary₃, Work.tapeIndex, Work.symbolIndex,
    emitCaseMembers_effect_internal stateCount workCount stateIndex
      inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt values
      hclean,
    emitConstantGate_effect_internal, prepareCaseReadSize_effect_internal,
    prepareRecentReference_effect,
    Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  all_goals omega

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
