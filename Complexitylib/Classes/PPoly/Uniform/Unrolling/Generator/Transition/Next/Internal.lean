/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.PolynomialOffset
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Primitive
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Next.Defs
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Effect
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.MovedHead
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.WrittenCell
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Polynomial

/-!
# Direct-unrolling next-atom generator -- proof internals
-/

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

private def advanceAvailableValues (values : BinaryValues WorkCount)
    (amount : ℕ) :
    BinaryValues WorkCount :=
  Function.update values Work.available (values Work.available + amount)

@[simp] private theorem advanceAvailableValues_zero
    (values : BinaryValues WorkCount) :
    advanceAvailableValues values 0 = values := by
  funext i
  simp [advanceAvailableValues]

private theorem seqListEight_requires
    (routine₀ routine₁ routine₂ routine₃ routine₄ routine₅ routine₆
      routine₇ : BinaryRoutine n) (values : BinaryValues n) :
    (BinaryRoutine.seqList
      [routine₀, routine₁, routine₂, routine₃, routine₄, routine₅,
        routine₆, routine₇]).requires values ↔
      routine₀.requires values ∧
      routine₁.requires (routine₀.effect values) ∧
      routine₂.requires (routine₁.effect (routine₀.effect values)) ∧
      routine₃.requires
        (routine₂.effect (routine₁.effect (routine₀.effect values))) ∧
      routine₄.requires
        (routine₃.effect
          (routine₂.effect (routine₁.effect (routine₀.effect values)))) ∧
      routine₅.requires
        (routine₄.effect
          (routine₃.effect
            (routine₂.effect (routine₁.effect (routine₀.effect values))))) ∧
      routine₆.requires
        (routine₅.effect
          (routine₄.effect
            (routine₃.effect
              (routine₂.effect
                (routine₁.effect (routine₀.effect values)))))) ∧
      routine₇.requires
        (routine₆.effect
          (routine₅.effect
            (routine₄.effect
              (routine₃.effect
                (routine₂.effect
                  (routine₁.effect (routine₀.effect values))))))) ∧
      True := Iff.rfl

private theorem HaltedOrFormulaClean.advanceAvailable
    (values : BinaryValues WorkCount) (hclean : HaltedOrFormulaClean values)
    (amount : ℕ) :
    HaltedOrFormulaClean (advanceAvailableValues values amount) := by
  rcases hclean with
    ⟨hreference₀, hreference₁, hemit, hcopy, hmultiply, hadd, hloop,
      htemporary, hpolynomial⟩
  constructor <;>
    simp_all [advanceAvailableValues, Work.available, Work.reference₀,
      Work.reference₁, Work.emitCounter, Work.copyCounter,
      Work.multiplyCounter, Work.addCounter, Work.loop₃, Work.temporary₃,
      Work.polynomialScratch]

private theorem CaseFormulaClean.advanceAvailable
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (amount : ℕ) :
    CaseFormulaClean (advanceAvailableValues values amount) :=
  { position := by simpa [advanceAvailableValues, Work.available,
      Work.position] using hclean.position
    loop₀ := by simpa [advanceAvailableValues, Work.available, Work.loop₀]
      using hclean.loop₀
    limit₀ := by simpa [advanceAvailableValues, Work.available, Work.limit₀]
      using hclean.limit₀
    reference₀ := by simpa [advanceAvailableValues, Work.available,
      Work.reference₀] using hclean.reference₀
    reference₁ := by simpa [advanceAvailableValues, Work.available,
      Work.reference₁] using hclean.reference₁
    emitCounter := by simpa [advanceAvailableValues, Work.available,
      Work.emitCounter] using hclean.emitCounter
    copyCounter := by simpa [advanceAvailableValues, Work.available,
      Work.copyCounter] using hclean.copyCounter
    multiplyCounter := by simpa [advanceAvailableValues, Work.available,
      Work.multiplyCounter] using hclean.multiplyCounter
    addCounter := by simpa [advanceAvailableValues, Work.available,
      Work.addCounter] using hclean.addCounter
    temporary₀ := by simpa [advanceAvailableValues, Work.available,
      Work.temporary₀] using hclean.temporary₀
    temporary₁ := by simpa [advanceAvailableValues, Work.available,
      Work.temporary₁] using hclean.temporary₁
    temporary₂ := by simpa [advanceAvailableValues, Work.available,
      Work.temporary₂] using hclean.temporary₂
    loop₃ := by simpa [advanceAvailableValues, Work.available, Work.loop₃]
      using hclean.loop₃
    temporary₃ := by simpa [advanceAvailableValues, Work.available,
      Work.temporary₃] using hclean.temporary₃
    polynomialScratch := by simpa [advanceAvailableValues, Work.available,
      Work.polynomialScratch] using hclean.polynomialScratch
    tapeIndex := by simpa [advanceAvailableValues, Work.available,
      Work.tapeIndex] using hclean.tapeIndex
    symbolIndex := by simpa [advanceAvailableValues, Work.available,
      Work.symbolIndex] using hclean.symbolIndex }

private theorem MovedHeadFormulaClean.advanceAvailable
    (values : BinaryValues WorkCount) (hclean : MovedHeadFormulaClean values)
    (amount : ℕ) :
    MovedHeadFormulaClean (advanceAvailableValues values amount) := by
  refine
    { caseClean := ?_
      limit₂ := ?_
      loop₁ := ?_
      savedOutput := ?_
      direction := ?_
      atomKind := ?_ }
  · have hcase := CaseFormulaClean.advanceAvailable
      (Function.update values Work.position 0) hclean.caseClean amount
    have hupdate :
        advanceAvailableValues (Function.update values Work.position 0) amount =
          Function.update (advanceAvailableValues values amount)
            Work.position 0 := by
      simpa [advanceAvailableValues, Work.available, Work.position] using
        (Function.update_comm (a := Work.position) (b := Work.available)
          (by decide) 0 (values Work.available + amount) values)
    rwa [hupdate] at hcase
  · simpa [advanceAvailableValues, Work.available, Work.limit₂] using
      hclean.limit₂
  · simpa [advanceAvailableValues, Work.available, Work.loop₁] using
      hclean.loop₁
  · simpa [advanceAvailableValues, Work.available, Work.savedOutput] using
      hclean.savedOutput
  · simpa [advanceAvailableValues, Work.available, Work.direction] using
      hclean.direction
  · simpa [advanceAvailableValues, Work.available, Work.atomKind] using
      hclean.atomKind

private theorem WrittenCellFormulaClean.advanceAvailable
    (values : BinaryValues WorkCount)
    (hclean : WrittenCellFormulaClean values) (amount : ℕ) :
    WrittenCellFormulaClean (advanceAvailableValues values amount) := by
  refine { caseClean := ?_, limit₂ := ?_, savedOutput := ?_ }
  · have hcase := CaseFormulaClean.advanceAvailable
      (Function.update values Work.position 0) hclean.caseClean amount
    have hupdate :
        advanceAvailableValues (Function.update values Work.position 0) amount =
          Function.update (advanceAvailableValues values amount)
            Work.position 0 := by
      simpa [advanceAvailableValues, Work.available, Work.position] using
        (Function.update_comm (a := Work.position) (b := Work.available)
          (by decide) 0 (values Work.available + amount) values)
    rwa [hupdate] at hcase
  · simpa [advanceAvailableValues, Work.available, Work.limit₂] using
      hclean.limit₂
  · simpa [advanceAvailableValues, Work.available, Work.savedOutput] using
      hclean.savedOutput

private theorem CaseFormulaClean.haltedOrClean
    {values : BinaryValues WorkCount} (hclean : CaseFormulaClean values) :
    HaltedOrFormulaClean values :=
  { reference₀ := hclean.reference₀
    reference₁ := hclean.reference₁
    emitCounter := hclean.emitCounter
    copyCounter := hclean.copyCounter
    multiplyCounter := hclean.multiplyCounter
    addCounter := hclean.addCounter
    loop₃ := hclean.loop₃
    temporary₃ := hclean.temporary₃
    polynomialScratch := hclean.polynomialScratch }

private theorem parkedCase_haltedOrClean
    {values : BinaryValues WorkCount}
    (hclean : CaseFormulaClean (Function.update values Work.position 0)) :
    HaltedOrFormulaClean values :=
  { reference₀ := by simpa [Work.position, Work.reference₀] using
      hclean.reference₀
    reference₁ := by simpa [Work.position, Work.reference₁] using
      hclean.reference₁
    emitCounter := by simpa [Work.position, Work.emitCounter] using
      hclean.emitCounter
    copyCounter := by simpa [Work.position, Work.copyCounter] using
      hclean.copyCounter
    multiplyCounter := by simpa [Work.position, Work.multiplyCounter] using
      hclean.multiplyCounter
    addCounter := by simpa [Work.position, Work.addCounter] using
      hclean.addCounter
    loop₃ := by simpa [Work.position, Work.loop₃] using hclean.loop₃
    temporary₃ := by simpa [Work.position, Work.temporary₃] using
      hclean.temporary₃
    polynomialScratch := by simpa [Work.position, Work.polynomialScratch]
      using hclean.polynomialScratch }

private theorem emitStateReference_effect_advanceAvailable
    (stateIndex amount : ℕ) (values : BinaryValues WorkCount)
    (hclean : HaltedOrFormulaClean values) :
    (emitStateReference stateIndex).effect
        (advanceAvailableValues values amount) =
      advanceAvailableValues values (amount + 1) := by
  rw [emitStateReference_effect]
  funext i
  by_cases havailable : i = Work.available
  · subst i
    simp [advanceAvailableValues, Work.available, Work.reference₀,
      Nat.add_assoc]
  by_cases hreference : i = Work.reference₀
  · subst i
    simpa [advanceAvailableValues, Work.available, Work.reference₀] using
      hclean.reference₀.symm
  · simp [advanceAvailableValues, havailable, hreference]

private theorem emitRecentGate_effect_advanceAvailable
    (op : AndOrOp) (negated₀ negated₁ : Bool) (offset₀ offset₁ amount : ℕ)
    (values : BinaryValues WorkCount) (hclean : HaltedOrFormulaClean values) :
    (emitRecentGate op negated₀ negated₁ offset₀ offset₁).effect
        (advanceAvailableValues values amount) =
      advanceAvailableValues values (amount + 1) := by
  rw [emitRecentGate_effect]
  funext i
  by_cases havailable : i = Work.available
  · subst i
    simp [advanceAvailableValues, Work.available, Work.reference₀,
      Work.reference₁, Nat.add_assoc]
  by_cases hreference₀ : i = Work.reference₀
  · subst i
    simpa [advanceAvailableValues, Work.available, Work.reference₀,
      Work.reference₁] using hclean.reference₀.symm
  by_cases hreference₁ : i = Work.reference₁
  · subst i
    simpa [advanceAvailableValues, Work.available, Work.reference₀,
      Work.reference₁] using hclean.reference₁.symm
  · simp [advanceAvailableValues, havailable, hreference₀, hreference₁]

private theorem emitPolynomialRecentGate_effect_advanceAvailable
    (polynomial : Polynomial ℕ) (extra : ℕ) (op : AndOrOp)
    (negated₀ negated₁ : Bool) (fixedOffset₁ amount : ℕ)
    (values : BinaryValues WorkCount) (hclean : HaltedOrFormulaClean values) :
    (emitPolynomialRecentGate polynomial extra op negated₀ negated₁
        fixedOffset₁).effect (advanceAvailableValues values amount) =
      advanceAvailableValues values (amount + 1) := by
  rw [emitPolynomialRecentGate_effect polynomial extra op negated₀ negated₁
    fixedOffset₁ (advanceAvailableValues values amount)]
  · funext i
    by_cases havailable : i = Work.available
    · subst i
      simp [advanceAvailableValues, Work.available, Work.reference₀,
        Work.reference₁, Work.loop₃, Work.temporary₃, Nat.add_assoc]
    by_cases hreference₀ : i = Work.reference₀
    · subst i
      simpa [advanceAvailableValues, Work.available, Work.reference₀,
        Work.reference₁, Work.loop₃, Work.temporary₃] using
        hclean.reference₀.symm
    by_cases hreference₁ : i = Work.reference₁
    · subst i
      simpa [advanceAvailableValues, Work.available, Work.reference₀,
        Work.reference₁, Work.loop₃, Work.temporary₃] using
        hclean.reference₁.symm
    by_cases hloop : i = Work.loop₃
    · subst i
      simpa [advanceAvailableValues, Work.available, Work.reference₀,
        Work.reference₁, Work.loop₃, Work.temporary₃] using
        hclean.loop₃.symm
    by_cases htemporary : i = Work.temporary₃
    · subst i
      simpa [advanceAvailableValues, Work.available, Work.reference₀,
        Work.reference₁, Work.loop₃, Work.temporary₃] using
        hclean.temporary₃.symm
    · simp [advanceAvailableValues, havailable, hreference₀, hreference₁,
        hloop, htemporary]
  · simpa [advanceAvailableValues, Work.available, Work.loop₃] using
      hclean.loop₃

theorem emitOldStateValue_sound_internal (stateIndex : ℕ) :
    (emitOldStateValue stateIndex).Sound :=
  emitStateReference_sound stateIndex false

theorem emitOldHeadValue_sound_internal (stateCount tapeIndex : ℕ) :
    (emitOldHeadValue stateCount tapeIndex).Sound := by
  apply BinaryRoutine.seqList_sound
  intro member hmember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
  rcases hmember with hmember | hmember | hmember
  · subst member
    exact BinaryRoutine.set_sound Work.tapeIndex tapeIndex
  · subst member
    exact emitHeadReference_sound stateCount false
  · subst member
    exact BinaryRoutine.clear_sound Work.tapeIndex

theorem emitOldCellValue_sound_internal
    (stateCount tapeCount tapeIndex symbolIndex : ℕ) :
    (emitOldCellValue stateCount tapeCount tapeIndex symbolIndex).Sound := by
  apply BinaryRoutine.seqList_sound
  intro member hmember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
  rcases hmember with hmember | hmember | hmember | hmember | hmember
  · subst member
    exact BinaryRoutine.set_sound Work.tapeIndex tapeIndex
  · subst member
    exact BinaryRoutine.set_sound Work.symbolIndex symbolIndex
  · subst member
    exact emitCellReference_sound stateCount tapeCount false
  · subst member
    exact BinaryRoutine.clear_sound Work.tapeIndex
  · subst member
    exact BinaryRoutine.clear_sound Work.symbolIndex

theorem emitOldStateValue_requires_internal (stateIndex : ℕ)
    (values : BinaryValues WorkCount)
    (hadd : values Work.addCounter = 0)
    (hemit : values Work.emitCounter = 0) :
    (emitOldStateValue stateIndex).requires values :=
  emitStateReference_requires stateIndex false values hadd hemit

theorem emitOldHeadValue_requires_internal (stateCount tapeIndex : ℕ)
    (values : BinaryValues WorkCount)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0)
    (hemit : values Work.emitCounter = 0) :
    (emitOldHeadValue stateCount tapeIndex).requires values := by
  simp only [emitOldHeadValue, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
    BinaryRoutine.identity, BinaryRoutine.emitBits, true_and]
  constructor
  · apply emitHeadReference_requires stateCount false
    · simpa [Work.tapeIndex, Work.addCounter] using hadd
    · simpa [Work.tapeIndex, Work.multiplyCounter] using hmultiply
    · simpa [Work.tapeIndex, Work.emitCounter] using hemit
  · trivial

theorem emitOldCellValue_requires_internal
    (stateCount tapeCount tapeIndex symbolIndex : ℕ)
    (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0)
    (hemit : values Work.emitCounter = 0) :
    (emitOldCellValue stateCount tapeCount tapeIndex symbolIndex).requires
      values := by
  simp only [emitOldCellValue, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
    BinaryRoutine.identity, BinaryRoutine.emitBits, true_and]
  constructor
  · apply emitCellReference_requires stateCount tapeCount false
    · simpa [Work.tapeIndex, Work.symbolIndex, Work.copyCounter] using hcopy
    · simpa [Work.tapeIndex, Work.symbolIndex, Work.addCounter] using hadd
    · simpa [Work.tapeIndex, Work.symbolIndex, Work.multiplyCounter] using
        hmultiply
    · simpa [Work.tapeIndex, Work.symbolIndex, Work.emitCounter] using hemit
  · trivial

theorem emitOldStateValue_effect_internal (stateIndex : ℕ)
    (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0) :
    (emitOldStateValue stateIndex).effect values =
      Function.update values Work.available (values Work.available + 1) := by
  rw [emitOldStateValue, emitStateReference_effect]
  funext i
  simp only [Function.update_apply]
  split_ifs <;> simp_all [Work.available, Work.reference₀]

theorem emitOldHeadValue_effect_internal (stateCount tapeIndex : ℕ)
    (values : BinaryValues WorkCount)
    (htape : values Work.tapeIndex = 0)
    (htemporary : values Work.temporary₀ = 0)
    (hreference : values Work.reference₀ = 0) :
    (emitOldHeadValue stateCount tapeIndex).effect values =
      Function.update values Work.available (values Work.available + 1) := by
  simp only [emitOldHeadValue, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
    BinaryRoutine.identity, BinaryRoutine.emitBits, emitHeadReference_effect]
  funext i
  by_cases havailable : i = Work.available
  · subst i
    simp [Work.available, Work.tapeIndex, Work.temporary₀, Work.reference₀]
  by_cases htapeIndex : i = Work.tapeIndex
  · subst i
    simpa [Work.available, Work.tapeIndex, Work.temporary₀, Work.reference₀]
      using htape.symm
  by_cases htemporaryIndex : i = Work.temporary₀
  · subst i
    simpa [Work.available, Work.tapeIndex, Work.temporary₀, Work.reference₀]
      using htemporary.symm
  by_cases hreferenceIndex : i = Work.reference₀
  · subst i
    simpa [Work.available, Work.tapeIndex, Work.temporary₀, Work.reference₀]
      using hreference.symm
  · simp [Function.update_apply, havailable, htapeIndex, htemporaryIndex,
      hreferenceIndex]

theorem emitOldCellValue_effect_internal
    (stateCount tapeCount tapeIndex symbolIndex : ℕ)
    (values : BinaryValues WorkCount)
    (htape : values Work.tapeIndex = 0)
    (hsymbol : values Work.symbolIndex = 0)
    (htemporary₀ : values Work.temporary₀ = 0)
    (htemporary₁ : values Work.temporary₁ = 0)
    (htemporary₂ : values Work.temporary₂ = 0)
    (hreference : values Work.reference₀ = 0) :
    (emitOldCellValue stateCount tapeCount tapeIndex symbolIndex).effect values =
      Function.update values Work.available (values Work.available + 1) := by
  simp only [emitOldCellValue, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
    BinaryRoutine.identity, BinaryRoutine.emitBits, emitCellReference_effect]
  funext i
  by_cases havailable : i = Work.available
  · subst i
    simp [Work.available, Work.tapeIndex, Work.symbolIndex, Work.temporary₀,
      Work.temporary₁, Work.temporary₂, Work.reference₀]
  by_cases htapeIndex : i = Work.tapeIndex
  · subst i
    simpa [Work.available, Work.tapeIndex, Work.symbolIndex, Work.temporary₀,
      Work.temporary₁, Work.temporary₂, Work.reference₀] using
      htape.symm
  by_cases hsymbolIndex : i = Work.symbolIndex
  · subst i
    simpa [Work.available, Work.tapeIndex, Work.symbolIndex, Work.temporary₀,
      Work.temporary₁, Work.temporary₂, Work.reference₀] using
      hsymbol.symm
  by_cases htemporary₀Index : i = Work.temporary₀
  · subst i
    simpa [Work.available, Work.tapeIndex, Work.symbolIndex, Work.temporary₀,
      Work.temporary₁, Work.temporary₂, Work.reference₀] using
      htemporary₀.symm
  by_cases htemporary₁Index : i = Work.temporary₁
  · subst i
    simpa [Work.available, Work.tapeIndex, Work.symbolIndex, Work.temporary₀,
      Work.temporary₁, Work.temporary₂, Work.reference₀] using
      htemporary₁.symm
  by_cases htemporary₂Index : i = Work.temporary₂
  · subst i
    simpa [Work.available, Work.tapeIndex, Work.symbolIndex, Work.temporary₀,
      Work.temporary₁, Work.temporary₂, Work.reference₀] using
      htemporary₂.symm
  by_cases hreferenceIndex : i = Work.reference₀
  · subst i
    simpa [Work.available, Work.tapeIndex, Work.symbolIndex, Work.temporary₀,
      Work.temporary₁, Work.temporary₂, Work.reference₀] using
      hreference.symm
  · simp [Function.update_apply, havailable, htapeIndex, hsymbolIndex,
      htemporary₀Index, htemporary₁Index, htemporary₂Index,
      hreferenceIndex]

@[simp] theorem emitOldStateValue_emitted_internal (stateIndex : ℕ)
    (values : BinaryValues WorkCount) :
    (emitOldStateValue stateIndex).emitted values =
      CircuitCode.RawGate.encode
        (CircuitCode.RawGate.copy
          (transitionStateRef (values Work.configBase) stateIndex)) := by
  simp [emitOldStateValue]

@[simp] theorem emitOldHeadValue_emitted_internal
    (stateCount tapeIndex : ℕ) (values : BinaryValues WorkCount) :
    (emitOldHeadValue stateCount tapeIndex).emitted values =
      CircuitCode.RawGate.encode
        (CircuitCode.RawGate.copy
          (transitionHeadRef stateCount (values Work.horizon)
            (values Work.configBase) tapeIndex (values Work.position))) := by
  simp [emitOldHeadValue, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
    BinaryRoutine.identity, BinaryRoutine.emitBits, Work.tapeIndex,
    Work.horizon, Work.configBase, Work.position]

@[simp] theorem emitOldCellValue_emitted_internal
    (stateCount tapeCount tapeIndex symbolIndex : ℕ)
    (values : BinaryValues WorkCount) :
    (emitOldCellValue stateCount tapeCount tapeIndex symbolIndex).emitted values =
      CircuitCode.RawGate.encode
        (CircuitCode.RawGate.copy
          (transitionCellRef stateCount tapeCount (values Work.horizon)
            (values Work.configBase) tapeIndex (values Work.position)
            symbolIndex)) := by
  simp [emitOldCellValue, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
    BinaryRoutine.identity, BinaryRoutine.emitBits, Work.tapeIndex,
    Work.symbolIndex, Work.horizon, Work.configBase, Work.position]

theorem emitNextCellCopy_sound_internal
    (stateCount tapeCount tapeIndex symbolIndex : ℕ) :
    (emitNextCellCopy stateCount tapeCount tapeIndex symbolIndex).Sound :=
  emitOldCellValue_sound_internal stateCount tapeCount tapeIndex symbolIndex

theorem emitNextCellCopy_requires_internal
    (stateCount tapeCount tapeIndex symbolIndex : ℕ)
    (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0)
    (hemit : values Work.emitCounter = 0) :
    (emitNextCellCopy stateCount tapeCount tapeIndex symbolIndex).requires
      values :=
  emitOldCellValue_requires_internal stateCount tapeCount tapeIndex symbolIndex
    values hcopy hadd hmultiply hemit

theorem emitNextCellCopy_effect_internal
    (stateCount tapeCount tapeIndex symbolIndex : ℕ)
    (values : BinaryValues WorkCount)
    (htape : values Work.tapeIndex = 0)
    (hsymbol : values Work.symbolIndex = 0)
    (htemporary₀ : values Work.temporary₀ = 0)
    (htemporary₁ : values Work.temporary₁ = 0)
    (htemporary₂ : values Work.temporary₂ = 0)
    (hreference : values Work.reference₀ = 0) :
    (emitNextCellCopy stateCount tapeCount tapeIndex symbolIndex).effect values =
      Function.update values Work.available (values Work.available + 1) :=
  emitOldCellValue_effect_internal stateCount tapeCount tapeIndex symbolIndex
    values htape hsymbol htemporary₀ htemporary₁ htemporary₂ hreference

theorem emitNextCellCopy_emitted_internal
    (stateCount tapeCount tapeIndex symbolIndex : ℕ)
    (values : BinaryValues WorkCount) :
    (emitNextCellCopy stateCount tapeCount tapeIndex symbolIndex).emitted values =
      (nextCellCopySchedule stateCount tapeCount (values Work.horizon)
        (values Work.configBase) tapeIndex (values Work.position)
        symbolIndex).flatMap CircuitCode.RawGate.encode := by
  simp [emitNextCellCopy, nextCellCopySchedule,
    emitOldCellValue_emitted_internal]

theorem emitHaltedOrFormula_sound_internal (haltStateIndex : ℕ)
    (childSize : Polynomial ℕ) (oldValue nextValue : BinaryRoutine WorkCount)
    (hold : oldValue.Sound) (hnext : nextValue.Sound) :
    (emitHaltedOrFormula haltStateIndex childSize oldValue nextValue).Sound := by
  apply BinaryRoutine.seqList_sound
  intro member hmember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
  rcases hmember with hmember | hmember | hmember | hmember | hmember |
    hmember | hmember | hmember
  · subst member
    exact emitStateReference_sound haltStateIndex false
  · subst member
    exact hold
  · subst member
    exact emitRecentGate_sound .and false false 2 1
  · subst member
    exact emitStateReference_sound haltStateIndex false
  · subst member
    exact emitRecentGate_sound .and true true 1 1
  · subst member
    exact hnext
  · subst member
    exact emitPolynomialRecentGate_sound childSize 1 .and false false 1
  · subst member
    exact emitPolynomialRecentGate_sound childSize 4 .or false false 1

theorem emitHaltedOrFormula_requires_internal (haltStateIndex : ℕ)
    (childSize : Polynomial ℕ) (oldValue nextValue : BinaryRoutine WorkCount)
    (values : BinaryValues WorkCount) (hclean : HaltedOrFormulaClean values)
    (holdRequires : oldValue.requires (advanceAvailableValues values 1))
    (holdEffect : oldValue.effect (advanceAvailableValues values 1) =
      advanceAvailableValues values 2)
    (hnextRequires : nextValue.requires (advanceAvailableValues values 5))
    (hnextEffect : nextValue.effect (advanceAvailableValues values 5) =
      advanceAvailableValues values
        (5 + childSize.eval (values Work.horizon))) :
    (emitHaltedOrFormula haltStateIndex childSize oldValue nextValue).requires
      values := by
  have hhalt₀ : (emitStateReference haltStateIndex).requires values :=
    emitStateReference_requires haltStateIndex false values hclean.addCounter
      hclean.emitCounter
  have hhalt₀Effect : (emitStateReference haltStateIndex).effect values =
      advanceAvailableValues values 1 := by
    simpa using emitStateReference_effect_advanceAvailable haltStateIndex 0
      values hclean
  have hleft :
      (emitRecentGate .and false false 2 1).requires
        (advanceAvailableValues values 2) := by
    apply (emitRecentGate_requires .and false false 2 1 _).2
    refine ⟨?_, by simp [advanceAvailableValues, Work.available],
      by simp [advanceAvailableValues, Work.available], ?_⟩
    · simpa [advanceAvailableValues, Work.available, Work.copyCounter] using
        hclean.copyCounter
    · simpa [advanceAvailableValues, Work.available, Work.emitCounter] using
        hclean.emitCounter
  have hleftEffect :
      (emitRecentGate .and false false 2 1).effect
          (advanceAvailableValues values 2) =
        advanceAvailableValues values 3 := by
    simpa using emitRecentGate_effect_advanceAvailable .and false false 2 1 2
      values hclean
  have hhalt₁ :
      (emitStateReference haltStateIndex).requires
        (advanceAvailableValues values 3) := by
    apply emitStateReference_requires haltStateIndex false
    · simpa [advanceAvailableValues, Work.available, Work.addCounter] using
        hclean.addCounter
    · simpa [advanceAvailableValues, Work.available, Work.emitCounter] using
        hclean.emitCounter
  have hhalt₁Effect :
      (emitStateReference haltStateIndex).effect
          (advanceAvailableValues values 3) =
        advanceAvailableValues values 4 := by
    simpa using emitStateReference_effect_advanceAvailable haltStateIndex 3
      values hclean
  have hnegated :
      (emitRecentGate .and true true 1 1).requires
        (advanceAvailableValues values 4) := by
    apply (emitRecentGate_requires .and true true 1 1 _).2
    refine ⟨?_, by simp [advanceAvailableValues, Work.available],
      by simp [advanceAvailableValues, Work.available], ?_⟩
    · simpa [advanceAvailableValues, Work.available, Work.copyCounter] using
        hclean.copyCounter
    · simpa [advanceAvailableValues, Work.available, Work.emitCounter] using
        hclean.emitCounter
  have hnegatedEffect :
      (emitRecentGate .and true true 1 1).effect
          (advanceAvailableValues values 4) =
        advanceAvailableValues values 5 := by
    simpa using emitRecentGate_effect_advanceAvailable .and true true 1 1 4
      values hclean
  let childGateCount := childSize.eval (values Work.horizon)
  have hright :
      (emitPolynomialRecentGate childSize 1 .and false false 1).requires
        (advanceAvailableValues values (5 + childGateCount)) := by
    apply (emitPolynomialRecentGate_requires childSize 1 .and false false 1
      _).2
    have hrightClean := HaltedOrFormulaClean.advanceAvailable values hclean
      (5 + childGateCount)
    refine ⟨hrightClean.temporary₃, hrightClean.polynomialScratch,
      hrightClean.multiplyCounter, hrightClean.addCounter,
      hrightClean.copyCounter, hrightClean.loop₃, ?_, ?_,
      hrightClean.emitCounter⟩
    · simp [advanceAvailableValues, childGateCount, Work.available,
        Work.horizon]
      omega
    · simp [advanceAvailableValues, Work.available]
      omega
  have hrightEffect :
      (emitPolynomialRecentGate childSize 1 .and false false 1).effect
          (advanceAvailableValues values (5 + childGateCount)) =
        advanceAvailableValues values (6 + childGateCount) := by
    rw [show 6 + childGateCount = (5 + childGateCount) + 1 by omega]
    exact emitPolynomialRecentGate_effect_advanceAvailable childSize 1 .and
      false false 1 (5 + childGateCount) values hclean
  have hfinal :
      (emitPolynomialRecentGate childSize 4 .or false false 1).requires
        (advanceAvailableValues values (6 + childGateCount)) := by
    apply (emitPolynomialRecentGate_requires childSize 4 .or false false 1
      _).2
    have hfinalClean := HaltedOrFormulaClean.advanceAvailable values hclean
      (6 + childGateCount)
    refine ⟨hfinalClean.temporary₃, hfinalClean.polynomialScratch,
      hfinalClean.multiplyCounter, hfinalClean.addCounter,
      hfinalClean.copyCounter, hfinalClean.loop₃, ?_, ?_,
      hfinalClean.emitCounter⟩
    · simp [advanceAvailableValues, childGateCount, Work.available,
        Work.horizon]
      omega
    · simp [advanceAvailableValues, Work.available]
      omega
  rw [emitHaltedOrFormula, seqListEight_requires]
  rw [hhalt₀Effect, holdEffect, hleftEffect, hhalt₁Effect,
    hnegatedEffect, hnextEffect, hrightEffect]
  refine ⟨hhalt₀, holdRequires, hleft, hhalt₁, hnegated, hnextRequires,
    hright, ?_⟩
  simpa [childGateCount] using hfinal

theorem emitHaltedOrFormula_effect_internal (haltStateIndex : ℕ)
    (childSize : Polynomial ℕ) (oldValue nextValue : BinaryRoutine WorkCount)
    (values : BinaryValues WorkCount) (hclean : HaltedOrFormulaClean values)
    (holdEffect : oldValue.effect (advanceAvailableValues values 1) =
      advanceAvailableValues values 2)
    (hnextEffect : nextValue.effect (advanceAvailableValues values 5) =
      advanceAvailableValues values
        (5 + childSize.eval (values Work.horizon))) :
    (emitHaltedOrFormula haltStateIndex childSize oldValue nextValue).effect
        values =
      advanceAvailableValues values
        (childSize.eval (values Work.horizon) + 7) := by
  have hhalt₀Effect : (emitStateReference haltStateIndex).effect values =
      advanceAvailableValues values 1 := by
    simpa using emitStateReference_effect_advanceAvailable haltStateIndex 0
      values hclean
  have hleftEffect :
      (emitRecentGate .and false false 2 1).effect
          (advanceAvailableValues values 2) =
        advanceAvailableValues values 3 := by
    simpa using emitRecentGate_effect_advanceAvailable .and false false 2 1 2
      values hclean
  have hhalt₁Effect :
      (emitStateReference haltStateIndex).effect
          (advanceAvailableValues values 3) =
        advanceAvailableValues values 4 := by
    simpa using emitStateReference_effect_advanceAvailable haltStateIndex 3
      values hclean
  have hnegatedEffect :
      (emitRecentGate .and true true 1 1).effect
          (advanceAvailableValues values 4) =
        advanceAvailableValues values 5 := by
    simpa using emitRecentGate_effect_advanceAvailable .and true true 1 1 4
      values hclean
  let childGateCount := childSize.eval (values Work.horizon)
  have hrightEffect :
      (emitPolynomialRecentGate childSize 1 .and false false 1).effect
          (advanceAvailableValues values (5 + childGateCount)) =
        advanceAvailableValues values (6 + childGateCount) := by
    rw [show 6 + childGateCount = (5 + childGateCount) + 1 by omega]
    exact emitPolynomialRecentGate_effect_advanceAvailable childSize 1 .and
      false false 1 (5 + childGateCount) values hclean
  have hfinalEffect :
      (emitPolynomialRecentGate childSize 4 .or false false 1).effect
          (advanceAvailableValues values (6 + childGateCount)) =
        advanceAvailableValues values (7 + childGateCount) := by
    rw [show 7 + childGateCount = (6 + childGateCount) + 1 by omega]
    exact emitPolynomialRecentGate_effect_advanceAvailable childSize 4 .or
      false false 1 (6 + childGateCount) values hclean
  simp only [emitHaltedOrFormula, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [hhalt₀Effect, holdEffect, hleftEffect, hhalt₁Effect,
    hnegatedEffect, hnextEffect, hrightEffect, hfinalEffect]
  simp [advanceAvailableValues, childGateCount, Nat.add_comm]

theorem emitHaltedOrFormula_emitted_internal (haltStateIndex : ℕ)
    (childSize : Polynomial ℕ) (oldValue nextValue : BinaryRoutine WorkCount)
    (oldWire : ℕ) (nextSchedule : CircuitCode.RawCircuit)
    (values : BinaryValues WorkCount) (hclean : HaltedOrFormulaClean values)
    (holdEffect : oldValue.effect (advanceAvailableValues values 1) =
      advanceAvailableValues values 2)
    (hnextEffect : nextValue.effect (advanceAvailableValues values 5) =
      advanceAvailableValues values
        (5 + childSize.eval (values Work.horizon)))
    (holdEmitted : oldValue.emitted (advanceAvailableValues values 1) =
      CircuitCode.RawGate.encode (CircuitCode.RawGate.copy oldWire))
    (hnextEmitted : nextValue.emitted (advanceAvailableValues values 5) =
      nextSchedule.flatMap CircuitCode.RawGate.encode)
    (hsize : nextSchedule.length = childSize.eval (values Work.horizon)) :
    (emitHaltedOrFormula haltStateIndex childSize oldValue nextValue).emitted
        values =
      (nextHaltedOrSchedule
        (transitionStateRef (values Work.configBase) haltStateIndex)
        (values Work.available) oldWire nextSchedule).flatMap
          CircuitCode.RawGate.encode := by
  have hhalt₀Effect : (emitStateReference haltStateIndex).effect values =
      advanceAvailableValues values 1 := by
    simpa using emitStateReference_effect_advanceAvailable haltStateIndex 0
      values hclean
  have hleftEffect :
      (emitRecentGate .and false false 2 1).effect
          (advanceAvailableValues values 2) =
        advanceAvailableValues values 3 := by
    simpa using emitRecentGate_effect_advanceAvailable .and false false 2 1 2
      values hclean
  have hhalt₁Effect :
      (emitStateReference haltStateIndex).effect
          (advanceAvailableValues values 3) =
        advanceAvailableValues values 4 := by
    simpa using emitStateReference_effect_advanceAvailable haltStateIndex 3
      values hclean
  have hnegatedEffect :
      (emitRecentGate .and true true 1 1).effect
          (advanceAvailableValues values 4) =
        advanceAvailableValues values 5 := by
    simpa using emitRecentGate_effect_advanceAvailable .and true true 1 1 4
      values hclean
  let childGateCount := childSize.eval (values Work.horizon)
  have hrightEffect :
      (emitPolynomialRecentGate childSize 1 .and false false 1).effect
          (advanceAvailableValues values (5 + childGateCount)) =
        advanceAvailableValues values (6 + childGateCount) := by
    rw [show 6 + childGateCount = (5 + childGateCount) + 1 by omega]
    exact emitPolynomialRecentGate_effect_advanceAvailable childSize 1 .and
      false false 1 (5 + childGateCount) values hclean
  have hrightReference :
      5 + (values Work.available +
          childSize.eval (values Work.horizon)) -
          (1 + childSize.eval (values Work.horizon)) =
        values Work.available + 4 := by
    omega
  have hfinalReference :
      6 + (values Work.available +
          childSize.eval (values Work.horizon)) -
          (4 + childSize.eval (values Work.horizon)) =
        values Work.available + 2 := by
    omega
  simp only [emitHaltedOrFormula, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits, List.append_nil]
  rw [hhalt₀Effect, holdEffect, hleftEffect, hhalt₁Effect,
    hnegatedEffect, hnextEffect, hrightEffect]
  rw [emitStateReference_emitted, holdEmitted, emitRecentGate_emitted,
    emitStateReference_emitted, emitRecentGate_emitted, hnextEmitted,
    emitPolynomialRecentGate_emitted, emitPolynomialRecentGate_emitted]
  · simp [nextHaltedOrSchedule, haltedOrSchedule, advanceAvailableValues,
      childGateCount, hsize, Work.available, Work.horizon, Work.configBase,
      CircuitCode.RawGate.copy, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
    congr 1
    · apply congrArg CircuitCode.RawGate.encode
      congr 1 <;> omega
    · apply congrArg (fun suffix : List Bool =>
        nextSchedule.flatMap CircuitCode.RawGate.encode ++ suffix)
      congr 1
      · apply congrArg CircuitCode.RawGate.encode
        congr 1 <;> omega
      · apply congrArg CircuitCode.RawGate.encode
        congr 1 <;> omega
  · simpa [advanceAvailableValues, childGateCount, Work.available,
      Work.loop₃] using hclean.loop₃
  · simpa [advanceAvailableValues, childGateCount, Work.available,
      Work.loop₃] using hclean.loop₃

theorem emitNextStateFormula_sound_internal (tm : NTM k)
    (state : tm.Q) :
    (emitNextStateFormula tm state).Sound :=
  emitHaltedOrFormula_sound_internal (stateIndex tm tm.qhalt)
    (stateNextChildPolynomial tm state)
    (emitOldStateValue (stateIndex tm state)) (emitStateNextChild tm state)
    (emitOldStateValue_sound_internal (stateIndex tm state))
    (emitEffectFormula_sound tm fun effect =>
      decide (effect.nextState = state))

theorem emitNextStateFormula_requires_internal (tm : NTM k)
    (state : tm.Q) (values : BinaryValues WorkCount)
    (hclean : CaseFormulaClean values) :
    (emitNextStateFormula tm state).requires values := by
  apply emitHaltedOrFormula_requires_internal _ _ _ _ values
    hclean.haltedOrClean
  · apply emitOldStateValue_requires_internal
    · simpa [advanceAvailableValues, Work.available, Work.addCounter] using
        hclean.addCounter
    · simpa [advanceAvailableValues, Work.available, Work.emitCounter] using
        hclean.emitCounter
  · have hreference :
        advanceAvailableValues values 1 Work.reference₀ = 0 := by
      simpa [advanceAvailableValues, Work.available, Work.reference₀] using
        hclean.reference₀
    simpa [advanceAvailableValues, Nat.add_assoc] using
      emitOldStateValue_effect_internal (stateIndex tm state)
        (advanceAvailableValues values 1) hreference
  · apply emitEffectFormula_requires
    · exact hclean.advanceAvailable values 5
    · simp [advanceAvailableValues, Work.available]
  · simp only [emitStateNextChild]
    rw [emitEffectFormula_effect]
    · simp [advanceAvailableValues, stateNextChildPolynomial, Nat.add_assoc,
        Work.available, Work.horizon]
    · exact hclean.advanceAvailable values 5
    · simp [advanceAvailableValues, Work.available]

theorem emitNextStateFormula_effect_internal (tm : NTM k)
    (state : tm.Q) (values : BinaryValues WorkCount)
    (hclean : CaseFormulaClean values) :
    (emitNextStateFormula tm state).effect values =
      Function.update values Work.available
        (values Work.available +
          nextStateFormulaScheduleSize (transitionCases tm).length k
            (values Work.horizon)
            (effectCaseSelectedAt tm fun effect =>
              decide (effect.nextState = state))
            (effectCaseChoiceAt tm)) := by
  have holdEffect :
      (emitOldStateValue (stateIndex tm state)).effect
          (advanceAvailableValues values 1) =
        advanceAvailableValues values 2 := by
    rw [emitOldStateValue_effect_internal]
    · simp [advanceAvailableValues, Nat.add_assoc]
    · simpa [advanceAvailableValues, Work.available, Work.reference₀] using
        hclean.reference₀
  have hnextEffect :
      (emitStateNextChild tm state).effect
          (advanceAvailableValues values 5) =
        advanceAvailableValues values
          (5 + (stateNextChildPolynomial tm state).eval
            (values Work.horizon)) := by
    simp only [emitStateNextChild]
    rw [emitEffectFormula_effect]
    · simp [advanceAvailableValues, stateNextChildPolynomial, Nat.add_assoc,
        Work.available, Work.horizon]
    · exact hclean.advanceAvailable values 5
    · simp [advanceAvailableValues, Work.available]
  have hresult := emitHaltedOrFormula_effect_internal
    (stateIndex tm tm.qhalt) (stateNextChildPolynomial tm state)
    (emitOldStateValue (stateIndex tm state)) (emitStateNextChild tm state)
    values hclean.haltedOrClean holdEffect hnextEffect
  simpa [emitNextStateFormula, advanceAvailableValues,
    stateNextChildPolynomial, nextStateFormulaScheduleSize,
    nextHaltedOrScheduleSize, Nat.add_assoc] using hresult

theorem emitNextStateFormula_emitted_internal (tm : NTM k)
    (state : tm.Q) (values : BinaryValues WorkCount)
    (hclean : CaseFormulaClean values) :
    (emitNextStateFormula tm state).emitted values =
      (nextStateFormulaSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k (values Work.horizon)
        (values Work.configBase) (values Work.reference₀)
        (values Work.available) (stateIndex tm state)
        (stateIndex tm tm.qhalt)
        (effectCaseSelectedAt tm fun effect =>
          decide (effect.nextState = state))
        (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
        (effectCaseInputSymbolIndexAt tm) (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm)).flatMap
          CircuitCode.RawGate.encode := by
  let nextSchedule := effectFormulaSchedule (transitionCases tm).length
    (Fintype.card tm.Q) k (values Work.horizon)
    (values Work.configBase) (values Work.reference₀)
    (values Work.available + 5)
    (effectCaseSelectedAt tm fun effect => decide (effect.nextState = state))
    (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
    (effectCaseInputSymbolIndexAt tm) (effectCaseOutputSymbolIndexAt tm)
    (effectCaseWorkSymbolIndexAt tm)
  have holdEffect :
      (emitOldStateValue (stateIndex tm state)).effect
          (advanceAvailableValues values 1) =
        advanceAvailableValues values 2 := by
    rw [emitOldStateValue_effect_internal]
    · simp [advanceAvailableValues, Nat.add_assoc]
    · simpa [advanceAvailableValues, Work.available, Work.reference₀] using
        hclean.reference₀
  have hnextEffect :
      (emitStateNextChild tm state).effect
          (advanceAvailableValues values 5) =
        advanceAvailableValues values
          (5 + (stateNextChildPolynomial tm state).eval
            (values Work.horizon)) := by
    simp only [emitStateNextChild]
    rw [emitEffectFormula_effect]
    · simp [advanceAvailableValues, stateNextChildPolynomial, Nat.add_assoc,
        Work.available, Work.horizon]
    · exact hclean.advanceAvailable values 5
    · simp [advanceAvailableValues, Work.available]
  have holdEmitted :
      (emitOldStateValue (stateIndex tm state)).emitted
          (advanceAvailableValues values 1) =
        CircuitCode.RawGate.encode (CircuitCode.RawGate.copy
          (transitionStateRef (values Work.configBase)
            (stateIndex tm state))) := by
    simp [advanceAvailableValues, Work.available, Work.configBase]
  have hnextEmitted :
      (emitStateNextChild tm state).emitted
          (advanceAvailableValues values 5) =
        nextSchedule.flatMap CircuitCode.RawGate.encode := by
    simp only [emitStateNextChild]
    rw [emitEffectFormula_emitted]
    · simp [nextSchedule, advanceAvailableValues, Work.available,
        Work.horizon, Work.configBase, Work.reference₀]
    · exact hclean.advanceAvailable values 5
    · simp [advanceAvailableValues, Work.available]
  have hsize : nextSchedule.length =
      (stateNextChildPolynomial tm state).eval (values Work.horizon) := by
    simp [nextSchedule, stateNextChildPolynomial]
  have hresult := emitHaltedOrFormula_emitted_internal
    (stateIndex tm tm.qhalt) (stateNextChildPolynomial tm state)
    (emitOldStateValue (stateIndex tm state)) (emitStateNextChild tm state)
    (transitionStateRef (values Work.configBase) (stateIndex tm state))
    nextSchedule values hclean.haltedOrClean holdEffect hnextEffect
    holdEmitted hnextEmitted hsize
  simpa [emitNextStateFormula, nextStateFormulaSchedule,
    nextSchedule, nextFormulaChildAvailable] using hresult

theorem emitNextHeadFormula_sound_internal (tm : NTM k)
    (tape : TapeSlot k) :
    (emitNextHeadFormula tm tape).Sound :=
  emitHaltedOrFormula_sound_internal (stateIndex tm tm.qhalt)
    (headNextChildPolynomial tm tape)
    (emitOldHeadValue (Fintype.card tm.Q) tape.index)
    (emitMovedHeadFormula tm tape)
    (emitOldHeadValue_sound_internal (Fintype.card tm.Q) tape.index)
    (emitMovedHeadFormula_sound tm tape)

theorem emitNextHeadFormula_requires_internal (tm : NTM k)
    (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitNextHeadFormula tm tape).requires values := by
  let hcase := hclean.caseClean
  apply emitHaltedOrFormula_requires_internal _ _ _ _ values
    (parkedCase_haltedOrClean hcase)
  · apply emitOldHeadValue_requires_internal
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.addCounter] using hcase.addCounter
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.multiplyCounter] using hcase.multiplyCounter
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.emitCounter] using hcase.emitCounter
  · have htape : advanceAvailableValues values 1 Work.tapeIndex = 0 := by
      simpa [advanceAvailableValues, Work.available, Work.position,
        Work.tapeIndex] using hcase.tapeIndex
    have htemporary :
        advanceAvailableValues values 1 Work.temporary₀ = 0 := by
      simpa [advanceAvailableValues, Work.available, Work.position,
        Work.temporary₀] using hcase.temporary₀
    have hreference :
        advanceAvailableValues values 1 Work.reference₀ = 0 := by
      simpa [advanceAvailableValues, Work.available, Work.position,
        Work.reference₀] using hcase.reference₀
    simpa [advanceAvailableValues, Nat.add_assoc] using
      emitOldHeadValue_effect_internal (Fintype.card tm.Q) tape.index
        (advanceAvailableValues values 1) htape htemporary hreference
  · apply emitMovedHeadFormula_requires
    · exact hclean.advanceAvailable values 5
    · simpa [advanceAvailableValues, Work.available, Work.horizon]
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.horizon]
    · simp [advanceAvailableValues, Work.available]
  · rw [emitMovedHeadFormula_effect]
    · simp [advanceAvailableValues, headNextChildPolynomial, Nat.add_assoc,
        Work.available, Work.horizon]
    · exact hclean.advanceAvailable values 5
    · simpa [advanceAvailableValues, Work.available, Work.horizon]
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.horizon]
    · simp [advanceAvailableValues, Work.available]

theorem emitNextHeadFormula_effect_internal (tm : NTM k)
    (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitNextHeadFormula tm tape).effect values =
      Function.update values Work.available
        (values Work.available +
          nextHeadFormulaScheduleSize (transitionCases tm).length k
            (values Work.horizon) (movedHeadCaseSelectedAt tm tape)
            (effectCaseChoiceAt tm)) := by
  let hcase := hclean.caseClean
  have holdEffect :
      (emitOldHeadValue (Fintype.card tm.Q) tape.index).effect
          (advanceAvailableValues values 1) =
        advanceAvailableValues values 2 := by
    rw [emitOldHeadValue_effect_internal]
    · simp [advanceAvailableValues, Nat.add_assoc]
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.tapeIndex] using hcase.tapeIndex
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.temporary₀] using hcase.temporary₀
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.reference₀] using hcase.reference₀
  have hnextEffect :
      (emitMovedHeadFormula tm tape).effect
          (advanceAvailableValues values 5) =
        advanceAvailableValues values
          (5 + (headNextChildPolynomial tm tape).eval
            (values Work.horizon)) := by
    rw [emitMovedHeadFormula_effect]
    · simp [advanceAvailableValues, headNextChildPolynomial, Nat.add_assoc,
        Work.available, Work.horizon]
    · exact hclean.advanceAvailable values 5
    · simpa [advanceAvailableValues, Work.available, Work.horizon]
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.horizon]
    · simp [advanceAvailableValues, Work.available]
  have hresult := emitHaltedOrFormula_effect_internal
    (stateIndex tm tm.qhalt) (headNextChildPolynomial tm tape)
    (emitOldHeadValue (Fintype.card tm.Q) tape.index)
    (emitMovedHeadFormula tm tape) values (parkedCase_haltedOrClean hcase)
    holdEffect hnextEffect
  simpa [emitNextHeadFormula, advanceAvailableValues,
    headNextChildPolynomial, nextHeadFormulaScheduleSize,
    nextHaltedOrScheduleSize, Nat.add_assoc] using hresult

theorem emitNextHeadFormula_emitted_internal (tm : NTM k)
    (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitNextHeadFormula tm tape).emitted values =
      (nextHeadFormulaSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k (values Work.horizon)
        (values Work.configBase) (values Work.reference₀)
        (values Work.available) tape.index (values Work.position)
        (stateIndex tm tm.qhalt) (movedHeadCaseSelectedAt tm tape)
        (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
        (effectCaseInputSymbolIndexAt tm) (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm)).flatMap
          CircuitCode.RawGate.encode := by
  let hcase := hclean.caseClean
  let nextSchedule := movedHeadFormulaSchedule (transitionCases tm).length
    (Fintype.card tm.Q) k (values Work.horizon)
    (values Work.configBase) (values Work.reference₀)
    (values Work.available + 5) tape.index (values Work.position)
    (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm)
    (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
    (effectCaseOutputSymbolIndexAt tm) (effectCaseWorkSymbolIndexAt tm)
  have holdEffect :
      (emitOldHeadValue (Fintype.card tm.Q) tape.index).effect
          (advanceAvailableValues values 1) =
        advanceAvailableValues values 2 := by
    rw [emitOldHeadValue_effect_internal]
    · simp [advanceAvailableValues, Nat.add_assoc]
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.tapeIndex] using hcase.tapeIndex
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.temporary₀] using hcase.temporary₀
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.reference₀] using hcase.reference₀
  have hnextEffect :
      (emitMovedHeadFormula tm tape).effect
          (advanceAvailableValues values 5) =
        advanceAvailableValues values
          (5 + (headNextChildPolynomial tm tape).eval
            (values Work.horizon)) := by
    rw [emitMovedHeadFormula_effect]
    · simp [advanceAvailableValues, headNextChildPolynomial, Nat.add_assoc,
        Work.available, Work.horizon]
    · exact hclean.advanceAvailable values 5
    · simpa [advanceAvailableValues, Work.available, Work.horizon]
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.horizon]
    · simp [advanceAvailableValues, Work.available]
  have holdEmitted :
      (emitOldHeadValue (Fintype.card tm.Q) tape.index).emitted
          (advanceAvailableValues values 1) =
        CircuitCode.RawGate.encode (CircuitCode.RawGate.copy
          (transitionHeadRef (Fintype.card tm.Q) (values Work.horizon)
            (values Work.configBase) tape.index (values Work.position))) := by
    simp [advanceAvailableValues, Work.available, Work.horizon,
      Work.configBase, Work.position]
  have hnextEmitted :
      (emitMovedHeadFormula tm tape).emitted
          (advanceAvailableValues values 5) =
        nextSchedule.flatMap CircuitCode.RawGate.encode := by
    rw [emitMovedHeadFormula_emitted]
    · simp [nextSchedule, advanceAvailableValues, Work.available,
        Work.horizon, Work.configBase, Work.reference₀, Work.position]
    · exact hclean.advanceAvailable values 5
    · simpa [advanceAvailableValues, Work.available, Work.horizon]
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.horizon]
    · simp [advanceAvailableValues, Work.available]
  have hsize : nextSchedule.length =
      (headNextChildPolynomial tm tape).eval (values Work.horizon) := by
    simp [nextSchedule, headNextChildPolynomial]
  have hresult := emitHaltedOrFormula_emitted_internal
    (stateIndex tm tm.qhalt) (headNextChildPolynomial tm tape)
    (emitOldHeadValue (Fintype.card tm.Q) tape.index)
    (emitMovedHeadFormula tm tape)
    (transitionHeadRef (Fintype.card tm.Q) (values Work.horizon)
      (values Work.configBase) tape.index (values Work.position))
    nextSchedule values (parkedCase_haltedOrClean hcase) holdEffect
    hnextEffect holdEmitted hnextEmitted hsize
  simpa [emitNextHeadFormula, nextHeadFormulaSchedule, nextSchedule,
    nextFormulaChildAvailable] using hresult

theorem emitNextWrittenCellFormula_sound_internal (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ) :
    (emitNextWrittenCellFormula tm tape symbol).Sound :=
  emitHaltedOrFormula_sound_internal (stateIndex tm tm.qhalt)
    (writtenNextChildPolynomial tm tape symbol)
    (emitOldCellValue (Fintype.card tm.Q) (k + 2)
      tape.toTapeSlot.index (CircuitUnrolling.symbolIndex symbol))
    (emitWrittenCellFormula tm tape symbol)
    (emitOldCellValue_sound_internal (Fintype.card tm.Q) (k + 2)
      tape.toTapeSlot.index (CircuitUnrolling.symbolIndex symbol))
    (emitWrittenCellFormula_sound tm tape symbol)

theorem emitNextWrittenCellFormula_requires_internal (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount)
    (hclean : WrittenCellFormulaClean values)
    (hposition : values Work.position ≤ values Work.horizon + 1) :
    (emitNextWrittenCellFormula tm tape symbol).requires values := by
  let hcase := hclean.caseClean
  apply emitHaltedOrFormula_requires_internal _ _ _ _ values
    (parkedCase_haltedOrClean hcase)
  · apply emitOldCellValue_requires_internal
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.copyCounter] using hcase.copyCounter
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.addCounter] using hcase.addCounter
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.multiplyCounter] using hcase.multiplyCounter
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.emitCounter] using hcase.emitCounter
  · have htape : advanceAvailableValues values 1 Work.tapeIndex = 0 := by
      simpa [advanceAvailableValues, Work.available, Work.position,
        Work.tapeIndex] using hcase.tapeIndex
    have hsymbol : advanceAvailableValues values 1 Work.symbolIndex = 0 := by
      simpa [advanceAvailableValues, Work.available, Work.position,
        Work.symbolIndex] using hcase.symbolIndex
    have htemporary₀ :
        advanceAvailableValues values 1 Work.temporary₀ = 0 := by
      simpa [advanceAvailableValues, Work.available, Work.position,
        Work.temporary₀] using hcase.temporary₀
    have htemporary₁ :
        advanceAvailableValues values 1 Work.temporary₁ = 0 := by
      simpa [advanceAvailableValues, Work.available, Work.position,
        Work.temporary₁] using hcase.temporary₁
    have htemporary₂ :
        advanceAvailableValues values 1 Work.temporary₂ = 0 := by
      simpa [advanceAvailableValues, Work.available, Work.position,
        Work.temporary₂] using hcase.temporary₂
    have hreference :
        advanceAvailableValues values 1 Work.reference₀ = 0 := by
      simpa [advanceAvailableValues, Work.available, Work.position,
        Work.reference₀] using hcase.reference₀
    simpa [advanceAvailableValues, Nat.add_assoc] using
      emitOldCellValue_effect_internal (Fintype.card tm.Q) (k + 2)
        tape.toTapeSlot.index (CircuitUnrolling.symbolIndex symbol)
        (advanceAvailableValues values 1) htape hsymbol htemporary₀
        htemporary₁ htemporary₂ hreference
  · apply emitWrittenCellFormula_requires
    · exact hclean.advanceAvailable values 5
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.horizon]
  · rw [emitWrittenCellFormula_effect]
    · simp [advanceAvailableValues, writtenNextChildPolynomial,
        Nat.add_assoc, Work.available, Work.horizon]
    · exact hclean.advanceAvailable values 5

theorem emitNextWrittenCellFormula_effect_internal (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount)
    (hclean : WrittenCellFormulaClean values) :
    (emitNextWrittenCellFormula tm tape symbol).effect values =
      Function.update values Work.available
        (values Work.available +
          nextWrittenCellFormulaScheduleSize (transitionCases tm).length k
            (values Work.horizon)
            (writtenCellEffectSelectedAt tm tape symbol)
            (effectCaseChoiceAt tm)) := by
  let hcase := hclean.caseClean
  have holdEffect :
      (emitOldCellValue (Fintype.card tm.Q) (k + 2)
          tape.toTapeSlot.index (CircuitUnrolling.symbolIndex symbol)).effect
          (advanceAvailableValues values 1) =
        advanceAvailableValues values 2 := by
    rw [emitOldCellValue_effect_internal]
    · simp [advanceAvailableValues, Nat.add_assoc]
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.tapeIndex] using hcase.tapeIndex
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.symbolIndex] using hcase.symbolIndex
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.temporary₀] using hcase.temporary₀
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.temporary₁] using hcase.temporary₁
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.temporary₂] using hcase.temporary₂
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.reference₀] using hcase.reference₀
  have hnextEffect :
      (emitWrittenCellFormula tm tape symbol).effect
          (advanceAvailableValues values 5) =
        advanceAvailableValues values
          (5 + (writtenNextChildPolynomial tm tape symbol).eval
            (values Work.horizon)) := by
    rw [emitWrittenCellFormula_effect]
    · simp [advanceAvailableValues, writtenNextChildPolynomial,
        Nat.add_assoc, Work.available, Work.horizon]
    · exact hclean.advanceAvailable values 5
  have hresult := emitHaltedOrFormula_effect_internal
    (stateIndex tm tm.qhalt) (writtenNextChildPolynomial tm tape symbol)
    (emitOldCellValue (Fintype.card tm.Q) (k + 2)
      tape.toTapeSlot.index (CircuitUnrolling.symbolIndex symbol))
    (emitWrittenCellFormula tm tape symbol) values
    (parkedCase_haltedOrClean hcase) holdEffect hnextEffect
  simpa [emitNextWrittenCellFormula, advanceAvailableValues,
    writtenNextChildPolynomial, nextWrittenCellFormulaScheduleSize,
    nextHaltedOrScheduleSize, Nat.add_assoc] using hresult

theorem emitNextWrittenCellFormula_emitted_internal (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount)
    (hclean : WrittenCellFormulaClean values)
    (hposition : values Work.position ≤ values Work.horizon + 1) :
    (emitNextWrittenCellFormula tm tape symbol).emitted values =
      (nextWrittenCellFormulaSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k (values Work.horizon)
        (values Work.configBase) (values Work.reference₀)
        (values Work.available) tape.toTapeSlot.index (values Work.position)
        (CircuitUnrolling.symbolIndex symbol) (stateIndex tm tm.qhalt)
        (writtenCellEffectSelectedAt tm tape symbol) (effectCaseChoiceAt tm)
        (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
        (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm)).flatMap
          CircuitCode.RawGate.encode := by
  let hcase := hclean.caseClean
  let nextSchedule := writtenCellSchedule (transitionCases tm).length
    (Fintype.card tm.Q) k (values Work.horizon)
    (values Work.configBase) (values Work.reference₀)
    (values Work.available + 5) tape.toTapeSlot.index
    (values Work.position) (CircuitUnrolling.symbolIndex symbol)
    (writtenCellEffectSelectedAt tm tape symbol) (effectCaseChoiceAt tm)
    (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
    (effectCaseOutputSymbolIndexAt tm) (effectCaseWorkSymbolIndexAt tm)
  have holdEffect :
      (emitOldCellValue (Fintype.card tm.Q) (k + 2)
          tape.toTapeSlot.index (CircuitUnrolling.symbolIndex symbol)).effect
          (advanceAvailableValues values 1) =
        advanceAvailableValues values 2 := by
    rw [emitOldCellValue_effect_internal]
    · simp [advanceAvailableValues, Nat.add_assoc]
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.tapeIndex] using hcase.tapeIndex
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.symbolIndex] using hcase.symbolIndex
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.temporary₀] using hcase.temporary₀
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.temporary₁] using hcase.temporary₁
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.temporary₂] using hcase.temporary₂
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.reference₀] using hcase.reference₀
  have hnextEffect :
      (emitWrittenCellFormula tm tape symbol).effect
          (advanceAvailableValues values 5) =
        advanceAvailableValues values
          (5 + (writtenNextChildPolynomial tm tape symbol).eval
            (values Work.horizon)) := by
    rw [emitWrittenCellFormula_effect]
    · simp [advanceAvailableValues, writtenNextChildPolynomial,
        Nat.add_assoc, Work.available, Work.horizon]
    · exact hclean.advanceAvailable values 5
  have holdEmitted :
      (emitOldCellValue (Fintype.card tm.Q) (k + 2)
          tape.toTapeSlot.index
          (CircuitUnrolling.symbolIndex symbol)).emitted
          (advanceAvailableValues values 1) =
        CircuitCode.RawGate.encode (CircuitCode.RawGate.copy
          (transitionCellRef (Fintype.card tm.Q) (k + 2)
            (values Work.horizon) (values Work.configBase)
            tape.toTapeSlot.index (values Work.position)
            (CircuitUnrolling.symbolIndex symbol))) := by
    simp [advanceAvailableValues, Work.available, Work.horizon,
      Work.configBase, Work.position]
  have hnextEmitted :
      (emitWrittenCellFormula tm tape symbol).emitted
          (advanceAvailableValues values 5) =
        nextSchedule.flatMap CircuitCode.RawGate.encode := by
    rw [emitWrittenCellFormula_emitted]
    · simp [nextSchedule, advanceAvailableValues, Work.available,
        Work.horizon, Work.configBase, Work.reference₀, Work.position]
    · exact hclean.advanceAvailable values 5
    · simpa [advanceAvailableValues, Work.available, Work.position,
        Work.horizon]
  have hsize : nextSchedule.length =
      (writtenNextChildPolynomial tm tape symbol).eval
        (values Work.horizon) := by
    simp [nextSchedule, writtenNextChildPolynomial]
  have hresult := emitHaltedOrFormula_emitted_internal
    (stateIndex tm tm.qhalt) (writtenNextChildPolynomial tm tape symbol)
    (emitOldCellValue (Fintype.card tm.Q) (k + 2)
      tape.toTapeSlot.index (CircuitUnrolling.symbolIndex symbol))
    (emitWrittenCellFormula tm tape symbol)
    (transitionCellRef (Fintype.card tm.Q) (k + 2)
      (values Work.horizon) (values Work.configBase) tape.toTapeSlot.index
      (values Work.position) (CircuitUnrolling.symbolIndex symbol))
    nextSchedule values (parkedCase_haltedOrClean hcase) holdEffect
    hnextEffect holdEmitted hnextEmitted hsize
  simpa [emitNextWrittenCellFormula, nextWrittenCellFormulaSchedule,
    nextSchedule, nextFormulaChildAvailable] using hresult

theorem stateNextChildPolynomial_eval_internal (tm : NTM k)
    (state : tm.Q) (T : ℕ) :
    (stateNextChildPolynomial tm state).eval T =
      effectFormulaScheduleSize (transitionCases tm).length k T
        (effectCaseSelectedAt tm fun effect =>
          decide (effect.nextState = state))
        (effectCaseChoiceAt tm) := by
  simp [stateNextChildPolynomial]

theorem stateNextFormulaPolynomial_eval_internal (tm : NTM k)
    (state : tm.Q) (T : ℕ) :
    (stateNextFormulaPolynomial tm state).eval T =
      nextStateFormulaScheduleSize (transitionCases tm).length k T
        (effectCaseSelectedAt tm fun effect =>
          decide (effect.nextState = state))
        (effectCaseChoiceAt tm) := by
  simp [stateNextFormulaPolynomial, stateNextChildPolynomial_eval_internal,
    nextStateFormulaScheduleSize, nextHaltedOrScheduleSize]

theorem headNextChildPolynomial_eval_internal (tm : NTM k)
    (tape : TapeSlot k) (T : ℕ) :
    (headNextChildPolynomial tm tape).eval T =
      movedHeadFormulaScheduleSize (transitionCases tm).length k T
        (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm) := by
  simp [headNextChildPolynomial]

theorem headNextFormulaPolynomial_eval_internal (tm : NTM k)
    (tape : TapeSlot k) (T : ℕ) :
    (headNextFormulaPolynomial tm tape).eval T =
      nextHeadFormulaScheduleSize (transitionCases tm).length k T
        (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm) := by
  simp [headNextFormulaPolynomial, headNextChildPolynomial_eval_internal,
    nextHeadFormulaScheduleSize, nextHaltedOrScheduleSize]

theorem writtenNextChildPolynomial_eval_internal (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ) (T : ℕ) :
    (writtenNextChildPolynomial tm tape symbol).eval T =
      writtenCellScheduleSize (transitionCases tm).length k T
        (writtenCellEffectSelectedAt tm tape symbol)
        (effectCaseChoiceAt tm) := by
  simp [writtenNextChildPolynomial]

theorem writtenNextFormulaPolynomial_eval_internal (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ) (T : ℕ) :
    (writtenNextFormulaPolynomial tm tape symbol).eval T =
      nextWrittenCellFormulaScheduleSize (transitionCases tm).length k T
        (writtenCellEffectSelectedAt tm tape symbol)
        (effectCaseChoiceAt tm) := by
  simp [writtenNextFormulaPolynomial,
    writtenNextChildPolynomial_eval_internal,
    nextWrittenCellFormulaScheduleSize, nextHaltedOrScheduleSize]

theorem stateNextFormulaPolynomial_eval_pos_internal (tm : NTM k)
    (state : tm.Q) (T : ℕ) :
    0 < (stateNextFormulaPolynomial tm state).eval T := by
  rw [stateNextFormulaPolynomial_eval_internal]
  simp [nextStateFormulaScheduleSize, nextHaltedOrScheduleSize]

theorem headNextFormulaPolynomial_eval_pos_internal (tm : NTM k)
    (tape : TapeSlot k) (T : ℕ) :
    0 < (headNextFormulaPolynomial tm tape).eval T := by
  rw [headNextFormulaPolynomial_eval_internal]
  simp [nextHeadFormulaScheduleSize, nextHaltedOrScheduleSize]

theorem writtenNextFormulaPolynomial_eval_pos_internal (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ) (T : ℕ) :
    0 < (writtenNextFormulaPolynomial tm tape symbol).eval T := by
  rw [writtenNextFormulaPolynomial_eval_internal]
  simp [nextWrittenCellFormulaScheduleSize, nextHaltedOrScheduleSize]

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
