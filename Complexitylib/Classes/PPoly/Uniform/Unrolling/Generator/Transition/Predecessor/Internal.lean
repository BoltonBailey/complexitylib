/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Initialization
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Offset
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Primitive
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Predecessor.Defs
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Arithmetic
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Control
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.List

/-!
# Direct predecessor-head formula generation -- proof internals
-/

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

private theorem binaryForValues_addsAvailable
    (body : BinaryRoutine n) (counterIdx availableIdx : Fin n)
    (step : ℕ)
    (heffect : ∀ values, body.effect values =
      Function.update values availableIdx (values availableIdx + step))
    (initial : BinaryValues n) : ∀ count,
    BinaryRoutine.binaryForValues body counterIdx initial count =
      Function.update
        (Function.update initial availableIdx
          (initial availableIdx + step * count))
        counterIdx (initial counterIdx + count) := by
  intro count
  induction count with
  | zero =>
      rw [BinaryRoutine.binaryForValues]
      funext i
      by_cases hic : i = counterIdx
      · subst i
        simp
      · by_cases hia : i = availableIdx
        · subst i
          simp [hic]
        · simp [hic]
  | succ count ih =>
      rw [BinaryRoutine.binaryForValues, BinaryRoutine.binaryForStep,
        heffect, ih]
      funext i
      by_cases hic : i = counterIdx
      · subst i
        simp
        omega
      · by_cases hia : i = availableIdx
        · subst i
          simp [hic, Nat.mul_succ]
          omega
        · simp [hic, hia]

private theorem indexedGateBlocks_succ_last
    (count : ℕ) (blockAt : ℕ → CircuitCode.RawCircuit) :
    indexedGateBlocks (count + 1) blockAt =
      indexedGateBlocks count blockAt ++ blockAt count := by
  induction count generalizing blockAt with
  | zero => simp [indexedGateBlocks]
  | succ count ih =>
      change blockAt 0 ++
          indexedGateBlocks (count + 1) (fun index => blockAt (index + 1)) =
        (blockAt 0 ++ indexedGateBlocks count
          (fun index => blockAt (index + 1))) ++ blockAt (count + 1)
      rw [ih (fun index => blockAt (index + 1))]
      simp [List.append_assoc]

private theorem emitConstantFalse_effect (values : BinaryValues WorkCount) :
    (emitConstantGate false).effect values =
      Function.update values Work.available (values Work.available + 1) :=
  rfl

private theorem emitConstantFalse_emitted
    (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0) :
    (emitConstantGate false).emitted values =
      CircuitCode.RawGate.encode (directInitConstant false) := by
  have href : values 7 = 0 := by
    simpa [Work.reference₀] using hreference
  simp [emitConstantGate, BinaryRoutine.emitRawGateStep,
    directInitConstant, CircuitCode.RawGate.constant, href, Work.reference₀]

private theorem emitConstantFalse_binaryForValues
    (values : BinaryValues WorkCount) (count : ℕ) :
    BinaryRoutine.binaryForValues (emitConstantGate false) Work.loop₀
        values count =
      Function.update
        (Function.update values Work.available
          (values Work.available + count))
        Work.loop₀ (values Work.loop₀ + count) := by
  simpa using binaryForValues_addsAvailable (emitConstantGate false)
    Work.loop₀ Work.available 1 emitConstantFalse_effect values count

private theorem emitConstantFalse_binaryForEmitted
    (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0) : ∀ count,
    BinaryRoutine.binaryForEmitted (emitConstantGate false) Work.loop₀
        values count =
      (indexedGateBlocks count fun _ => [directInitConstant false]).flatMap
        CircuitCode.RawGate.encode := by
  intro count
  induction count with
  | zero =>
      simp [BinaryRoutine.binaryForEmitted, indexedGateBlocks]
  | succ count ih =>
      rw [BinaryRoutine.binaryForEmitted, ih,
        indexedGateBlocks_succ_last]
      have hcurrent :
          (BinaryRoutine.binaryForValues (emitConstantGate false) Work.loop₀
            values count) Work.reference₀ = 0 := by
        rw [emitConstantFalse_binaryForValues]
        have href : values 7 = 0 := by
          simpa [Work.reference₀] using hreference
        simp [href, Work.available, Work.loop₀, Work.reference₀]
      rw [emitConstantFalse_emitted _ hcurrent]
      simp only [List.flatMap_append]
      rfl

theorem setPredecessorHorizonLimit_sound_internal :
    setPredecessorHorizonLimit.Sound :=
  (BinaryRoutine.binaryCopy_sound Work.horizon Work.limit₀
    Work.copyCounter).seq (BinaryRoutine.addConst_sound Work.limit₀ 1)

theorem emitPredecessorFalseRange_sound_internal :
    emitPredecessorFalseRange.Sound :=
  (emitConstantGate_sound false).binaryFor Work.loop₀ Work.limit₀ |>.seq
    (BinaryRoutine.clear_sound Work.loop₀)

theorem emitStayPredecessorMembers_sound_internal (stateCount : ℕ) :
    (emitStayPredecessorMembers stateCount).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h | h | h
  · subst routine
    exact BinaryRoutine.binaryCopy_sound Work.position Work.limit₀
      Work.copyCounter
  · subst routine
    exact emitPredecessorFalseRange_sound_internal
  · subst routine
    exact emitHeadReference_sound stateCount false
  · subst routine
    exact BinaryRoutine.binaryCopy_sound Work.position Work.loop₀
      Work.copyCounter
  · subst routine
    exact BinaryRoutine.addConst_sound Work.loop₀ 1
  · subst routine
    exact setPredecessorHorizonLimit_sound_internal
  · subst routine
    exact emitPredecessorFalseRange_sound_internal

theorem emitRightZeroPredecessorMembers_sound_internal :
    emitRightZeroPredecessorMembers.Sound :=
  setPredecessorHorizonLimit_sound_internal.seq
    emitPredecessorFalseRange_sound_internal

theorem emitRightPositivePredecessorMembers_sound_internal
    (stateCount : ℕ) :
    (emitRightPositivePredecessorMembers stateCount).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h | h | h | h | h
  · subst routine
    exact BinaryRoutine.binaryCopy_sound Work.position Work.limit₀
      Work.copyCounter
  · subst routine
    exact BinaryRoutine.binaryPred_sound Work.limit₀
  · subst routine
    exact emitPredecessorFalseRange_sound_internal
  · subst routine
    exact BinaryRoutine.binaryPred_sound Work.position
  · subst routine
    exact emitHeadReference_sound stateCount false
  · subst routine
    exact BinaryRoutine.addConst_sound Work.position 1
  · subst routine
    exact BinaryRoutine.binaryCopy_sound Work.position Work.loop₀
      Work.copyCounter
  · subst routine
    exact setPredecessorHorizonLimit_sound_internal
  · subst routine
    exact emitPredecessorFalseRange_sound_internal

theorem emitRightPredecessorMembers_sound_internal (stateCount : ℕ) :
    (emitRightPredecessorMembers stateCount).Sound :=
  emitRightZeroPredecessorMembers_sound_internal.branchZero
    (emitRightPositivePredecessorMembers_sound_internal stateCount)
    Work.position

theorem emitLeftZeroPredecessorMembers_sound_internal (stateCount : ℕ) :
    (emitLeftZeroPredecessorMembers stateCount).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h | h | h
  · subst routine
    exact emitHeadReference_sound stateCount false
  · subst routine
    exact BinaryRoutine.addConst_sound Work.position 1
  · subst routine
    exact emitHeadReference_sound stateCount false
  · subst routine
    exact BinaryRoutine.binaryPred_sound Work.position
  · subst routine
    exact BinaryRoutine.set_sound Work.loop₀ 2
  · subst routine
    exact setPredecessorHorizonLimit_sound_internal
  · subst routine
    exact emitPredecessorFalseRange_sound_internal

theorem preparePredecessorHorizonGap_sound_internal :
    preparePredecessorHorizonGap.Sound :=
  (BinaryRoutine.binaryCopy_sound Work.horizon Work.temporary₃
    Work.copyCounter).seq
      (decrementReferenceBy_sound Work.temporary₃ Work.position Work.loop₀)

theorem emitLeftPositivePredecessorTail_sound_internal
    (stateCount : ℕ) :
    (emitLeftPositivePredecessorTail stateCount).Sound := by
  apply (BinaryRoutine.clear_sound Work.temporary₃).branchZero
  · apply BinaryRoutine.seqList_sound
    intro routine hroutine
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
    rcases hroutine with h | h | h | h | h | h | h
    · subst routine
      exact BinaryRoutine.addConst_sound Work.position 1
    · subst routine
      exact emitHeadReference_sound stateCount false
    · subst routine
      exact BinaryRoutine.binaryPred_sound Work.position
    · subst routine
      exact BinaryRoutine.binaryPred_sound Work.temporary₃
    · subst routine
      exact (emitConstantGate_sound false).binaryFor Work.loop₀
        Work.temporary₃
    · subst routine
      exact BinaryRoutine.clear_sound Work.loop₀
    · subst routine
      exact BinaryRoutine.clear_sound Work.temporary₃

theorem emitLeftPositivePredecessorMembers_sound_internal
    (stateCount : ℕ) :
    (emitLeftPositivePredecessorMembers stateCount).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h | h
  · subst routine
    exact BinaryRoutine.binaryCopy_sound Work.position Work.limit₀
      Work.copyCounter
  · subst routine
    exact BinaryRoutine.addConst_sound Work.limit₀ 1
  · subst routine
    exact emitPredecessorFalseRange_sound_internal
  · subst routine
    exact preparePredecessorHorizonGap_sound_internal
  · subst routine
    exact emitLeftPositivePredecessorTail_sound_internal stateCount
  · subst routine
    exact setPredecessorHorizonLimit_sound_internal

theorem emitLeftPredecessorMembers_sound_internal (stateCount : ℕ) :
    (emitLeftPredecessorMembers stateCount).Sound :=
  (emitLeftZeroPredecessorMembers_sound_internal stateCount).branchZero
    (emitLeftPositivePredecessorMembers_sound_internal stateCount)
    Work.position

theorem emitPredecessorHeadMembers_sound_internal
    (stateCount directionCode : ℕ) :
    (emitPredecessorHeadMembers stateCount directionCode).Sound := by
  by_cases hleft : directionCode = 0
  · simp [emitPredecessorHeadMembers, hleft,
      emitLeftPredecessorMembers_sound_internal]
  · by_cases hright : directionCode = 1
    · simp [emitPredecessorHeadMembers, hright,
        emitRightPredecessorMembers_sound_internal]
    · simp [emitPredecessorHeadMembers, hleft, hright,
        emitStayPredecessorMembers_sound_internal]

theorem emitPredecessorHeadConnector_sound_internal :
    emitPredecessorHeadConnector.Sound :=
  (emitDynamicRecentGate_sound .or false false Work.temporary₃ Work.loop₁
    1).seq (BinaryRoutine.addConst_sound Work.temporary₃ 2)

theorem setPredecessorHorizonLimit_effect_internal
    (values : BinaryValues WorkCount) :
    setPredecessorHorizonLimit.effect values =
      Function.update values Work.limit₀ (values Work.horizon + 1) := by
  simp [setPredecessorHorizonLimit, BinaryRoutine.seq,
    BinaryRoutine.binaryCopy, BinaryRoutine.addConst, Work.horizon,
    Work.limit₀]

theorem setPredecessorHorizonLimit_emitted_internal
    (values : BinaryValues WorkCount) :
    setPredecessorHorizonLimit.emitted values = [] := by
  rfl

theorem emitPredecessorFalseRange_effect_internal
    (values : BinaryValues WorkCount) :
    emitPredecessorFalseRange.effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available +
            (values Work.limit₀ - values Work.loop₀)))
        Work.loop₀ 0 := by
  rw [emitPredecessorFalseRange, BinaryRoutine.seq]
  change (BinaryRoutine.clear Work.loop₀).effect
      ((BinaryRoutine.binaryFor (emitConstantGate false) Work.loop₀
        Work.limit₀).effect values) = _
  rw [show (BinaryRoutine.binaryFor (emitConstantGate false) Work.loop₀
      Work.limit₀).effect values =
      BinaryRoutine.binaryForValues (emitConstantGate false) Work.loop₀
        values (values Work.limit₀ - values Work.loop₀) by rfl,
    emitConstantFalse_binaryForValues]
  simp [BinaryRoutine.clear]

theorem emitPredecessorFalseRange_emitted_internal
    (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0) :
    emitPredecessorFalseRange.emitted values =
      (indexedGateBlocks (values Work.limit₀ - values Work.loop₀) fun _ =>
        [directInitConstant false]).flatMap CircuitCode.RawGate.encode := by
  rw [emitPredecessorFalseRange, BinaryRoutine.seq]
  change BinaryRoutine.binaryForEmitted (emitConstantGate false) Work.loop₀
      values (values Work.limit₀ - values Work.loop₀) ++
      (BinaryRoutine.clear Work.loop₀).emitted
        ((BinaryRoutine.binaryFor (emitConstantGate false) Work.loop₀
          Work.limit₀).effect values) = _
  rw [emitConstantFalse_binaryForEmitted values hreference]
  simp [BinaryRoutine.clear]

private theorem emitHeadReference_effect_of_clean
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (htemporary : values Work.temporary₀ = 0)
    (hreference : values Work.reference₀ = 0) :
    (emitHeadReference stateCount).effect values =
      Function.update values Work.available (values Work.available + 1) := by
  rw [emitHeadReference_effect]
  simp only [Work.temporary₀, Work.available, Work.reference₀] at htemporary hreference ⊢
  funext i
  simp only [Function.update_apply]
  split_ifs
  all_goals simp_all

set_option maxHeartbeats 800000 in
theorem emitStayPredecessorMembers_effect_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitStayPredecessorMembers stateCount).effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available + (values Work.horizon + 1)))
        Work.limit₀ (values Work.horizon + 1) := by
  let afterLimit :=
    (BinaryRoutine.binaryCopy Work.position Work.limit₀
      Work.copyCounter).effect values
  let afterPrefix := emitPredecessorFalseRange.effect afterLimit
  let afterHead := (emitHeadReference stateCount).effect afterPrefix
  let afterLoopCopy :=
    (BinaryRoutine.binaryCopy Work.position Work.loop₀
      Work.copyCounter).effect afterHead
  let afterLoopSucc :=
    (BinaryRoutine.addConst Work.loop₀ 1).effect afterLoopCopy
  let afterHorizon := setPredecessorHorizonLimit.effect afterLoopSucc
  have hafterLimit : afterLimit =
      Function.update values Work.limit₀ (values Work.position) := rfl
  have hafterPrefix : afterPrefix =
      Function.update
        (Function.update afterLimit Work.available
          (afterLimit Work.available +
            (afterLimit Work.limit₀ - afterLimit Work.loop₀)))
        Work.loop₀ 0 :=
    emitPredecessorFalseRange_effect_internal afterLimit
  have htemporaryPrefix : afterPrefix Work.temporary₀ = 0 := by
    rw [hafterPrefix, hafterLimit]
    have htemporary : values 22 = 0 := by
      simpa [Work.temporary₀] using hclean.temporary₀
    simp [htemporary, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₀]
  have hreferencePrefix : afterPrefix Work.reference₀ = 0 := by
    rw [hafterPrefix, hafterLimit]
    have hreference : values 7 = 0 := by
      simpa [Work.reference₀] using hclean.reference₀
    simp [hreference, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.reference₀]
  have hafterHead : afterHead =
      Function.update afterPrefix Work.available
        (afterPrefix Work.available + 1) :=
    emitHeadReference_effect_of_clean stateCount afterPrefix
      htemporaryPrefix hreferencePrefix
  have hafterLoopCopy : afterLoopCopy =
      Function.update afterHead Work.loop₀ (afterHead Work.position) := rfl
  have hafterLoopSucc : afterLoopSucc =
      Function.update afterLoopCopy Work.loop₀
        (afterLoopCopy Work.loop₀ + 1) := rfl
  have hafterHorizon : afterHorizon =
      Function.update afterLoopSucc Work.limit₀
        (afterLoopSucc Work.horizon + 1) :=
    setPredecessorHorizonLimit_effect_internal afterLoopSucc
  have hloop' : values 14 = 0 := by
    simpa [Work.loop₀] using hclean.loop₀
  have htarget' : values 30 ≤ values 1 := by
    simpa [Work.position, Work.horizon] using htarget
  have htemporary₃' : values 25 = 0 := by
    simpa [Work.temporary₃] using hclean.temporary₃
  rw [emitStayPredecessorMembers]
  change emitPredecessorFalseRange.effect afterHorizon = _
  rw [emitPredecessorFalseRange_effect_internal, hafterHorizon,
    hafterLoopSucc, hafterLoopCopy, hafterHead, hafterPrefix, hafterLimit]
  simp only [Work.horizon, Work.available, Work.position, Work.loop₀,
    Work.limit₀] at ⊢
  funext i
  simp only [Function.update_apply]
  split_ifs
  all_goals (try simp_all)
  all_goals omega

theorem emitRightZeroPredecessorMembers_effect_internal
    (values : BinaryValues WorkCount)
    (hloop : values Work.loop₀ = 0) :
    emitRightZeroPredecessorMembers.effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available + (values Work.horizon + 1)))
        Work.limit₀ (values Work.horizon + 1) := by
  rw [emitRightZeroPredecessorMembers, BinaryRoutine.seq]
  change emitPredecessorFalseRange.effect
      (setPredecessorHorizonLimit.effect values) = _
  rw [setPredecessorHorizonLimit_effect_internal,
    emitPredecessorFalseRange_effect_internal]
  have hloop' : values 14 = 0 := by
    simpa [Work.loop₀] using hloop
  funext i
  simp only [Work.horizon, Work.available, Work.loop₀, Work.limit₀,
    Function.update_apply]
  split_ifs <;> simp_all

private theorem predecessorGapDistinct :
    DecrementReferenceDistinct Work.temporary₃ Work.position Work.loop₀ :=
  ⟨by decide, by decide, by decide⟩

theorem preparePredecessorHorizonGap_effect_internal
    (values : BinaryValues WorkCount)
    (hloop : values Work.loop₀ = 0) :
    preparePredecessorHorizonGap.effect values =
      Function.update
        (Function.update values Work.temporary₃
          (values Work.horizon - values Work.position))
        Work.loop₀ 0 := by
  rw [preparePredecessorHorizonGap, BinaryRoutine.seq]
  change (decrementReferenceBy Work.temporary₃ Work.position
      Work.loop₀).effect
      ((BinaryRoutine.binaryCopy Work.horizon Work.temporary₃
        Work.copyCounter).effect values) = _
  rw [show (BinaryRoutine.binaryCopy Work.horizon Work.temporary₃
      Work.copyCounter).effect values =
      Function.update values Work.temporary₃ (values Work.horizon) by rfl]
  have hcounter :
      Function.update values Work.temporary₃
          (values Work.horizon) Work.loop₀ = 0 := by
    have hloop' : values 14 = 0 := by
      simpa [Work.loop₀] using hloop
    simp [hloop', Work.horizon, Work.loop₀, Work.temporary₃]
  rw [decrementReferenceBy_effect Work.temporary₃ Work.position Work.loop₀
    _ predecessorGapDistinct hcounter]
  funext i
  simp only [Work.horizon, Work.position, Work.loop₀, Work.temporary₃,
    Function.update_apply]
  split_ifs <;> simp_all

theorem preparePredecessorHorizonGap_emitted_internal
    (values : BinaryValues WorkCount) :
    preparePredecessorHorizonGap.emitted values = [] := by
  simp [preparePredecessorHorizonGap, BinaryRoutine.seq,
    BinaryRoutine.binaryCopy, decrementReferenceBy_emitted]

private theorem emitConstantFalse_binaryForTemporaryEffect
    (values : BinaryValues WorkCount) :
    (BinaryRoutine.binaryFor (emitConstantGate false) Work.loop₀
      Work.temporary₃).effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available +
            (values Work.temporary₃ - values Work.loop₀)))
        Work.loop₀
          (values Work.loop₀ +
            (values Work.temporary₃ - values Work.loop₀)) := by
  exact emitConstantFalse_binaryForValues values
    (values Work.temporary₃ - values Work.loop₀)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem emitLeftPositivePredecessorTail_effect_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hloop : values Work.loop₀ = 0)
    (htemporary : values Work.temporary₀ = 0)
    (hreference : values Work.reference₀ = 0) :
    (emitLeftPositivePredecessorTail stateCount).effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available + values Work.temporary₃))
        Work.temporary₃ 0 := by
  by_cases hgap : values Work.temporary₃ = 0
  · rw [emitLeftPositivePredecessorTail]
    simp [BinaryRoutine.branchZero, hgap, BinaryRoutine.clear]
  · let afterPositionSucc :=
      (BinaryRoutine.addConst Work.position 1).effect values
    let afterHead :=
      (emitHeadReference stateCount).effect afterPositionSucc
    let afterPositionPred :=
      (BinaryRoutine.binaryPred Work.position).effect afterHead
    let afterGapPred :=
      (BinaryRoutine.binaryPred Work.temporary₃).effect afterPositionPred
    let afterFalse :=
      (BinaryRoutine.binaryFor (emitConstantGate false) Work.loop₀
        Work.temporary₃).effect afterGapPred
    let afterLoopClear :=
      (BinaryRoutine.clear Work.loop₀).effect afterFalse
    have hafterPositionSucc : afterPositionSucc =
        Function.update values Work.position (values Work.position + 1) := rfl
    have htemporarySucc : afterPositionSucc Work.temporary₀ = 0 := by
      rw [hafterPositionSucc]
      have htemporary' : values 22 = 0 := by
        simpa [Work.temporary₀] using htemporary
      simp [htemporary', Work.position, Work.temporary₀]
    have hreferenceSucc : afterPositionSucc Work.reference₀ = 0 := by
      rw [hafterPositionSucc]
      have hreference' : values 7 = 0 := by
        simpa [Work.reference₀] using hreference
      simp [hreference', Work.position, Work.reference₀]
    have hafterHead : afterHead =
        Function.update afterPositionSucc Work.available
          (afterPositionSucc Work.available + 1) :=
      emitHeadReference_effect_of_clean stateCount afterPositionSucc
        htemporarySucc hreferenceSucc
    have hafterPositionPred : afterPositionPred =
        Function.update afterHead Work.position
          (afterHead Work.position - 1) := rfl
    have hafterGapPred : afterGapPred =
        Function.update afterPositionPred Work.temporary₃
          (afterPositionPred Work.temporary₃ - 1) := rfl
    have hafterFalse : afterFalse =
        Function.update
          (Function.update afterGapPred Work.available
            (afterGapPred Work.available +
              (afterGapPred Work.temporary₃ - afterGapPred Work.loop₀)))
          Work.loop₀
            (afterGapPred Work.loop₀ +
              (afterGapPred Work.temporary₃ - afterGapPred Work.loop₀)) :=
      emitConstantFalse_binaryForTemporaryEffect afterGapPred
    have hafterLoopClear : afterLoopClear =
        Function.update afterFalse Work.loop₀ 0 := rfl
    rw [emitLeftPositivePredecessorTail]
    simp only [BinaryRoutine.branchZero, hgap, ↓reduceIte]
    change (BinaryRoutine.clear Work.temporary₃).effect afterLoopClear = _
    rw [show (BinaryRoutine.clear Work.temporary₃).effect afterLoopClear =
      Function.update afterLoopClear Work.temporary₃ 0 by rfl,
      hafterLoopClear, hafterFalse, hafterGapPred, hafterPositionPred,
      hafterHead, hafterPositionSucc]
    have hloop' : values 14 = 0 := by
      simpa [Work.loop₀] using hloop
    have hgap' : values 25 ≠ 0 := by
      simpa [Work.temporary₃] using hgap
    funext i
    simp only [Work.available, Work.position, Work.loop₀, Work.temporary₃,
      Function.update_apply] at hloop' hgap' ⊢
    by_cases htemp : i = (25 : Fin WorkCount)
    · subst i
      simp
    · by_cases hloopIdx : i = (14 : Fin WorkCount)
      · subst i
        simp [hloop', htemp]
      · by_cases havailable : i = (5 : Fin WorkCount)
        · subst i
          simp [htemp, hloopIdx, hloop']
          omega
        · by_cases hposition : i = (30 : Fin WorkCount)
          · subst i
            simp [htemp, hloopIdx, havailable]
          · simp [htemp, hloopIdx, havailable, hposition]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem emitRightPositivePredecessorMembers_effect_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hpositive : 0 < values Work.position)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitRightPositivePredecessorMembers stateCount).effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available + (values Work.horizon + 1)))
        Work.limit₀ (values Work.horizon + 1) := by
  rw [emitRightPositivePredecessorMembers]
  funext i
  have hloop' : values 14 = 0 := by
    simpa [Work.loop₀] using hclean.loop₀
  have htemporary' : values 22 = 0 := by
    simpa [Work.temporary₀] using hclean.temporary₀
  have hreference' : values 7 = 0 := by
    simpa [Work.reference₀] using hclean.reference₀
  have hpositive' : 0 < values 30 := by
    simpa [Work.position] using hpositive
  have htarget' : values 30 ≤ values 1 := by
    simpa [Work.position, Work.horizon] using htarget
  simp [BinaryRoutine.seqList, BinaryRoutine.seq,
    emitPredecessorFalseRange_effect_internal,
    setPredecessorHorizonLimit_effect_internal, emitHeadReference_effect,
    BinaryRoutine.binaryCopy, BinaryRoutine.binaryPred,
    BinaryRoutine.addConst, BinaryRoutine.identity, BinaryRoutine.emitBits,
    Work.horizon, Work.available, Work.position, Work.loop₀, Work.limit₀,
    Work.temporary₀, Work.reference₀]
  simp only [Function.update_apply]
  split_ifs
  all_goals simp_all
  all_goals omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem emitLeftZeroPredecessorMembers_effect_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hhorizon : 0 < values Work.horizon) :
    (emitLeftZeroPredecessorMembers stateCount).effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available + (values Work.horizon + 1)))
        Work.limit₀ (values Work.horizon + 1) := by
  rw [emitLeftZeroPredecessorMembers]
  funext i
  have hloop' : values 14 = 0 := by
    simpa [Work.loop₀] using hclean.loop₀
  have htemporary' : values 22 = 0 := by
    simpa [Work.temporary₀] using hclean.temporary₀
  have hreference' : values 7 = 0 := by
    simpa [Work.reference₀] using hclean.reference₀
  have hhorizon' : 0 < values 1 := by
    simpa [Work.horizon] using hhorizon
  simp [BinaryRoutine.seqList, BinaryRoutine.seq,
    emitPredecessorFalseRange_effect_internal,
    setPredecessorHorizonLimit_effect_internal, emitHeadReference_effect,
    BinaryRoutine.binaryPred, BinaryRoutine.addConst, BinaryRoutine.set,
    BinaryRoutine.clear, BinaryRoutine.identity, BinaryRoutine.emitBits, Work.horizon,
    Work.available, Work.position, Work.loop₀, Work.limit₀,
    Work.temporary₀, Work.reference₀]
  simp only [Function.update_apply]
  split_ifs
  all_goals (try simp_all)
  all_goals omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem emitLeftPositivePredecessorMembers_effect_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitLeftPositivePredecessorMembers stateCount).effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available + (values Work.horizon + 1)))
        Work.limit₀ (values Work.horizon + 1) := by
  let afterLimit :=
    (BinaryRoutine.binaryCopy Work.position Work.limit₀
      Work.copyCounter).effect values
  let afterLimitSucc :=
    (BinaryRoutine.addConst Work.limit₀ 1).effect afterLimit
  let afterPrefix := emitPredecessorFalseRange.effect afterLimitSucc
  let afterGap := preparePredecessorHorizonGap.effect afterPrefix
  let afterTail :=
    (emitLeftPositivePredecessorTail stateCount).effect afterGap
  have hafterLimit : afterLimit =
      Function.update values Work.limit₀ (values Work.position) := rfl
  have hafterLimitSucc : afterLimitSucc =
      Function.update afterLimit Work.limit₀
        (afterLimit Work.limit₀ + 1) := rfl
  have hafterPrefix : afterPrefix =
      Function.update
        (Function.update afterLimitSucc Work.available
          (afterLimitSucc Work.available +
            (afterLimitSucc Work.limit₀ - afterLimitSucc Work.loop₀)))
        Work.loop₀ 0 :=
    emitPredecessorFalseRange_effect_internal afterLimitSucc
  have hloopPrefix : afterPrefix Work.loop₀ = 0 := by
    rw [hafterPrefix]
    simp
  have hafterGap : afterGap =
      Function.update
        (Function.update afterPrefix Work.temporary₃
          (afterPrefix Work.horizon - afterPrefix Work.position))
        Work.loop₀ 0 :=
    preparePredecessorHorizonGap_effect_internal afterPrefix hloopPrefix
  have hloopGap : afterGap Work.loop₀ = 0 := by
    rw [hafterGap]
    simp
  have htemporaryGap : afterGap Work.temporary₀ = 0 := by
    rw [hafterGap, hafterPrefix, hafterLimitSucc, hafterLimit]
    have htemporary' : values 22 = 0 := by
      simpa [Work.temporary₀] using hclean.temporary₀
    simp [htemporary', Work.horizon, Work.available, Work.position,
      Work.loop₀, Work.limit₀, Work.temporary₀, Work.temporary₃]
  have hreferenceGap : afterGap Work.reference₀ = 0 := by
    rw [hafterGap, hafterPrefix, hafterLimitSucc, hafterLimit]
    have hreference' : values 7 = 0 := by
      simpa [Work.reference₀] using hclean.reference₀
    simp [hreference', Work.horizon, Work.available, Work.position,
      Work.loop₀, Work.limit₀, Work.reference₀, Work.temporary₃]
  have hafterTail : afterTail =
      Function.update
        (Function.update afterGap Work.available
          (afterGap Work.available + afterGap Work.temporary₃))
        Work.temporary₃ 0 :=
    emitLeftPositivePredecessorTail_effect_internal stateCount afterGap
      hloopGap htemporaryGap hreferenceGap
  rw [emitLeftPositivePredecessorMembers]
  change setPredecessorHorizonLimit.effect afterTail = _
  rw [setPredecessorHorizonLimit_effect_internal, hafterTail, hafterGap,
    hafterPrefix, hafterLimitSucc, hafterLimit]
  have hloop' : values 14 = 0 := by
    simpa [Work.loop₀] using hclean.loop₀
  have htarget' : values 30 ≤ values 1 := by
    simpa [Work.position, Work.horizon] using htarget
  funext i
  simp only [Work.horizon, Work.available, Work.position, Work.loop₀,
    Work.limit₀, Work.temporary₃, Function.update_apply]
  split_ifs
  all_goals (try simp_all)
  all_goals omega

theorem emitRightPredecessorMembers_effect_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitRightPredecessorMembers stateCount).effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available + (values Work.horizon + 1)))
        Work.limit₀ (values Work.horizon + 1) := by
  by_cases hzero : values Work.position = 0
  · rw [emitRightPredecessorMembers]
    simp only [BinaryRoutine.branchZero, hzero, ↓reduceIte]
    exact emitRightZeroPredecessorMembers_effect_internal values hclean.loop₀
  · rw [emitRightPredecessorMembers]
    simp only [BinaryRoutine.branchZero, hzero, ↓reduceIte]
    exact emitRightPositivePredecessorMembers_effect_internal stateCount values
      hclean (Nat.pos_of_ne_zero hzero) htarget

theorem emitLeftPredecessorMembers_effect_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitLeftPredecessorMembers stateCount).effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available + (values Work.horizon + 1)))
        Work.limit₀ (values Work.horizon + 1) := by
  by_cases hzero : values Work.position = 0
  · rw [emitLeftPredecessorMembers]
    simp only [BinaryRoutine.branchZero, hzero, ↓reduceIte]
    exact emitLeftZeroPredecessorMembers_effect_internal stateCount values
      hclean hhorizon
  · rw [emitLeftPredecessorMembers]
    simp only [BinaryRoutine.branchZero, hzero, ↓reduceIte]
    exact emitLeftPositivePredecessorMembers_effect_internal stateCount values
      hclean htarget

theorem emitPredecessorHeadMembers_effect_internal
    (stateCount directionCode : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitPredecessorHeadMembers stateCount directionCode).effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available + (values Work.horizon + 1)))
        Work.limit₀ (values Work.horizon + 1) := by
  by_cases hleft : directionCode = 0
  · simp only [emitPredecessorHeadMembers, hleft, ↓reduceIte]
    exact emitLeftPredecessorMembers_effect_internal stateCount values hclean
      hhorizon htarget
  · by_cases hright : directionCode = 1
    · simp only [emitPredecessorHeadMembers, hright, ↓reduceIte]
      exact emitRightPredecessorMembers_effect_internal stateCount values
        hclean htarget
    · simp only [emitPredecessorHeadMembers, hleft, hright, ↓reduceIte]
      exact emitStayPredecessorMembers_effect_internal stateCount values
        hclean htarget

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
theorem emitStayPredecessorMembers_emitted_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitStayPredecessorMembers stateCount).emitted values =
      ((indexedGateBlocks (values Work.position) fun _ =>
          [CircuitCode.RawGate.constant 0 false]) ++
        [CircuitCode.RawGate.copy
          (transitionHeadRef stateCount (values Work.horizon)
            (values Work.configBase) (values Work.tapeIndex)
            (values Work.position))] ++
        (indexedGateBlocks
          (values Work.horizon - values Work.position) fun _ =>
            [CircuitCode.RawGate.constant 0 false])).flatMap
        CircuitCode.RawGate.encode := by
  let afterLimit :=
    (BinaryRoutine.binaryCopy Work.position Work.limit₀
      Work.copyCounter).effect values
  let afterPrefix := emitPredecessorFalseRange.effect afterLimit
  let afterHead := (emitHeadReference stateCount).effect afterPrefix
  let afterLoopCopy :=
    (BinaryRoutine.binaryCopy Work.position Work.loop₀
      Work.copyCounter).effect afterHead
  let afterLoopSucc :=
    (BinaryRoutine.addConst Work.loop₀ 1).effect afterLoopCopy
  let afterHorizon := setPredecessorHorizonLimit.effect afterLoopSucc
  have hafterLimit : afterLimit =
      Function.update values Work.limit₀ (values Work.position) := rfl
  have hafterPrefix : afterPrefix =
      Function.update
        (Function.update afterLimit Work.available
          (afterLimit Work.available +
            (afterLimit Work.limit₀ - afterLimit Work.loop₀)))
        Work.loop₀ 0 :=
    emitPredecessorFalseRange_effect_internal afterLimit
  have hafterHead : afterHead =
      Function.update
        (Function.update
          (Function.update afterPrefix Work.temporary₀ 0) Work.available
            (afterPrefix Work.available + 1)) Work.reference₀ 0 :=
    emitHeadReference_effect stateCount false afterPrefix
  have hafterLoopCopy : afterLoopCopy =
      Function.update afterHead Work.loop₀ (afterHead Work.position) := rfl
  have hafterLoopSucc : afterLoopSucc =
      Function.update afterLoopCopy Work.loop₀
        (afterLoopCopy Work.loop₀ + 1) := rfl
  have hafterHorizon : afterHorizon =
      Function.update afterLoopSucc Work.limit₀
        (afterLoopSucc Work.horizon + 1) :=
    setPredecessorHorizonLimit_effect_internal afterLoopSucc
  have hrefLimit : afterLimit Work.reference₀ = 0 := by
    rw [hafterLimit]
    simpa [Work.limit₀, Work.reference₀] using hclean.reference₀
  have hrefHorizon : afterHorizon Work.reference₀ = 0 := by
    rw [hafterHorizon, hafterLoopSucc, hafterLoopCopy, hafterHead]
    simp [Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₀, Work.reference₀]
  have hprefixEmission :=
    emitPredecessorFalseRange_emitted_internal afterLimit hrefLimit
  have hsuffixEmission :=
    emitPredecessorFalseRange_emitted_internal afterHorizon hrefHorizon
  rw [emitStayPredecessorMembers]
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  change emitPredecessorFalseRange.emitted afterLimit ++
      (emitHeadReference stateCount).emitted afterPrefix ++
      emitPredecessorFalseRange.emitted afterHorizon = _
  rw [hprefixEmission, emitHeadReference_emitted, hsuffixEmission]
  rw [hafterHorizon, hafterLoopSucc, hafterLoopCopy, hafterHead,
    hafterPrefix, hafterLimit]
  have hloop' : values 14 = 0 := by
    simpa [Work.loop₀] using hclean.loop₀
  have htarget' : values 30 ≤ values 1 := by
    simpa [Work.position, Work.horizon] using htarget
  simp only [Work.horizon, Work.configBase, Work.available, Work.tapeIndex,
    Work.position, Work.loop₀, Work.limit₀, Work.temporary₀,
    Work.reference₀, Function.update_apply]
  split_ifs
  all_goals (simp_all [List.flatMap_append]; omega)

theorem emitRightZeroPredecessorMembers_emitted_internal
    (values : BinaryValues WorkCount)
    (hloop : values Work.loop₀ = 0)
    (hreference : values Work.reference₀ = 0) :
    emitRightZeroPredecessorMembers.emitted values =
      (indexedGateBlocks (values Work.horizon + 1) fun _ =>
        [CircuitCode.RawGate.constant 0 false]).flatMap
          CircuitCode.RawGate.encode := by
  let afterHorizon := setPredecessorHorizonLimit.effect values
  have hafterHorizon : afterHorizon =
      Function.update values Work.limit₀ (values Work.horizon + 1) :=
    setPredecessorHorizonLimit_effect_internal values
  have hrefHorizon : afterHorizon Work.reference₀ = 0 := by
    rw [hafterHorizon]
    simpa [Work.limit₀, Work.reference₀] using hreference
  rw [emitRightZeroPredecessorMembers, BinaryRoutine.seq]
  change [] ++ emitPredecessorFalseRange.emitted afterHorizon = _
  rw [emitPredecessorFalseRange_emitted_internal afterHorizon hrefHorizon,
    hafterHorizon]
  have hloop' : values 14 = 0 := by
    simpa [Work.loop₀] using hloop
  simp [hloop', directInitConstant, Work.horizon, Work.loop₀, Work.limit₀]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
theorem emitRightPositivePredecessorMembers_emitted_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hpositive : 0 < values Work.position)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitRightPositivePredecessorMembers stateCount).emitted values =
      ((indexedGateBlocks (values Work.position - 1) fun _ =>
          [CircuitCode.RawGate.constant 0 false]) ++
        [CircuitCode.RawGate.copy
          (transitionHeadRef stateCount (values Work.horizon)
            (values Work.configBase) (values Work.tapeIndex)
            (values Work.position - 1))] ++
        (indexedGateBlocks
          (values Work.horizon + 1 - values Work.position) fun _ =>
            [CircuitCode.RawGate.constant 0 false])).flatMap
        CircuitCode.RawGate.encode := by
  let afterLimit :=
    (BinaryRoutine.binaryCopy Work.position Work.limit₀
      Work.copyCounter).effect values
  let afterLimitPred :=
    (BinaryRoutine.binaryPred Work.limit₀).effect afterLimit
  let afterPrefix := emitPredecessorFalseRange.effect afterLimitPred
  let afterPositionPred :=
    (BinaryRoutine.binaryPred Work.position).effect afterPrefix
  let afterHead := (emitHeadReference stateCount).effect afterPositionPred
  let afterPositionSucc :=
    (BinaryRoutine.addConst Work.position 1).effect afterHead
  let afterLoopCopy :=
    (BinaryRoutine.binaryCopy Work.position Work.loop₀
      Work.copyCounter).effect afterPositionSucc
  let afterHorizon := setPredecessorHorizonLimit.effect afterLoopCopy
  have hafterLimit : afterLimit =
      Function.update values Work.limit₀ (values Work.position) := rfl
  have hafterLimitPred : afterLimitPred =
      Function.update afterLimit Work.limit₀
        (afterLimit Work.limit₀ - 1) := rfl
  have hafterPrefix : afterPrefix =
      Function.update
        (Function.update afterLimitPred Work.available
          (afterLimitPred Work.available +
            (afterLimitPred Work.limit₀ - afterLimitPred Work.loop₀)))
        Work.loop₀ 0 :=
    emitPredecessorFalseRange_effect_internal afterLimitPred
  have hafterPositionPred : afterPositionPred =
      Function.update afterPrefix Work.position
        (afterPrefix Work.position - 1) := rfl
  have hafterHead : afterHead =
      Function.update
        (Function.update
          (Function.update afterPositionPred Work.temporary₀ 0) Work.available
            (afterPositionPred Work.available + 1)) Work.reference₀ 0 :=
    emitHeadReference_effect stateCount false afterPositionPred
  have hafterPositionSucc : afterPositionSucc =
      Function.update afterHead Work.position
        (afterHead Work.position + 1) := rfl
  have hafterLoopCopy : afterLoopCopy =
      Function.update afterPositionSucc Work.loop₀
        (afterPositionSucc Work.position) := rfl
  have hafterHorizon : afterHorizon =
      Function.update afterLoopCopy Work.limit₀
        (afterLoopCopy Work.horizon + 1) :=
    setPredecessorHorizonLimit_effect_internal afterLoopCopy
  have hrefLimitPred : afterLimitPred Work.reference₀ = 0 := by
    rw [hafterLimitPred, hafterLimit]
    simpa [Work.limit₀, Work.reference₀] using hclean.reference₀
  have hrefHorizon : afterHorizon Work.reference₀ = 0 := by
    rw [hafterHorizon, hafterLoopCopy, hafterPositionSucc, hafterHead]
    simp [Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₀, Work.reference₀]
  have hprefixEmission :=
    emitPredecessorFalseRange_emitted_internal afterLimitPred hrefLimitPred
  have hsuffixEmission :=
    emitPredecessorFalseRange_emitted_internal afterHorizon hrefHorizon
  rw [emitRightPositivePredecessorMembers]
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  change emitPredecessorFalseRange.emitted afterLimitPred ++
      (emitHeadReference stateCount).emitted afterPositionPred ++
      emitPredecessorFalseRange.emitted afterHorizon = _
  rw [hprefixEmission, emitHeadReference_emitted, hsuffixEmission]
  rw [hafterHorizon, hafterLoopCopy, hafterPositionSucc, hafterHead,
    hafterPositionPred, hafterPrefix, hafterLimitPred, hafterLimit]
  have hloop' : values 14 = 0 := by
    simpa [Work.loop₀] using hclean.loop₀
  have hpositive' : 0 < values 30 := by
    simpa [Work.position] using hpositive
  have htarget' : values 30 ≤ values 1 := by
    simpa [Work.position, Work.horizon] using htarget
  simp only [Work.horizon, Work.configBase, Work.available, Work.tapeIndex,
    Work.position, Work.loop₀, Work.limit₀, Work.temporary₀,
    Work.reference₀, Function.update_apply]
  split_ifs
  all_goals (simp_all [List.flatMap_append]; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
theorem emitLeftZeroPredecessorMembers_emitted_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hposition : values Work.position = 0)
    (hhorizon : 0 < values Work.horizon) :
    (emitLeftZeroPredecessorMembers stateCount).emitted values =
      ([CircuitCode.RawGate.copy
          (transitionHeadRef stateCount (values Work.horizon)
            (values Work.configBase) (values Work.tapeIndex) 0),
        CircuitCode.RawGate.copy
          (transitionHeadRef stateCount (values Work.horizon)
            (values Work.configBase) (values Work.tapeIndex) 1)] ++
        (indexedGateBlocks (values Work.horizon - 1) fun _ =>
          [CircuitCode.RawGate.constant 0 false])).flatMap
        CircuitCode.RawGate.encode := by
  let afterHead₀ := (emitHeadReference stateCount).effect values
  let afterPositionSucc :=
    (BinaryRoutine.addConst Work.position 1).effect afterHead₀
  let afterHead₁ :=
    (emitHeadReference stateCount).effect afterPositionSucc
  let afterPositionPred :=
    (BinaryRoutine.binaryPred Work.position).effect afterHead₁
  let afterLoop := (BinaryRoutine.set Work.loop₀ 2).effect afterPositionPred
  let afterHorizon := setPredecessorHorizonLimit.effect afterLoop
  have hafterHead₀ : afterHead₀ =
      Function.update
        (Function.update
          (Function.update values Work.temporary₀ 0) Work.available
            (values Work.available + 1)) Work.reference₀ 0 :=
    emitHeadReference_effect stateCount false values
  have hafterPositionSucc : afterPositionSucc =
      Function.update afterHead₀ Work.position
        (afterHead₀ Work.position + 1) := rfl
  have hafterHead₁ : afterHead₁ =
      Function.update
        (Function.update
          (Function.update afterPositionSucc Work.temporary₀ 0) Work.available
            (afterPositionSucc Work.available + 1)) Work.reference₀ 0 :=
    emitHeadReference_effect stateCount false afterPositionSucc
  have hafterPositionPred : afterPositionPred =
      Function.update afterHead₁ Work.position
        (afterHead₁ Work.position - 1) := rfl
  have hafterLoop : afterLoop =
      Function.update afterPositionPred Work.loop₀ 2 := by
    funext i
    simp [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
      BinaryRoutine.addConst]
  have hafterHorizon : afterHorizon =
      Function.update afterLoop Work.limit₀
        (afterLoop Work.horizon + 1) :=
    setPredecessorHorizonLimit_effect_internal afterLoop
  have hrefHorizon : afterHorizon Work.reference₀ = 0 := by
    rw [hafterHorizon, hafterLoop, hafterPositionPred, hafterHead₁]
    simp [Work.horizon, Work.position, Work.loop₀, Work.limit₀,
      Work.reference₀]
  have hsuffixEmission :=
    emitPredecessorFalseRange_emitted_internal afterHorizon hrefHorizon
  rw [emitLeftZeroPredecessorMembers]
  change (emitHeadReference stateCount).emitted values ++
      (emitHeadReference stateCount).emitted afterPositionSucc ++
      emitPredecessorFalseRange.emitted afterHorizon = _
  rw [emitHeadReference_emitted, emitHeadReference_emitted,
    hsuffixEmission, hafterHorizon, hafterLoop, hafterPositionPred,
    hafterHead₁, hafterPositionSucc, hafterHead₀]
  have hposition' : values 30 = 0 := by
    simpa [Work.position] using hposition
  have hhorizon' : 0 < values 1 := by
    simpa [Work.horizon] using hhorizon
  simp only [Work.horizon, Work.configBase, Work.available, Work.tapeIndex,
    Work.position, Work.loop₀, Work.limit₀, Work.temporary₀,
    Work.reference₀, Function.update_apply]
  split_ifs
  all_goals (simp_all [List.flatMap_append]; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
theorem emitLeftPositivePredecessorTail_emitted_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hloop : values Work.loop₀ = 0) :
    (emitLeftPositivePredecessorTail stateCount).emitted values =
      if values Work.temporary₃ = 0 then [] else
        ([CircuitCode.RawGate.copy
            (transitionHeadRef stateCount (values Work.horizon)
              (values Work.configBase) (values Work.tapeIndex)
              (values Work.position + 1))] ++
          (indexedGateBlocks (values Work.temporary₃ - 1) fun _ =>
            [CircuitCode.RawGate.constant 0 false])).flatMap
          CircuitCode.RawGate.encode := by
  by_cases hgap : values Work.temporary₃ = 0
  · rw [emitLeftPositivePredecessorTail]
    simp [BinaryRoutine.branchZero, hgap, BinaryRoutine.clear]
  · let afterPositionSucc :=
      (BinaryRoutine.addConst Work.position 1).effect values
    let afterHead :=
      (emitHeadReference stateCount).effect afterPositionSucc
    let afterPositionPred :=
      (BinaryRoutine.binaryPred Work.position).effect afterHead
    let afterGapPred :=
      (BinaryRoutine.binaryPred Work.temporary₃).effect afterPositionPred
    have hafterPositionSucc : afterPositionSucc =
        Function.update values Work.position
          (values Work.position + 1) := rfl
    have hafterHead : afterHead =
        Function.update
          (Function.update
            (Function.update afterPositionSucc Work.temporary₀ 0)
              Work.available (afterPositionSucc Work.available + 1))
          Work.reference₀ 0 :=
      emitHeadReference_effect stateCount false afterPositionSucc
    have hafterPositionPred : afterPositionPred =
        Function.update afterHead Work.position
          (afterHead Work.position - 1) := rfl
    have hafterGapPred : afterGapPred =
        Function.update afterPositionPred Work.temporary₃
          (afterPositionPred Work.temporary₃ - 1) := rfl
    have hrefGapPred : afterGapPred Work.reference₀ = 0 := by
      rw [hafterGapPred, hafterPositionPred, hafterHead]
      simp [Work.available, Work.position, Work.temporary₀,
        Work.temporary₃, Work.reference₀]
    rw [emitLeftPositivePredecessorTail]
    simp only [BinaryRoutine.branchZero, hgap, ↓reduceIte]
    simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
      BinaryRoutine.identity, BinaryRoutine.emitBits]
    change (emitHeadReference stateCount).emitted afterPositionSucc ++
        BinaryRoutine.binaryForEmitted (emitConstantGate false) Work.loop₀
          afterGapPred
            (afterGapPred Work.temporary₃ - afterGapPred Work.loop₀) = _
    rw [emitHeadReference_emitted,
      emitConstantFalse_binaryForEmitted afterGapPred hrefGapPred]
    rw [hafterGapPred, hafterPositionPred, hafterHead,
      hafterPositionSucc]
    have hloop' : values 14 = 0 := by
      simpa [Work.loop₀] using hloop
    have hgap' : values 25 ≠ 0 := by
      simpa [Work.temporary₃] using hgap
    simp only [Work.horizon, Work.configBase, Work.available,
      Work.tapeIndex, Work.position, Work.loop₀, Work.temporary₀,
      Work.temporary₃, Work.reference₀, Function.update_apply]
    split_ifs
    all_goals (simp_all [List.flatMap_append]; omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
theorem emitLeftPositivePredecessorMembers_emitted_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitLeftPositivePredecessorMembers stateCount).emitted values =
      ((indexedGateBlocks (values Work.position + 1) fun _ =>
          [CircuitCode.RawGate.constant 0 false]) ++
        if values Work.horizon - values Work.position = 0 then [] else
          [CircuitCode.RawGate.copy
            (transitionHeadRef stateCount (values Work.horizon)
              (values Work.configBase) (values Work.tapeIndex)
              (values Work.position + 1))] ++
            (indexedGateBlocks
              (values Work.horizon - values Work.position - 1) fun _ =>
                [CircuitCode.RawGate.constant 0 false])).flatMap
        CircuitCode.RawGate.encode := by
  let afterLimit :=
    (BinaryRoutine.binaryCopy Work.position Work.limit₀
      Work.copyCounter).effect values
  let afterLimitSucc :=
    (BinaryRoutine.addConst Work.limit₀ 1).effect afterLimit
  let afterPrefix := emitPredecessorFalseRange.effect afterLimitSucc
  let afterGap := preparePredecessorHorizonGap.effect afterPrefix
  have hafterLimit : afterLimit =
      Function.update values Work.limit₀ (values Work.position) := rfl
  have hafterLimitSucc : afterLimitSucc =
      Function.update afterLimit Work.limit₀
        (afterLimit Work.limit₀ + 1) := rfl
  have hafterPrefix : afterPrefix =
      Function.update
        (Function.update afterLimitSucc Work.available
          (afterLimitSucc Work.available +
            (afterLimitSucc Work.limit₀ - afterLimitSucc Work.loop₀)))
        Work.loop₀ 0 :=
    emitPredecessorFalseRange_effect_internal afterLimitSucc
  have hloopPrefix : afterPrefix Work.loop₀ = 0 := by
    rw [hafterPrefix]
    simp
  have hafterGap : afterGap =
      Function.update
        (Function.update afterPrefix Work.temporary₃
          (afterPrefix Work.horizon - afterPrefix Work.position))
        Work.loop₀ 0 :=
    preparePredecessorHorizonGap_effect_internal afterPrefix hloopPrefix
  have hloopGap : afterGap Work.loop₀ = 0 := by
    rw [hafterGap]
    simp
  have hrefLimitSucc : afterLimitSucc Work.reference₀ = 0 := by
    rw [hafterLimitSucc, hafterLimit]
    simpa [Work.limit₀, Work.reference₀] using hclean.reference₀
  have hprefixEmission :=
    emitPredecessorFalseRange_emitted_internal afterLimitSucc hrefLimitSucc
  have htailEmission :=
    emitLeftPositivePredecessorTail_emitted_internal stateCount afterGap
      hloopGap
  rw [emitLeftPositivePredecessorMembers]
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  change emitPredecessorFalseRange.emitted afterLimitSucc ++
      preparePredecessorHorizonGap.emitted afterPrefix ++
      (emitLeftPositivePredecessorTail stateCount).emitted afterGap = _
  rw [hprefixEmission, preparePredecessorHorizonGap_emitted_internal,
    htailEmission, hafterGap, hafterPrefix, hafterLimitSucc, hafterLimit]
  have hloop' : values 14 = 0 := by
    simpa [Work.loop₀] using hclean.loop₀
  have htarget' : values 30 ≤ values 1 := by
    simpa [Work.position, Work.horizon] using htarget
  simp only [Work.horizon, Work.configBase, Work.available, Work.tapeIndex,
    Work.position, Work.loop₀, Work.limit₀, Work.temporary₃,
    Function.update_apply]
  split_ifs
  all_goals (simp_all [List.flatMap_append]; omega)

private theorem getElem_indexedSingletonBlocks
    (count : ℕ) (gateAt : ℕ → CircuitCode.RawGate)
    (index : ℕ) (hindex : index < count) :
    (indexedGateBlocks count fun source => [gateAt source])[index]'(by
      rw [length_indexedGateBlocks count 1 _ (by simp)]
      omega) = gateAt index := by
  have hget := getElem_indexedGateBlocks count 1
    (fun source => [gateAt source]) (by simp) index 0 hindex (by omega)
  simpa using hget

private theorem getElem_predecessorHeadMemberGates
    (stateCount T configBase tapeIndex target directionCode source : ℕ)
    (hsource : source < T + 1) :
    (predecessorHeadMemberGates stateCount T configBase tapeIndex target
      directionCode)[source]'(by
        rw [length_predecessorHeadMemberGates]
        exact hsource) =
      predecessorHeadMemberGate stateCount T configBase tapeIndex target
        directionCode source := by
  unfold predecessorHeadMemberGates
  exact getElem_indexedSingletonBlocks (T + 1)
    (predecessorHeadMemberGate stateCount T configBase tapeIndex target
      directionCode) source hsource

private theorem stayPredecessorMemberStream_eq
    (stateCount T configBase tapeIndex target : ℕ)
    (htarget : target ≤ T) :
    (indexedGateBlocks target fun _ =>
        [CircuitCode.RawGate.constant 0 false]) ++
      [CircuitCode.RawGate.copy
        (transitionHeadRef stateCount T configBase tapeIndex target)] ++
      (indexedGateBlocks (T - target) fun _ =>
        [CircuitCode.RawGate.constant 0 false]) =
      predecessorHeadMemberGates stateCount T configBase tapeIndex target 2 := by
  apply List.ext_getElem
  · simp [length_predecessorHeadMemberGates]
    omega
  · intro index hleft hright
    have hsource : index < T + 1 := by
      simpa [length_predecessorHeadMemberGates] using hright
    rw [getElem_predecessorHeadMemberGates stateCount T configBase tapeIndex
      target 2 index hsource]
    by_cases hbefore : index < target
    · rw [List.getElem_append_left]
      · rw [List.getElem_append_left]
        · rw [getElem_indexedSingletonBlocks target
            (fun _ => CircuitCode.RawGate.constant 0 false) index hbefore]
          simp [predecessorHeadMemberGate, movedHeadPositionCode]
          omega
        · simp [length_indexedGateBlocks]
          omega

private theorem rightZeroPredecessorMemberStream_eq
    (stateCount T configBase tapeIndex : ℕ) :
    (indexedGateBlocks (T + 1) fun _ =>
        [CircuitCode.RawGate.constant 0 false]) =
      predecessorHeadMemberGates stateCount T configBase tapeIndex 0 1 := by
  apply List.ext_getElem
  · simp [length_predecessorHeadMemberGates]
  · intro index hleft hright
    have hsource : index < T + 1 := by
      simpa [length_predecessorHeadMemberGates] using hright
    rw [getElem_indexedSingletonBlocks (T + 1)
      (fun _ => CircuitCode.RawGate.constant 0 false) index hsource,
      getElem_predecessorHeadMemberGates stateCount T configBase tapeIndex
        0 1 index hsource]
    simp [predecessorHeadMemberGate, movedHeadPositionCode]

private theorem rightPositivePredecessorMemberStream_eq
    (stateCount T configBase tapeIndex target : ℕ)
    (hpositive : 0 < target) (htarget : target ≤ T) :
    (indexedGateBlocks (target - 1) fun _ =>
        [CircuitCode.RawGate.constant 0 false]) ++
      [CircuitCode.RawGate.copy
        (transitionHeadRef stateCount T configBase tapeIndex (target - 1))] ++
      (indexedGateBlocks (T + 1 - target) fun _ =>
        [CircuitCode.RawGate.constant 0 false]) =
      predecessorHeadMemberGates stateCount T configBase tapeIndex target 1 := by
  apply List.ext_getElem
  · simp [length_predecessorHeadMemberGates]
    omega
  · intro index hleft hright
    have hsource : index < T + 1 := by
      simpa [length_predecessorHeadMemberGates] using hright
    by_cases hbefore : index < target - 1
    · rw [List.getElem_append_left]
      · rw [List.getElem_append_left]
        · rw [getElem_indexedSingletonBlocks (target - 1)
            (fun _ => CircuitCode.RawGate.constant 0 false) index hbefore,
          getElem_predecessorHeadMemberGates stateCount T configBase tapeIndex
            target 1 index hsource]
          simp [predecessorHeadMemberGate, movedHeadPositionCode]
          omega
        · simp [length_indexedGateBlocks]
          omega
      · simp [length_indexedGateBlocks]
        omega
    · by_cases hat : index = target - 1
      · subst index
        rw [List.getElem_append_left]
        · rw [List.getElem_append_right]
          all_goals simp [length_indexedGateBlocks,
            getElem_predecessorHeadMemberGates,
            predecessorHeadMemberGate, movedHeadPositionCode]
          omega
        · simp [length_indexedGateBlocks]
          omega
      · rw [List.getElem_append_right]
        · have htail : index - target < T + 1 - target := by omega
          rw [getElem_indexedSingletonBlocks (T + 1 - target)
            (fun _ => CircuitCode.RawGate.constant 0 false)
            (index - target) htail,
            getElem_predecessorHeadMemberGates stateCount T configBase
              tapeIndex target 1 index hsource]
          simp [predecessorHeadMemberGate, movedHeadPositionCode]
          omega
        · simp [length_indexedGateBlocks]
          omega

private theorem leftZeroPredecessorMemberStream_eq
    (stateCount T configBase tapeIndex : ℕ) (hpositive : 0 < T) :
    [CircuitCode.RawGate.copy
        (transitionHeadRef stateCount T configBase tapeIndex 0),
      CircuitCode.RawGate.copy
        (transitionHeadRef stateCount T configBase tapeIndex 1)] ++
      (indexedGateBlocks (T - 1) fun _ =>
        [CircuitCode.RawGate.constant 0 false]) =
      predecessorHeadMemberGates stateCount T configBase tapeIndex 0 0 := by
  apply List.ext_getElem
  · simp [length_predecessorHeadMemberGates]
    omega
  · intro index hleft hright
    have hsource : index < T + 1 := by
      simpa [length_predecessorHeadMemberGates] using hright
    by_cases hprefix : index < 2
    · rw [List.getElem_append_left]
      · rw [getElem_predecessorHeadMemberGates stateCount T configBase
          tapeIndex 0 0 index hsource]
        interval_cases index <;>
          simp [predecessorHeadMemberGate, movedHeadPositionCode]
      · simp
        omega
    · rw [List.getElem_append_right]
      · have htail : index - 2 < T - 1 := by omega
        rw [getElem_indexedSingletonBlocks (T - 1)
          (fun _ => CircuitCode.RawGate.constant 0 false) (index - 2) htail,
          getElem_predecessorHeadMemberGates stateCount T configBase tapeIndex
            0 0 index hsource]
        simp [predecessorHeadMemberGate, movedHeadPositionCode]
        omega
      · simp
        omega

private theorem leftPositivePredecessorMemberStream_eq
    (stateCount T configBase tapeIndex target : ℕ)
    (hpositive : 0 < target) (htarget : target ≤ T) :
    (indexedGateBlocks (target + 1) fun _ =>
        [CircuitCode.RawGate.constant 0 false]) ++
      (if T - target = 0 then [] else
        [CircuitCode.RawGate.copy
          (transitionHeadRef stateCount T configBase tapeIndex (target + 1))] ++
        (indexedGateBlocks (T - target - 1) fun _ =>
          [CircuitCode.RawGate.constant 0 false])) =
      predecessorHeadMemberGates stateCount T configBase tapeIndex target 0 := by
  by_cases heq : target = T
  · subst target
    simp only [Nat.sub_self, ↓reduceIte, List.append_nil]
    apply List.ext_getElem
    · simp [length_predecessorHeadMemberGates]
    · intro index hleft hright
      have hsource : index < T + 1 := by
        simpa [length_predecessorHeadMemberGates] using hright
      rw [getElem_indexedSingletonBlocks (T + 1)
        (fun _ => CircuitCode.RawGate.constant 0 false) index hsource,
        getElem_predecessorHeadMemberGates stateCount T configBase tapeIndex
          T 0 index hsource]
      simp [predecessorHeadMemberGate, movedHeadPositionCode]
      omega
  · have htargetLt : target < T := by omega
    have hgap : T - target ≠ 0 := by omega
    simp only [hgap, ↓reduceIte]
    apply List.ext_getElem
    · simp [length_predecessorHeadMemberGates]
      omega
    · intro index hleft hright
      have hsource : index < T + 1 := by
        simpa [length_predecessorHeadMemberGates] using hright
      by_cases hbefore : index < target + 1
      · rw [List.getElem_append_left]
        · rw [getElem_indexedSingletonBlocks (target + 1)
            (fun _ => CircuitCode.RawGate.constant 0 false) index hbefore,
          getElem_predecessorHeadMemberGates stateCount T configBase tapeIndex
            target 0 index hsource]
          simp [predecessorHeadMemberGate, movedHeadPositionCode]
          omega
        · simp [length_indexedGateBlocks]
          omega
      · by_cases hat : index = target + 1
        · subst index
          rw [List.getElem_append_right]
          · rw [List.getElem_append_left]
            · rw [getElem_predecessorHeadMemberGates stateCount T configBase
                tapeIndex target 0 (target + 1) (by omega)]
              simp [predecessorHeadMemberGate, movedHeadPositionCode]
            · simp
          · simp [length_indexedGateBlocks]
        · rw [List.getElem_append_right]
          · rw [List.getElem_append_right]
            · have htail : index - (target + 2) < T - target - 1 := by omega
              rw [getElem_indexedSingletonBlocks (T - target - 1)
                (fun _ => CircuitCode.RawGate.constant 0 false)
                (index - (target + 2)) htail,
                getElem_predecessorHeadMemberGates stateCount T configBase
                  tapeIndex target 0 index hsource]
              simp [predecessorHeadMemberGate, movedHeadPositionCode]
              omega
            · simp
              omega
          · simp [length_indexedGateBlocks]
            omega

theorem emitRightPredecessorMembers_emitted_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitRightPredecessorMembers stateCount).emitted values =
      (predecessorHeadMemberGates stateCount (values Work.horizon)
        (values Work.configBase) (values Work.tapeIndex)
        (values Work.position) 1).flatMap CircuitCode.RawGate.encode := by
  by_cases hzero : values Work.position = 0
  · rw [emitRightPredecessorMembers]
    simp only [BinaryRoutine.branchZero, hzero, ↓reduceIte]
    rw [emitRightZeroPredecessorMembers_emitted_internal values hclean.loop₀
      hclean.reference₀]
    congr 1
    simpa [hzero] using rightZeroPredecessorMemberStream_eq stateCount
      (values Work.horizon) (values Work.configBase) (values Work.tapeIndex)
  · rw [emitRightPredecessorMembers]
    simp only [BinaryRoutine.branchZero, hzero, ↓reduceIte]
    have hpositive := Nat.pos_of_ne_zero hzero
    rw [emitRightPositivePredecessorMembers_emitted_internal stateCount values
      hclean hpositive htarget]
    congr 1
    exact rightPositivePredecessorMemberStream_eq stateCount
      (values Work.horizon) (values Work.configBase) (values Work.tapeIndex)
      (values Work.position) hpositive htarget

theorem emitLeftPredecessorMembers_emitted_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitLeftPredecessorMembers stateCount).emitted values =
      (predecessorHeadMemberGates stateCount (values Work.horizon)
        (values Work.configBase) (values Work.tapeIndex)
        (values Work.position) 0).flatMap CircuitCode.RawGate.encode := by
  by_cases hzero : values Work.position = 0
  · rw [emitLeftPredecessorMembers]
    simp only [BinaryRoutine.branchZero, hzero, ↓reduceIte]
    rw [emitLeftZeroPredecessorMembers_emitted_internal stateCount values
      hclean hzero hhorizon]
    congr 1
    simpa [hzero] using leftZeroPredecessorMemberStream_eq stateCount
      (values Work.horizon) (values Work.configBase) (values Work.tapeIndex)
      hhorizon
  · rw [emitLeftPredecessorMembers]
    simp only [BinaryRoutine.branchZero, hzero, ↓reduceIte]
    have hpositive := Nat.pos_of_ne_zero hzero
    rw [emitLeftPositivePredecessorMembers_emitted_internal stateCount values
      hclean htarget]
    congr 1
    exact leftPositivePredecessorMemberStream_eq stateCount
      (values Work.horizon) (values Work.configBase) (values Work.tapeIndex)
      (values Work.position) hpositive htarget

theorem emitPredecessorHeadMembers_emitted_internal
    (stateCount directionCode : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitPredecessorHeadMembers stateCount directionCode).emitted values =
      (predecessorHeadMemberGates stateCount (values Work.horizon)
        (values Work.configBase) (values Work.tapeIndex)
        (values Work.position) directionCode).flatMap
          CircuitCode.RawGate.encode := by
  by_cases hleft : directionCode = 0
  · subst directionCode
    simp only [emitPredecessorHeadMembers, ↓reduceIte]
    exact emitLeftPredecessorMembers_emitted_internal stateCount values
      hclean hhorizon htarget
  · by_cases hright : directionCode = 1
    · subst directionCode
      simp only [emitPredecessorHeadMembers, one_ne_zero, ↓reduceIte]
      exact emitRightPredecessorMembers_emitted_internal stateCount values
        hclean htarget
    · simp only [emitPredecessorHeadMembers, hleft, hright, ↓reduceIte]
      rw [emitStayPredecessorMembers_emitted_internal stateCount values hclean
        htarget]
      congr 1
      have hcode : movedHeadPositionCode (values Work.position)
          directionCode = values Work.position := by
        simp [movedHeadPositionCode, hleft, hright]
      exact stayPredecessorMemberStream_eq stateCount (values Work.horizon)
        (values Work.configBase) (values Work.tapeIndex)
        (values Work.position) htarget |>.trans (by
          apply List.ext_getElem
          · simp [length_predecessorHeadMemberGates]
          · intro index htwo hcodeLength
            have hsource : index < values Work.horizon + 1 := by
              simpa [length_predecessorHeadMemberGates] using hcodeLength
            rw [getElem_predecessorHeadMemberGates stateCount
              (values Work.horizon) (values Work.configBase)
              (values Work.tapeIndex) (values Work.position) 2 index hsource,
              getElem_predecessorHeadMemberGates stateCount
                (values Work.horizon) (values Work.configBase)
                (values Work.tapeIndex) (values Work.position) directionCode
                index hsource]
            simp [predecessorHeadMemberGate, movedHeadPositionCode, hleft,
              hright])

private theorem predecessorConnectorDistinct :
    DynamicRecentGateDistinct Work.temporary₃ Work.loop₁ := by
  exact
    { reference_ne_offset := by decide
      reference_ne_counter := by decide
      offset_ne_counter := by decide
      available_ne_reference := by decide
      available_ne_offset := by decide
      available_ne_counter := by decide
      available_ne_copyCounter := by decide
      reference_ne_copyCounter := by decide
      offset_ne_copyCounter := by decide
      counter_ne_copyCounter := by decide
      available_ne_reference₁ := by decide
      available_ne_emitCounter := by decide
      reference₀_ne_reference₁ := by decide
      reference₀_ne_emitCounter := by decide
      offset_ne_reference₁ := by decide
      offset_ne_emitCounter := by decide
      counter_ne_reference₁ := by decide
      counter_ne_emitCounter := by decide
      copyCounter_ne_reference₁ := by decide
      copyCounter_ne_emitCounter := by decide
      reference₁_ne_emitCounter := by decide }

theorem emitPredecessorHeadConnector_effect_internal
    (values : BinaryValues WorkCount)
    (hloop : values Work.loop₁ = 0) :
    emitPredecessorHeadConnector.effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update values Work.loop₁ 0) Work.available
                (values Work.available + 1)) Work.reference₀ 0)
          Work.reference₁ 0) Work.temporary₃
        (values Work.temporary₃ + 2) := by
  rw [emitPredecessorHeadConnector, BinaryRoutine.seq]
  change (BinaryRoutine.addConst Work.temporary₃ 2).effect
      ((emitDynamicRecentGate .or false false Work.temporary₃ Work.loop₁
        1).effect values) = _
  rw [emitDynamicRecentGate_effect .or false false Work.temporary₃
    Work.loop₁ 1 values predecessorConnectorDistinct hloop]
  rfl

theorem emitPredecessorHeadConnector_emitted_internal
    (values : BinaryValues WorkCount)
    (hloop : values Work.loop₁ = 0) :
    emitPredecessorHeadConnector.emitted values =
      CircuitCode.RawGate.encode
        { op := .or
          input₀ := values Work.available - values Work.temporary₃
          input₁ := values Work.available - 1
          negated₀ := false
          negated₁ := false } := by
  rw [emitPredecessorHeadConnector, BinaryRoutine.seq]
  change (emitDynamicRecentGate .or false false Work.temporary₃ Work.loop₁
      1).emitted values ++ [] = _
  rw [emitDynamicRecentGate_emitted .or false false Work.temporary₃
    Work.loop₁ 1 values predecessorConnectorDistinct hloop]
  simp

private theorem emitPredecessorHeadConnector_binaryForValues
    (initial : BinaryValues WorkCount)
    (hloop₁ : initial Work.loop₁ = 0)
    (hreference₀ : initial Work.reference₀ = 0)
    (hreference₁ : initial Work.reference₁ = 0) : ∀ count,
    BinaryRoutine.binaryForValues emitPredecessorHeadConnector Work.loop₀
        initial count =
      Function.update
        (Function.update
          (Function.update initial Work.available
            (initial Work.available + count)) Work.temporary₃
          (initial Work.temporary₃ + 2 * count)) Work.loop₀
        (initial Work.loop₀ + count) := by
  intro count
  induction count with
  | zero => simp [BinaryRoutine.binaryForValues]
  | succ count ih =>
      have hcurrentLoop₁ :
          (BinaryRoutine.binaryForValues emitPredecessorHeadConnector
            Work.loop₀ initial count) Work.loop₁ = 0 := by
        rw [ih]
        simpa [Work.available, Work.temporary₃, Work.loop₀, Work.loop₁]
          using hloop₁
      rw [BinaryRoutine.binaryForValues, BinaryRoutine.binaryForStep,
        emitPredecessorHeadConnector_effect_internal _ hcurrentLoop₁, ih]
      funext i
      by_cases hiloop : i = Work.loop₀
      · subst i
        simp [Work.available, Work.reference₀, Work.reference₁,
          Work.loop₀, Work.loop₁, Work.temporary₃]
        omega
      by_cases hitemporary : i = Work.temporary₃
      · subst i
        simp [hiloop, Work.available, Work.reference₀, Work.reference₁,
          Work.loop₀, Work.loop₁, Work.temporary₃, Nat.mul_succ]
        omega
      by_cases hiavailable : i = Work.available
      · subst i
        simp [hiloop, hitemporary, Work.available, Work.reference₀,
          Work.reference₁, Work.loop₀, Work.loop₁, Work.temporary₃]
        omega
      by_cases hiloop₁ : i = Work.loop₁
      · subst i
        simpa [hiloop, hitemporary, hiavailable, Work.available,
          Work.reference₀, Work.reference₁, Work.loop₀, Work.loop₁,
          Work.temporary₃] using hloop₁.symm
      by_cases hireference₀ : i = Work.reference₀
      · subst i
        simpa [hiloop, hitemporary, hiavailable, hiloop₁, Work.available,
          Work.reference₀, Work.reference₁, Work.loop₀, Work.loop₁,
          Work.temporary₃] using hreference₀.symm
      by_cases hireference₁ : i = Work.reference₁
      · subst i
        simpa [hiloop, hitemporary, hiavailable, hiloop₁, hireference₀,
          Work.available, Work.reference₀, Work.reference₁, Work.loop₀,
          Work.loop₁, Work.temporary₃] using hreference₁.symm
      · simp [hiloop, hitemporary, hiavailable, hiloop₁, hireference₀,
          hireference₁]

private theorem binaryForEmitted_eq_indexedGateBlocks
    (body : BinaryRoutine n) (counterIdx : Fin n)
    (initial : BinaryValues n) (blockAt : ℕ → CircuitCode.RawCircuit)
    (hemitted : ∀ count,
      body.emitted
          (BinaryRoutine.binaryForValues body counterIdx initial count) =
        (blockAt count).flatMap CircuitCode.RawGate.encode) : ∀ count,
    BinaryRoutine.binaryForEmitted body counterIdx initial count =
      (indexedGateBlocks count blockAt).flatMap
        CircuitCode.RawGate.encode := by
  intro count
  induction count with
  | zero => simp [BinaryRoutine.binaryForEmitted, indexedGateBlocks]
  | succ count ih =>
      rw [BinaryRoutine.binaryForEmitted, ih, hemitted,
        indexedGateBlocks_succ_last]
      simp only [List.flatMap_append]

private theorem emitPredecessorHeadConnector_binaryForEmitted
    (initial : BinaryValues WorkCount)
    (hloop₁ : initial Work.loop₁ = 0)
    (hreference₀ : initial Work.reference₀ = 0)
    (hreference₁ : initial Work.reference₁ = 0) : ∀ count,
    BinaryRoutine.binaryForEmitted emitPredecessorHeadConnector Work.loop₀
        initial count =
      (indexedGateBlocks count fun rank =>
        [{ op := .or
           input₀ := initial Work.available + rank -
             (initial Work.temporary₃ + 2 * rank)
           input₁ := initial Work.available + rank - 1
           negated₀ := false
           negated₁ := false }]).flatMap CircuitCode.RawGate.encode := by
  intro count
  apply binaryForEmitted_eq_indexedGateBlocks
  intro rank
  have htrajectory := emitPredecessorHeadConnector_binaryForValues initial
    hloop₁ hreference₀ hreference₁ rank
  have hcurrentLoop₁ :
      (BinaryRoutine.binaryForValues emitPredecessorHeadConnector Work.loop₀
        initial rank) Work.loop₁ = 0 := by
    rw [htrajectory]
    simpa [Work.available, Work.temporary₃, Work.loop₀, Work.loop₁]
      using hloop₁
  rw [emitPredecessorHeadConnector_emitted_internal _ hcurrentLoop₁,
    htrajectory]
  simp [Work.available, Work.temporary₃, Work.loop₀]

private theorem prefixSize_fixedWidthSizeAt_of_le
    (count width upto : ℕ) (hupto : upto ≤ count) :
    prefixSize (fixedWidthSizeAt count width) upto = width * upto := by
  induction upto with
  | zero => simp [prefixSize]
  | succ upto ih =>
      have huptoLe : upto ≤ count := by omega
      have huptoLt : upto < count := by omega
      rw [prefixSize, ih huptoLe, fixedWidthSizeAt_of_lt huptoLt]
      ring

private theorem indexedPredecessorConnector_eq
    (available count rank : ℕ) (hrank : rank < count) :
    ({ op := .or
       input₀ := available + count + 1 + rank - (2 + 2 * rank)
       input₁ := available + count + 1 + rank - 1
       negated₀ := false
       negated₁ := false } : CircuitCode.RawGate) =
      indexedRightFoldConnector .or available count
        (fixedWidthSizeAt count 1) rank := by
  unfold indexedRightFoldConnector reverseMember
  dsimp only
  have hmember : count - rank - 1 + 1 = count - rank := by omega
  rw [hmember,
    prefixSize_fixedWidthSizeAt_of_le count 1 (count - rank) (by omega),
    prefixSize_fixedWidthSizeAt_of_le count 1 count (by omega)]
  simp only [Nat.one_mul]
  congr <;> omega

private theorem predecessorConnectorBlocks_eq
    (available count : ℕ) :
    indexedGateBlocks count (fun rank =>
        [{ op := .or
           input₀ := available + count + 1 + rank - (2 + 2 * rank)
           input₁ := available + count + 1 + rank - 1
           negated₀ := false
           negated₁ := false }]) =
      indexedRightFoldConnectors .or available count
        (fixedWidthSizeAt count 1) := by
  apply List.ext_getElem
  · simp [length_indexedGateBlocks]
  · intro index hleft hright
    have hindex : index < count := by
      simpa [length_indexedRightFoldConnectors] using hright
    rw [getElem_indexedSingletonBlocks count (fun rank =>
      ({ op := .or
         input₀ := available + count + 1 + rank - (2 + 2 * rank)
         input₁ := available + count + 1 + rank - 1
         negated₀ := false
         negated₁ := false } : CircuitCode.RawGate)) index hindex]
    exact (indexedPredecessorConnector_eq available count index hindex).trans
      (getElem_indexedRightFoldConnectors .or available count
        (fixedWidthSizeAt count 1) ⟨index, hindex⟩).symm

theorem emitPredecessorHeadConnectors_effect_internal
    (values : BinaryValues WorkCount)
    (hloop₁ : values Work.loop₁ = 0)
    (hreference₀ : values Work.reference₀ = 0)
    (hreference₁ : values Work.reference₁ = 0) :
    (BinaryRoutine.binaryFor emitPredecessorHeadConnector Work.loop₀
      Work.limit₀).effect values =
      Function.update
        (Function.update
          (Function.update values Work.available
            (values Work.available +
              (values Work.limit₀ - values Work.loop₀))) Work.temporary₃
          (values Work.temporary₃ +
            2 * (values Work.limit₀ - values Work.loop₀))) Work.loop₀
        (values Work.loop₀ +
          (values Work.limit₀ - values Work.loop₀)) :=
  emitPredecessorHeadConnector_binaryForValues values hloop₁ hreference₀
    hreference₁ (values Work.limit₀ - values Work.loop₀)

theorem emitPredecessorHeadConnectors_emitted_internal
    (values : BinaryValues WorkCount) (available count : ℕ)
    (hloop₀ : values Work.loop₀ = 0)
    (hlimit : values Work.limit₀ = count)
    (hloop₁ : values Work.loop₁ = 0)
    (hreference₀ : values Work.reference₀ = 0)
    (hreference₁ : values Work.reference₁ = 0)
    (havailable : values Work.available = available + count + 1)
    (htemporary : values Work.temporary₃ = 2) :
    (BinaryRoutine.binaryFor emitPredecessorHeadConnector Work.loop₀
      Work.limit₀).emitted values =
      (indexedRightFoldConnectors .or available count
        (fixedWidthSizeAt count 1)).flatMap CircuitCode.RawGate.encode := by
  change BinaryRoutine.binaryForEmitted emitPredecessorHeadConnector
      Work.loop₀ values (values Work.limit₀ - values Work.loop₀) = _
  rw [hlimit, hloop₀, Nat.sub_zero,
    emitPredecessorHeadConnector_binaryForEmitted values hloop₁ hreference₀
      hreference₁]
  rw [havailable, htemporary]
  have hblocks := predecessorConnectorBlocks_eq available count
  simpa only [hblocks]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
theorem emitPredecessorHeadFormula_effect_internal
    (stateCount directionCode : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitPredecessorHeadFormula stateCount directionCode).effect values =
      Function.update values Work.available
        (values Work.available +
          movedHeadPredecessorSize (values Work.horizon)) := by
  let afterMembers :=
    (emitPredecessorHeadMembers stateCount directionCode).effect values
  let afterIdentity := (emitConstantGate false).effect afterMembers
  let afterLimit := setPredecessorHorizonLimit.effect afterIdentity
  let afterTemporary :=
    (BinaryRoutine.set Work.temporary₃ 2).effect afterLimit
  let afterConnectors :=
    (BinaryRoutine.binaryFor emitPredecessorHeadConnector Work.loop₀
      Work.limit₀).effect afterTemporary
  have hafterMembers : afterMembers =
      Function.update
        (Function.update values Work.available
          (values Work.available + (values Work.horizon + 1)))
        Work.limit₀ (values Work.horizon + 1) :=
    emitPredecessorHeadMembers_effect_internal stateCount directionCode values
      hclean hhorizon htarget
  have hafterIdentity : afterIdentity =
      Function.update afterMembers Work.available
        (afterMembers Work.available + 1) :=
    emitConstantFalse_effect afterMembers
  have hafterLimit : afterLimit =
      Function.update afterIdentity Work.limit₀
        (afterIdentity Work.horizon + 1) :=
    setPredecessorHorizonLimit_effect_internal afterIdentity
  have hafterTemporary : afterTemporary =
      Function.update afterLimit Work.temporary₃ 2 := by
    funext i
    simp [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
      BinaryRoutine.addConst]
  have hloop₁Temporary : afterTemporary Work.loop₁ = 0 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simpa [Work.horizon, Work.available, Work.limit₀, Work.loop₁,
      Work.temporary₃] using hclean.loop₁
  have href₀Temporary : afterTemporary Work.reference₀ = 0 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simpa [Work.horizon, Work.available, Work.limit₀, Work.reference₀,
      Work.temporary₃] using hclean.reference₀
  have href₁Temporary : afterTemporary Work.reference₁ = 0 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simpa [Work.horizon, Work.available, Work.limit₀, Work.reference₁,
      Work.temporary₃] using hclean.reference₁
  have hafterConnectors : afterConnectors =
      Function.update
        (Function.update
          (Function.update afterTemporary Work.available
            (afterTemporary Work.available +
              (afterTemporary Work.limit₀ - afterTemporary Work.loop₀)))
          Work.temporary₃
            (afterTemporary Work.temporary₃ +
              2 * (afterTemporary Work.limit₀ -
                afterTemporary Work.loop₀))) Work.loop₀
        (afterTemporary Work.loop₀ +
          (afterTemporary Work.limit₀ - afterTemporary Work.loop₀)) :=
    emitPredecessorHeadConnectors_effect_internal afterTemporary
      hloop₁Temporary href₀Temporary href₁Temporary
  rw [emitPredecessorHeadFormula]
  change (BinaryRoutine.clear Work.temporary₃).effect
      ((BinaryRoutine.clear Work.limit₀).effect
        ((BinaryRoutine.clear Work.loop₀).effect afterConnectors)) = _
  rw [show (BinaryRoutine.clear Work.loop₀).effect afterConnectors =
      Function.update afterConnectors Work.loop₀ 0 by rfl,
    show (BinaryRoutine.clear Work.limit₀).effect
        (Function.update afterConnectors Work.loop₀ 0) =
      Function.update (Function.update afterConnectors Work.loop₀ 0)
        Work.limit₀ 0 by rfl,
    show (BinaryRoutine.clear Work.temporary₃).effect
        (Function.update (Function.update afterConnectors Work.loop₀ 0)
          Work.limit₀ 0) =
      Function.update
        (Function.update (Function.update afterConnectors Work.loop₀ 0)
          Work.limit₀ 0) Work.temporary₃ 0 by rfl,
    hafterConnectors, hafterTemporary, hafterLimit, hafterIdentity,
    hafterMembers]
  have hloop' : values 14 = 0 := by
    simpa [Work.loop₀] using hclean.loop₀
  have hlimit' : values 15 = 0 := by
    simpa [Work.limit₀] using hclean.limit₀
  have htemporary' : values 25 = 0 := by
    simpa [Work.temporary₃] using hclean.temporary₃
  funext i
  simp only [Work.horizon, Work.available, Work.loop₀, Work.limit₀,
    Work.temporary₃, Function.update_apply]
  split_ifs
  all_goals (try simp_all [movedHeadPredecessorSize])
  all_goals omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
theorem emitPredecessorHeadFormula_emitted_internal
    (stateCount directionCode : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitPredecessorHeadFormula stateCount directionCode).emitted values =
      (predecessorHeadFormulaSchedule stateCount (values Work.horizon)
        (values Work.configBase) (values Work.available)
        (values Work.tapeIndex) (values Work.position)
        directionCode).flatMap CircuitCode.RawGate.encode := by
  let afterMembers :=
    (emitPredecessorHeadMembers stateCount directionCode).effect values
  let afterIdentity := (emitConstantGate false).effect afterMembers
  let afterLimit := setPredecessorHorizonLimit.effect afterIdentity
  let afterTemporary :=
    (BinaryRoutine.set Work.temporary₃ 2).effect afterLimit
  have hafterMembers : afterMembers =
      Function.update
        (Function.update values Work.available
          (values Work.available + (values Work.horizon + 1)))
        Work.limit₀ (values Work.horizon + 1) :=
    emitPredecessorHeadMembers_effect_internal stateCount directionCode values
      hclean hhorizon htarget
  have hafterIdentity : afterIdentity =
      Function.update afterMembers Work.available
        (afterMembers Work.available + 1) :=
    emitConstantFalse_effect afterMembers
  have hafterLimit : afterLimit =
      Function.update afterIdentity Work.limit₀
        (afterIdentity Work.horizon + 1) :=
    setPredecessorHorizonLimit_effect_internal afterIdentity
  have hafterTemporary : afterTemporary =
      Function.update afterLimit Work.temporary₃ 2 := by
    funext i
    simp [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
      BinaryRoutine.addConst]
  have hrefMembers : afterMembers Work.reference₀ = 0 := by
    rw [hafterMembers]
    simpa [Work.available, Work.limit₀, Work.reference₀] using
      hclean.reference₀
  have hloop₀Temporary : afterTemporary Work.loop₀ = 0 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simpa [Work.horizon, Work.available, Work.loop₀, Work.limit₀,
      Work.temporary₃] using hclean.loop₀
  have hlimitTemporary :
      afterTemporary Work.limit₀ = values Work.horizon + 1 := by
    rw [hafterTemporary, hafterLimit]
    simp [Work.horizon, Work.limit₀, Work.temporary₃]
  have hloop₁Temporary : afterTemporary Work.loop₁ = 0 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simpa [Work.horizon, Work.available, Work.limit₀, Work.loop₁,
      Work.temporary₃] using hclean.loop₁
  have href₀Temporary : afterTemporary Work.reference₀ = 0 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simpa [Work.horizon, Work.available, Work.limit₀, Work.reference₀,
      Work.temporary₃] using hclean.reference₀
  have href₁Temporary : afterTemporary Work.reference₁ = 0 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simpa [Work.horizon, Work.available, Work.limit₀, Work.reference₁,
      Work.temporary₃] using hclean.reference₁
  have havailableTemporary : afterTemporary Work.available =
      values Work.available + (values Work.horizon + 1) + 1 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simp [Work.horizon, Work.available, Work.limit₀, Work.temporary₃]
  have htemporaryTemporary : afterTemporary Work.temporary₃ = 2 := by
    rw [hafterTemporary]
    simp
  rw [emitPredecessorHeadFormula]
  change (emitPredecessorHeadMembers stateCount directionCode).emitted values ++
      (emitConstantGate false).emitted afterMembers ++
      (BinaryRoutine.binaryFor emitPredecessorHeadConnector Work.loop₀
        Work.limit₀).emitted afterTemporary = _
  rw [emitPredecessorHeadMembers_emitted_internal stateCount directionCode
      values hclean hhorizon htarget,
    emitConstantFalse_emitted afterMembers hrefMembers,
    emitPredecessorHeadConnectors_emitted_internal afterTemporary
      (values Work.available) (values Work.horizon + 1) hloop₀Temporary
      hlimitTemporary hloop₁Temporary href₀Temporary href₁Temporary
      havailableTemporary htemporaryTemporary]
  simp [predecessorHeadFormulaSchedule, List.flatMap_append]

theorem setPredecessorHorizonLimit_requires_internal
    (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0) :
    setPredecessorHorizonLimit.requires values := by
  have hcopy' : values 10 = 0 := by
    simpa [Work.copyCounter] using hcopy
  simp [setPredecessorHorizonLimit, BinaryRoutine.seq,
    BinaryRoutine.binaryCopy, BinaryRoutine.addConst, hcopy', Work.horizon,
    Work.limit₀, Work.copyCounter]

theorem emitPredecessorFalseRange_requires_internal
    (values : BinaryValues WorkCount)
    (hle : values Work.loop₀ ≤ values Work.limit₀)
    (hemit : values Work.emitCounter = 0) :
    emitPredecessorFalseRange.requires values := by
  rw [emitPredecessorFalseRange, BinaryRoutine.seq]
  refine ⟨?_, trivial⟩
  change Work.loop₀ ≠ Work.limit₀ ∧
    values Work.loop₀ ≤ values Work.limit₀ ∧ _
  refine ⟨by decide, hle, ?_⟩
  intro count hcount
  let current := BinaryRoutine.binaryForValues (emitConstantGate false)
    Work.loop₀ values count
  have hcurrent := emitConstantFalse_binaryForValues values count
  have hemitCurrent : current Work.emitCounter = 0 := by
    change (BinaryRoutine.binaryForValues (emitConstantGate false)
      Work.loop₀ values count) Work.emitCounter = 0
    rw [hcurrent]
    simpa [Work.available, Work.loop₀, Work.emitCounter] using hemit
  constructor
  · change CircuitCode.Machine.RawGateStepDistinct Work.emitCounter
        Work.available Work.reference₀ Work.reference₀ ∧
      current Work.emitCounter = 0
    exact ⟨⟨by decide, by decide, by decide, by decide, by decide⟩,
      hemitCurrent⟩
  · rw [emitConstantFalse_effect]
    constructor <;> simp [Work.available, Work.loop₀, Work.limit₀]

theorem emitPredecessorHeadConnector_requires_internal
    (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0)
    (hloop₁ : values Work.loop₁ = 0)
    (hoffset : values Work.temporary₃ ≤ values Work.available)
    (havailable : 1 ≤ values Work.available)
    (hemit : values Work.emitCounter = 0) :
    emitPredecessorHeadConnector.requires values := by
  rw [emitPredecessorHeadConnector, BinaryRoutine.seq]
  refine ⟨?_, trivial⟩
  exact (emitDynamicRecentGate_requires .or false false Work.temporary₃
    Work.loop₁ 1 values).2
      ⟨predecessorConnectorDistinct, hcopy, hloop₁, hoffset, havailable,
        hemit⟩

private theorem emitPredecessorHeadConnectors_requires_internal
    (values : BinaryValues WorkCount)
    (hle : values Work.loop₀ ≤ values Work.limit₀)
    (hloop₁ : values Work.loop₁ = 0)
    (hreference₀ : values Work.reference₀ = 0)
    (hreference₁ : values Work.reference₁ = 0)
    (hcopy : values Work.copyCounter = 0)
    (hemit : values Work.emitCounter = 0)
    (havailable : 1 ≤ values Work.available)
    (hoffset : ∀ count,
      count < values Work.limit₀ - values Work.loop₀ →
        values Work.temporary₃ + 2 * count ≤
          values Work.available + count) :
    (BinaryRoutine.binaryFor emitPredecessorHeadConnector Work.loop₀
      Work.limit₀).requires values := by
  refine ⟨by decide, hle, ?_⟩
  intro count hcount
  let current :=
    BinaryRoutine.binaryForValues emitPredecessorHeadConnector Work.loop₀
      values count
  have hcurrent := emitPredecessorHeadConnector_binaryForValues values
    hloop₁ hreference₀ hreference₁ count
  have hloop₁Current : current Work.loop₁ = 0 := by
    change (BinaryRoutine.binaryForValues emitPredecessorHeadConnector
      Work.loop₀ values count) Work.loop₁ = 0
    rw [hcurrent]
    simpa [Work.available, Work.temporary₃, Work.loop₀, Work.loop₁]
      using hloop₁
  have hcopyCurrent : current Work.copyCounter = 0 := by
    change (BinaryRoutine.binaryForValues emitPredecessorHeadConnector
      Work.loop₀ values count) Work.copyCounter = 0
    rw [hcurrent]
    simpa [Work.available, Work.temporary₃, Work.loop₀,
      Work.copyCounter] using hcopy
  have hemitCurrent : current Work.emitCounter = 0 := by
    change (BinaryRoutine.binaryForValues emitPredecessorHeadConnector
      Work.loop₀ values count) Work.emitCounter = 0
    rw [hcurrent]
    simpa [Work.available, Work.temporary₃, Work.loop₀,
      Work.emitCounter] using hemit
  have havailableCurrent : 1 ≤ current Work.available := by
    change 1 ≤ (BinaryRoutine.binaryForValues emitPredecessorHeadConnector
      Work.loop₀ values count) Work.available
    rw [hcurrent]
    simp [Work.available, Work.temporary₃, Work.loop₀]
    omega
  have hoffsetCurrent : current Work.temporary₃ ≤ current Work.available := by
    change (BinaryRoutine.binaryForValues emitPredecessorHeadConnector
        Work.loop₀ values count) Work.temporary₃ ≤
      (BinaryRoutine.binaryForValues emitPredecessorHeadConnector
        Work.loop₀ values count) Work.available
    rw [hcurrent]
    simpa [Work.available, Work.temporary₃, Work.loop₀] using
      hoffset count hcount
  constructor
  · exact emitPredecessorHeadConnector_requires_internal current hcopyCurrent
      hloop₁Current hoffsetCurrent havailableCurrent hemitCurrent
  · rw [emitPredecessorHeadConnector_effect_internal current hloop₁Current]
    constructor
    · change current Work.loop₀ =
        (BinaryRoutine.binaryForValues emitPredecessorHeadConnector
          Work.loop₀ values count) Work.loop₀
      rfl
    · change current Work.limit₀ =
        (BinaryRoutine.binaryForValues emitPredecessorHeadConnector
          Work.loop₀ values count) Work.limit₀
      rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
theorem emitStayPredecessorMembers_requires_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitStayPredecessorMembers stateCount).requires values := by
  let afterLimit :=
    (BinaryRoutine.binaryCopy Work.position Work.limit₀
      Work.copyCounter).effect values
  let afterPrefix := emitPredecessorFalseRange.effect afterLimit
  let afterHead := (emitHeadReference stateCount).effect afterPrefix
  let afterLoopCopy :=
    (BinaryRoutine.binaryCopy Work.position Work.loop₀
      Work.copyCounter).effect afterHead
  let afterLoopSucc :=
    (BinaryRoutine.addConst Work.loop₀ 1).effect afterLoopCopy
  let afterHorizon := setPredecessorHorizonLimit.effect afterLoopSucc
  have hafterLimit : afterLimit =
      Function.update values Work.limit₀ (values Work.position) := rfl
  have hafterPrefix : afterPrefix =
      Function.update
        (Function.update afterLimit Work.available
          (afterLimit Work.available +
            (afterLimit Work.limit₀ - afterLimit Work.loop₀)))
        Work.loop₀ 0 :=
    emitPredecessorFalseRange_effect_internal afterLimit
  have hafterHead : afterHead =
      Function.update
        (Function.update
          (Function.update afterPrefix Work.temporary₀ 0) Work.available
            (afterPrefix Work.available + 1)) Work.reference₀ 0 :=
    emitHeadReference_effect stateCount false afterPrefix
  have hafterLoopCopy : afterLoopCopy =
      Function.update afterHead Work.loop₀ (afterHead Work.position) := rfl
  have hafterLoopSucc : afterLoopSucc =
      Function.update afterLoopCopy Work.loop₀
        (afterLoopCopy Work.loop₀ + 1) := rfl
  have hafterHorizon : afterHorizon =
      Function.update afterLoopSucc Work.limit₀
        (afterLoopSucc Work.horizon + 1) :=
    setPredecessorHorizonLimit_effect_internal afterLoopSucc
  have hloopLimit : afterLimit Work.loop₀ ≤ afterLimit Work.limit₀ := by
    rw [hafterLimit]
    have hloop' : values 14 = 0 := by
      simpa [Work.loop₀] using hclean.loop₀
    simp [hloop', Work.position, Work.loop₀, Work.limit₀]
  have hemitLimit : afterLimit Work.emitCounter = 0 := by
    rw [hafterLimit]
    simpa [Work.limit₀, Work.emitCounter] using hclean.emitCounter
  have haddPrefix : afterPrefix Work.addCounter = 0 := by
    rw [hafterPrefix, hafterLimit]
    simpa [Work.available, Work.loop₀, Work.limit₀, Work.addCounter] using
      hclean.addCounter
  have hmultiplyPrefix : afterPrefix Work.multiplyCounter = 0 := by
    rw [hafterPrefix, hafterLimit]
    simpa [Work.available, Work.loop₀, Work.limit₀,
      Work.multiplyCounter] using hclean.multiplyCounter
  have hemitPrefix : afterPrefix Work.emitCounter = 0 := by
    rw [hafterPrefix, hafterLimit]
    simpa [Work.available, Work.loop₀, Work.limit₀, Work.emitCounter] using
      hclean.emitCounter
  have hcopyHead : afterHead Work.copyCounter = 0 := by
    rw [hafterHead, hafterPrefix, hafterLimit]
    simpa [Work.available, Work.loop₀, Work.limit₀, Work.temporary₀,
      Work.reference₀, Work.copyCounter] using hclean.copyCounter
  have hcopyLoopSucc : afterLoopSucc Work.copyCounter = 0 := by
    rw [hafterLoopSucc, hafterLoopCopy]
    simpa [Work.loop₀, Work.copyCounter] using hcopyHead
  have hloopHorizon :
      afterHorizon Work.loop₀ ≤ afterHorizon Work.limit₀ := by
    rw [hafterHorizon, hafterLoopSucc, hafterLoopCopy, hafterHead,
      hafterPrefix, hafterLimit]
    have hloop' : values 14 = 0 := by
      simpa [Work.loop₀] using hclean.loop₀
    have htarget' : values 30 ≤ values 1 := by
      simpa [Work.position, Work.horizon] using htarget
    simp [hloop', Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₀, Work.reference₀]
    omega
  have hemitHorizon : afterHorizon Work.emitCounter = 0 := by
    rw [hafterHorizon, hafterLoopSucc, hafterLoopCopy, hafterHead,
      hafterPrefix, hafterLimit]
    simpa [Work.horizon, Work.available, Work.loop₀, Work.limit₀,
      Work.temporary₀, Work.reference₀, Work.emitCounter] using
      hclean.emitCounter
  rw [emitStayPredecessorMembers]
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  exact
    ⟨⟨by decide, by decide, by decide, hclean.copyCounter⟩,
      emitPredecessorFalseRange_requires_internal afterLimit hloopLimit
        hemitLimit,
      emitHeadReference_requires stateCount false afterPrefix haddPrefix
        hmultiplyPrefix hemitPrefix,
      ⟨by decide, by decide, by decide, hcopyHead⟩,
      trivial,
      setPredecessorHorizonLimit_requires_internal afterLoopSucc
        hcopyLoopSucc,
      emitPredecessorFalseRange_requires_internal afterHorizon hloopHorizon
        hemitHorizon,
      trivial⟩

theorem emitRightZeroPredecessorMembers_requires_internal
    (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values) :
    emitRightZeroPredecessorMembers.requires values := by
  let afterHorizon := setPredecessorHorizonLimit.effect values
  have hafterHorizon : afterHorizon =
      Function.update values Work.limit₀ (values Work.horizon + 1) :=
    setPredecessorHorizonLimit_effect_internal values
  have hle : afterHorizon Work.loop₀ ≤ afterHorizon Work.limit₀ := by
    rw [hafterHorizon]
    have hloop' : values 14 = 0 := by
      simpa [Work.loop₀] using hclean.loop₀
    simp [hloop', Work.horizon, Work.loop₀, Work.limit₀]
  have hemit : afterHorizon Work.emitCounter = 0 := by
    rw [hafterHorizon]
    simpa [Work.limit₀, Work.emitCounter] using hclean.emitCounter
  rw [emitRightZeroPredecessorMembers, BinaryRoutine.seq]
  exact ⟨setPredecessorHorizonLimit_requires_internal values
    hclean.copyCounter,
    emitPredecessorFalseRange_requires_internal afterHorizon hle hemit⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2400000 in
theorem emitRightPositivePredecessorMembers_requires_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hpositive : 0 < values Work.position)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitRightPositivePredecessorMembers stateCount).requires values := by
  let afterLimit :=
    (BinaryRoutine.binaryCopy Work.position Work.limit₀
      Work.copyCounter).effect values
  let afterLimitPred :=
    (BinaryRoutine.binaryPred Work.limit₀).effect afterLimit
  let afterPrefix := emitPredecessorFalseRange.effect afterLimitPred
  let afterPositionPred :=
    (BinaryRoutine.binaryPred Work.position).effect afterPrefix
  let afterHead := (emitHeadReference stateCount).effect afterPositionPred
  let afterPositionSucc :=
    (BinaryRoutine.addConst Work.position 1).effect afterHead
  let afterLoopCopy :=
    (BinaryRoutine.binaryCopy Work.position Work.loop₀
      Work.copyCounter).effect afterPositionSucc
  let afterHorizon := setPredecessorHorizonLimit.effect afterLoopCopy
  have hafterLimit : afterLimit =
      Function.update values Work.limit₀ (values Work.position) := rfl
  have hafterLimitPred : afterLimitPred =
      Function.update afterLimit Work.limit₀
        (afterLimit Work.limit₀ - 1) := rfl
  have hafterPrefix : afterPrefix =
      Function.update
        (Function.update afterLimitPred Work.available
          (afterLimitPred Work.available +
            (afterLimitPred Work.limit₀ - afterLimitPred Work.loop₀)))
        Work.loop₀ 0 :=
    emitPredecessorFalseRange_effect_internal afterLimitPred
  have hafterPositionPred : afterPositionPred =
      Function.update afterPrefix Work.position
        (afterPrefix Work.position - 1) := rfl
  have hafterHead : afterHead =
      Function.update
        (Function.update
          (Function.update afterPositionPred Work.temporary₀ 0)
            Work.available (afterPositionPred Work.available + 1))
        Work.reference₀ 0 :=
    emitHeadReference_effect stateCount false afterPositionPred
  have hafterPositionSucc : afterPositionSucc =
      Function.update afterHead Work.position
        (afterHead Work.position + 1) := rfl
  have hafterLoopCopy : afterLoopCopy =
      Function.update afterPositionSucc Work.loop₀
        (afterPositionSucc Work.position) := rfl
  have hafterHorizon : afterHorizon =
      Function.update afterLoopCopy Work.limit₀
        (afterLoopCopy Work.horizon + 1) :=
    setPredecessorHorizonLimit_effect_internal afterLoopCopy
  have hlimitPositive : 0 < afterLimit Work.limit₀ := by
    rw [hafterLimit]
    simpa [Work.position, Work.limit₀] using hpositive
  have hprefixLe :
      afterLimitPred Work.loop₀ ≤ afterLimitPred Work.limit₀ := by
    rw [hafterLimitPred, hafterLimit]
    have hloop' : values 14 = 0 := by
      simpa [Work.loop₀] using hclean.loop₀
    simp [hloop', Work.position, Work.loop₀, Work.limit₀]
  have hemitLimitPred : afterLimitPred Work.emitCounter = 0 := by
    rw [hafterLimitPred, hafterLimit]
    simpa [Work.limit₀, Work.emitCounter] using hclean.emitCounter
  have hpositionPositive : 0 < afterPrefix Work.position := by
    rw [hafterPrefix, hafterLimitPred, hafterLimit]
    simpa [Work.available, Work.position, Work.loop₀, Work.limit₀] using
      hpositive
  have haddPositionPred : afterPositionPred Work.addCounter = 0 := by
    rw [hafterPositionPred, hafterPrefix, hafterLimitPred, hafterLimit]
    simpa [Work.available, Work.position, Work.loop₀, Work.limit₀,
      Work.addCounter] using hclean.addCounter
  have hmultiplyPositionPred :
      afterPositionPred Work.multiplyCounter = 0 := by
    rw [hafterPositionPred, hafterPrefix, hafterLimitPred, hafterLimit]
    simpa [Work.available, Work.position, Work.loop₀, Work.limit₀,
      Work.multiplyCounter] using hclean.multiplyCounter
  have hemitPositionPred : afterPositionPred Work.emitCounter = 0 := by
    rw [hafterPositionPred, hafterPrefix, hafterLimitPred, hafterLimit]
    simpa [Work.available, Work.position, Work.loop₀, Work.limit₀,
      Work.emitCounter] using hclean.emitCounter
  have hcopyPositionSucc : afterPositionSucc Work.copyCounter = 0 := by
    rw [hafterPositionSucc, hafterHead, hafterPositionPred, hafterPrefix,
      hafterLimitPred, hafterLimit]
    simpa [Work.available, Work.position, Work.loop₀, Work.limit₀,
      Work.temporary₀, Work.reference₀, Work.copyCounter] using
      hclean.copyCounter
  have hcopyLoopCopy : afterLoopCopy Work.copyCounter = 0 := by
    rw [hafterLoopCopy]
    simpa [Work.loop₀, Work.copyCounter] using hcopyPositionSucc
  have hsuffixLe :
      afterHorizon Work.loop₀ ≤ afterHorizon Work.limit₀ := by
    rw [hafterHorizon, hafterLoopCopy, hafterPositionSucc, hafterHead,
      hafterPositionPred, hafterPrefix, hafterLimitPred, hafterLimit]
    have hloop' : values 14 = 0 := by
      simpa [Work.loop₀] using hclean.loop₀
    have hpositive' : 0 < values 30 := by
      simpa [Work.position] using hpositive
    have htarget' : values 30 ≤ values 1 := by
      simpa [Work.position, Work.horizon] using htarget
    simp [hloop', Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₀, Work.reference₀]
    omega
  have hemitHorizon : afterHorizon Work.emitCounter = 0 := by
    rw [hafterHorizon, hafterLoopCopy, hafterPositionSucc, hafterHead,
      hafterPositionPred, hafterPrefix, hafterLimitPred, hafterLimit]
    simpa [Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₀, Work.reference₀, Work.emitCounter] using
      hclean.emitCounter
  rw [emitRightPositivePredecessorMembers]
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  exact
    ⟨⟨by decide, by decide, by decide, hclean.copyCounter⟩,
      hlimitPositive,
      emitPredecessorFalseRange_requires_internal afterLimitPred hprefixLe
        hemitLimitPred,
      hpositionPositive,
      emitHeadReference_requires stateCount false afterPositionPred
        haddPositionPred hmultiplyPositionPred hemitPositionPred,
      trivial,
      ⟨by decide, by decide, by decide, hcopyPositionSucc⟩,
      setPredecessorHorizonLimit_requires_internal afterLoopCopy
        hcopyLoopCopy,
      emitPredecessorFalseRange_requires_internal afterHorizon hsuffixLe
        hemitHorizon,
      trivial⟩

theorem emitRightPredecessorMembers_requires_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitRightPredecessorMembers stateCount).requires values := by
  by_cases hzero : values Work.position = 0
  · rw [emitRightPredecessorMembers]
    simp only [BinaryRoutine.branchZero, hzero, ↓reduceIte]
    exact emitRightZeroPredecessorMembers_requires_internal values hclean
  · rw [emitRightPredecessorMembers]
    simp only [BinaryRoutine.branchZero, hzero, ↓reduceIte]
    exact emitRightPositivePredecessorMembers_requires_internal stateCount
      values hclean (Nat.pos_of_ne_zero hzero) htarget

theorem preparePredecessorHorizonGap_requires_internal
    (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0)
    (hloop : values Work.loop₀ = 0)
    (htarget : values Work.position ≤ values Work.horizon) :
    preparePredecessorHorizonGap.requires values := by
  let afterCopy :=
    (BinaryRoutine.binaryCopy Work.horizon Work.temporary₃
      Work.copyCounter).effect values
  have hafterCopy : afterCopy =
      Function.update values Work.temporary₃ (values Work.horizon) := rfl
  rw [preparePredecessorHorizonGap, BinaryRoutine.seq]
  refine ⟨⟨by decide, by decide, by decide, hcopy⟩, ?_⟩
  apply (decrementReferenceBy_requires Work.temporary₃ Work.position
    Work.loop₀ afterCopy).2
  constructor
  · exact predecessorGapDistinct
  constructor
  · rw [hafterCopy]
    simpa [Work.temporary₃, Work.loop₀] using hloop
  · rw [hafterCopy]
    simpa [Work.horizon, Work.position, Work.temporary₃] using htarget

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
theorem emitLeftZeroPredecessorMembers_requires_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hposition : values Work.position = 0)
    (hhorizon : 0 < values Work.horizon) :
    (emitLeftZeroPredecessorMembers stateCount).requires values := by
  let afterHead₀ := (emitHeadReference stateCount).effect values
  let afterPositionSucc :=
    (BinaryRoutine.addConst Work.position 1).effect afterHead₀
  let afterHead₁ :=
    (emitHeadReference stateCount).effect afterPositionSucc
  let afterPositionPred :=
    (BinaryRoutine.binaryPred Work.position).effect afterHead₁
  let afterLoop := (BinaryRoutine.set Work.loop₀ 2).effect afterPositionPred
  let afterHorizon := setPredecessorHorizonLimit.effect afterLoop
  have hafterHead₀ : afterHead₀ =
      Function.update
        (Function.update
          (Function.update values Work.temporary₀ 0) Work.available
            (values Work.available + 1)) Work.reference₀ 0 :=
    emitHeadReference_effect stateCount false values
  have hafterPositionSucc : afterPositionSucc =
      Function.update afterHead₀ Work.position
        (afterHead₀ Work.position + 1) := rfl
  have hafterHead₁ : afterHead₁ =
      Function.update
        (Function.update
          (Function.update afterPositionSucc Work.temporary₀ 0)
            Work.available (afterPositionSucc Work.available + 1))
        Work.reference₀ 0 :=
    emitHeadReference_effect stateCount false afterPositionSucc
  have hafterPositionPred : afterPositionPred =
      Function.update afterHead₁ Work.position
        (afterHead₁ Work.position - 1) := rfl
  have hafterLoop : afterLoop =
      Function.update afterPositionPred Work.loop₀ 2 := rfl
  have hafterHorizon : afterHorizon =
      Function.update afterLoop Work.limit₀
        (afterLoop Work.horizon + 1) :=
    setPredecessorHorizonLimit_effect_internal afterLoop
  have haddPositionSucc : afterPositionSucc Work.addCounter = 0 := by
    rw [hafterPositionSucc, hafterHead₀]
    simpa [Work.available, Work.position, Work.temporary₀, Work.reference₀,
      Work.addCounter] using hclean.addCounter
  have hmultiplyPositionSucc :
      afterPositionSucc Work.multiplyCounter = 0 := by
    rw [hafterPositionSucc, hafterHead₀]
    simpa [Work.available, Work.position, Work.temporary₀, Work.reference₀,
      Work.multiplyCounter] using hclean.multiplyCounter
  have hemitPositionSucc : afterPositionSucc Work.emitCounter = 0 := by
    rw [hafterPositionSucc, hafterHead₀]
    simpa [Work.available, Work.position, Work.temporary₀, Work.reference₀,
      Work.emitCounter] using hclean.emitCounter
  have hpositionPositive : 0 < afterHead₁ Work.position := by
    rw [hafterHead₁, hafterPositionSucc, hafterHead₀]
    have hposition' : values 30 = 0 := by
      simpa [Work.position] using hposition
    simp [hposition', Work.available, Work.position, Work.temporary₀,
      Work.reference₀]
  have hcopyLoop : afterLoop Work.copyCounter = 0 := by
    rw [hafterLoop, hafterPositionPred, hafterHead₁, hafterPositionSucc,
      hafterHead₀]
    simpa [Work.available, Work.position, Work.loop₀, Work.temporary₀,
      Work.reference₀, Work.copyCounter] using hclean.copyCounter
  have hsuffixLe :
      afterHorizon Work.loop₀ ≤ afterHorizon Work.limit₀ := by
    rw [hafterHorizon, hafterLoop, hafterPositionPred, hafterHead₁,
      hafterPositionSucc, hafterHead₀]
    have hhorizon' : 0 < values 1 := by
      simpa [Work.horizon] using hhorizon
    simp [Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₀, Work.reference₀]
    omega
  have hemitHorizon : afterHorizon Work.emitCounter = 0 := by
    rw [hafterHorizon, hafterLoop, hafterPositionPred, hafterHead₁,
      hafterPositionSucc, hafterHead₀]
    simpa [Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₀, Work.reference₀, Work.emitCounter] using
      hclean.emitCounter
  rw [emitLeftZeroPredecessorMembers]
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  exact
    ⟨emitHeadReference_requires stateCount false values hclean.addCounter
        hclean.multiplyCounter hclean.emitCounter,
      trivial,
      emitHeadReference_requires stateCount false afterPositionSucc
        haddPositionSucc hmultiplyPositionSucc hemitPositionSucc,
      hpositionPositive,
      trivial,
      setPredecessorHorizonLimit_requires_internal afterLoop hcopyLoop,
      emitPredecessorFalseRange_requires_internal afterHorizon hsuffixLe
        hemitHorizon,
      trivial⟩

private theorem emitConstantFalseTemporaryFor_requires
    (values : BinaryValues WorkCount)
    (hle : values Work.loop₀ ≤ values Work.temporary₃)
    (hemit : values Work.emitCounter = 0) :
    (BinaryRoutine.binaryFor (emitConstantGate false) Work.loop₀
      Work.temporary₃).requires values := by
  change Work.loop₀ ≠ Work.temporary₃ ∧
    values Work.loop₀ ≤ values Work.temporary₃ ∧ _
  refine ⟨by decide, hle, ?_⟩
  intro count hcount
  let current := BinaryRoutine.binaryForValues (emitConstantGate false)
    Work.loop₀ values count
  have hcurrent := emitConstantFalse_binaryForValues values count
  have hemitCurrent : current Work.emitCounter = 0 := by
    rw [hcurrent]
    simpa [Work.available, Work.loop₀, Work.emitCounter] using hemit
  constructor
  · change CircuitCode.Machine.RawGateStepDistinct Work.emitCounter
        Work.available Work.reference₀ Work.reference₀ ∧
      current Work.emitCounter = 0
    exact ⟨⟨by decide, by decide, by decide, by decide, by decide⟩,
      hemitCurrent⟩
  · rw [emitConstantFalse_effect]
    constructor <;> simp [Work.available, Work.loop₀, Work.temporary₃]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
theorem emitLeftPositivePredecessorTail_requires_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hloop : values Work.loop₀ = 0)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0)
    (hemit : values Work.emitCounter = 0) :
    (emitLeftPositivePredecessorTail stateCount).requires values := by
  by_cases hgap : values Work.temporary₃ = 0
  · rw [emitLeftPositivePredecessorTail]
    simp [BinaryRoutine.branchZero, hgap, BinaryRoutine.clear]
  · let afterPositionSucc :=
      (BinaryRoutine.addConst Work.position 1).effect values
    let afterHead :=
      (emitHeadReference stateCount).effect afterPositionSucc
    let afterPositionPred :=
      (BinaryRoutine.binaryPred Work.position).effect afterHead
    let afterGapPred :=
      (BinaryRoutine.binaryPred Work.temporary₃).effect afterPositionPred
    have hafterPositionSucc : afterPositionSucc =
        Function.update values Work.position
          (values Work.position + 1) := rfl
    have hafterHead : afterHead =
        Function.update
          (Function.update
            (Function.update afterPositionSucc Work.temporary₀ 0)
              Work.available (afterPositionSucc Work.available + 1))
          Work.reference₀ 0 :=
      emitHeadReference_effect stateCount false afterPositionSucc
    have hafterPositionPred : afterPositionPred =
        Function.update afterHead Work.position
          (afterHead Work.position - 1) := rfl
    have hafterGapPred : afterGapPred =
        Function.update afterPositionPred Work.temporary₃
          (afterPositionPred Work.temporary₃ - 1) := rfl
    have haddPositionSucc : afterPositionSucc Work.addCounter = 0 := by
      rw [hafterPositionSucc]
      simpa [Work.position, Work.addCounter] using hadd
    have hmultiplyPositionSucc :
        afterPositionSucc Work.multiplyCounter = 0 := by
      rw [hafterPositionSucc]
      simpa [Work.position, Work.multiplyCounter] using hmultiply
    have hemitPositionSucc : afterPositionSucc Work.emitCounter = 0 := by
      rw [hafterPositionSucc]
      simpa [Work.position, Work.emitCounter] using hemit
    have hpositionPositive : 0 < afterHead Work.position := by
      rw [hafterHead, hafterPositionSucc]
      simp [Work.available, Work.position, Work.temporary₀, Work.reference₀]
    have hgapPositive : 0 < afterPositionPred Work.temporary₃ := by
      rw [hafterPositionPred, hafterHead, hafterPositionSucc]
      have hgap' : values 25 ≠ 0 := by
        simpa [Work.temporary₃] using hgap
      simp [Work.available, Work.position, Work.temporary₀,
        Work.temporary₃, Work.reference₀]
      omega
    have hloopGapPred :
        afterGapPred Work.loop₀ ≤ afterGapPred Work.temporary₃ := by
      rw [hafterGapPred, hafterPositionPred, hafterHead,
        hafterPositionSucc]
      have hloop' : values 14 = 0 := by
        simpa [Work.loop₀] using hloop
      simp [hloop', Work.available, Work.position, Work.loop₀,
        Work.temporary₀, Work.temporary₃, Work.reference₀]
    have hemitGapPred : afterGapPred Work.emitCounter = 0 := by
      rw [hafterGapPred, hafterPositionPred, hafterHead,
        hafterPositionSucc]
      simpa [Work.available, Work.position, Work.temporary₀,
        Work.temporary₃, Work.reference₀, Work.emitCounter] using hemit
    rw [emitLeftPositivePredecessorTail]
    simp only [BinaryRoutine.branchZero, hgap, ↓reduceIte,
      BinaryRoutine.seqList, BinaryRoutine.seq, BinaryRoutine.identity,
      BinaryRoutine.emitBits]
    exact
      ⟨trivial,
        emitHeadReference_requires stateCount false afterPositionSucc
          haddPositionSucc hmultiplyPositionSucc hemitPositionSucc,
        hpositionPositive,
        hgapPositive,
        emitConstantFalseTemporaryFor_requires afterGapPred hloopGapPred
          hemitGapPred,
        trivial, trivial, trivial⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem emitLeftPositivePredecessorMembers_requires_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitLeftPositivePredecessorMembers stateCount).requires values := by
  let afterLimit :=
    (BinaryRoutine.binaryCopy Work.position Work.limit₀
      Work.copyCounter).effect values
  let afterLimitSucc :=
    (BinaryRoutine.addConst Work.limit₀ 1).effect afterLimit
  let afterPrefix := emitPredecessorFalseRange.effect afterLimitSucc
  let afterGap := preparePredecessorHorizonGap.effect afterPrefix
  let afterTail :=
    (emitLeftPositivePredecessorTail stateCount).effect afterGap
  have hafterLimit : afterLimit =
      Function.update values Work.limit₀ (values Work.position) := rfl
  have hafterLimitSucc : afterLimitSucc =
      Function.update afterLimit Work.limit₀
        (afterLimit Work.limit₀ + 1) := rfl
  have hafterPrefix : afterPrefix =
      Function.update
        (Function.update afterLimitSucc Work.available
          (afterLimitSucc Work.available +
            (afterLimitSucc Work.limit₀ - afterLimitSucc Work.loop₀)))
        Work.loop₀ 0 :=
    emitPredecessorFalseRange_effect_internal afterLimitSucc
  have hloopPrefix : afterPrefix Work.loop₀ = 0 := by
    rw [hafterPrefix]
    simp
  have hafterGap : afterGap =
      Function.update
        (Function.update afterPrefix Work.temporary₃
          (afterPrefix Work.horizon - afterPrefix Work.position))
        Work.loop₀ 0 :=
    preparePredecessorHorizonGap_effect_internal afterPrefix hloopPrefix
  have hprefixLe :
      afterLimitSucc Work.loop₀ ≤ afterLimitSucc Work.limit₀ := by
    rw [hafterLimitSucc, hafterLimit]
    have hloop' : values 14 = 0 := by
      simpa [Work.loop₀] using hclean.loop₀
    simp [hloop', Work.position, Work.loop₀, Work.limit₀]
  have hemitLimitSucc : afterLimitSucc Work.emitCounter = 0 := by
    rw [hafterLimitSucc, hafterLimit]
    simpa [Work.limit₀, Work.emitCounter] using hclean.emitCounter
  have hcopyPrefix : afterPrefix Work.copyCounter = 0 := by
    rw [hafterPrefix, hafterLimitSucc, hafterLimit]
    simpa [Work.available, Work.loop₀, Work.limit₀, Work.copyCounter] using
      hclean.copyCounter
  have htargetPrefix :
      afterPrefix Work.position ≤ afterPrefix Work.horizon := by
    rw [hafterPrefix, hafterLimitSucc, hafterLimit]
    simpa [Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀] using htarget
  have hloopGap : afterGap Work.loop₀ = 0 := by
    rw [hafterGap]
    simp
  have haddGap : afterGap Work.addCounter = 0 := by
    rw [hafterGap, hafterPrefix, hafterLimitSucc, hafterLimit]
    simpa [Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₃, Work.addCounter] using hclean.addCounter
  have hmultiplyGap : afterGap Work.multiplyCounter = 0 := by
    rw [hafterGap, hafterPrefix, hafterLimitSucc, hafterLimit]
    simpa [Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₃, Work.multiplyCounter] using
      hclean.multiplyCounter
  have hemitGap : afterGap Work.emitCounter = 0 := by
    rw [hafterGap, hafterPrefix, hafterLimitSucc, hafterLimit]
    simpa [Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₃, Work.emitCounter] using
      hclean.emitCounter
  have htemporaryGap : afterGap Work.temporary₀ = 0 := by
    rw [hafterGap, hafterPrefix, hafterLimitSucc, hafterLimit]
    simpa [Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₀, Work.temporary₃] using hclean.temporary₀
  have hreferenceGap : afterGap Work.reference₀ = 0 := by
    rw [hafterGap, hafterPrefix, hafterLimitSucc, hafterLimit]
    simpa [Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.reference₀, Work.temporary₃] using hclean.reference₀
  have hafterTail : afterTail =
      Function.update
        (Function.update afterGap Work.available
          (afterGap Work.available + afterGap Work.temporary₃))
        Work.temporary₃ 0 :=
    emitLeftPositivePredecessorTail_effect_internal stateCount afterGap
      hloopGap htemporaryGap hreferenceGap
  have hcopyTail : afterTail Work.copyCounter = 0 := by
    rw [hafterTail, hafterGap, hafterPrefix, hafterLimitSucc, hafterLimit]
    simpa [Work.horizon, Work.available, Work.position, Work.loop₀,
      Work.limit₀, Work.temporary₃, Work.copyCounter] using hclean.copyCounter
  rw [emitLeftPositivePredecessorMembers]
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  exact
    ⟨⟨by decide, by decide, by decide, hclean.copyCounter⟩,
      trivial,
      emitPredecessorFalseRange_requires_internal afterLimitSucc hprefixLe
        hemitLimitSucc,
      preparePredecessorHorizonGap_requires_internal afterPrefix hcopyPrefix
        hloopPrefix htargetPrefix,
      emitLeftPositivePredecessorTail_requires_internal stateCount afterGap
        hloopGap haddGap hmultiplyGap hemitGap,
      setPredecessorHorizonLimit_requires_internal afterTail hcopyTail,
      trivial⟩

theorem emitLeftPredecessorMembers_requires_internal
    (stateCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitLeftPredecessorMembers stateCount).requires values := by
  by_cases hzero : values Work.position = 0
  · rw [emitLeftPredecessorMembers]
    simp only [BinaryRoutine.branchZero, hzero, ↓reduceIte]
    exact emitLeftZeroPredecessorMembers_requires_internal stateCount values
      hclean hzero hhorizon
  · rw [emitLeftPredecessorMembers]
    simp only [BinaryRoutine.branchZero, hzero, ↓reduceIte]
    exact emitLeftPositivePredecessorMembers_requires_internal stateCount
      values hclean htarget

theorem emitPredecessorHeadMembers_requires_internal
    (stateCount directionCode : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitPredecessorHeadMembers stateCount directionCode).requires values := by
  by_cases hleft : directionCode = 0
  · simp only [emitPredecessorHeadMembers, hleft, ↓reduceIte]
    exact emitLeftPredecessorMembers_requires_internal stateCount values
      hclean hhorizon htarget
  · by_cases hright : directionCode = 1
    · simp only [emitPredecessorHeadMembers, hleft, hright, ↓reduceIte]
      exact emitRightPredecessorMembers_requires_internal stateCount values
        hclean htarget
    · simp only [emitPredecessorHeadMembers, hleft, hright, ↓reduceIte]
      exact emitStayPredecessorMembers_requires_internal stateCount values
        hclean htarget

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2400000 in
private theorem predecessorHeadRoutine_requires
    (stateCount directionCode : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (BinaryRoutine.seqList
      [emitPredecessorHeadMembers stateCount directionCode,
        emitConstantGate false,
        setPredecessorHorizonLimit,
        BinaryRoutine.set Work.temporary₃ 2,
        BinaryRoutine.binaryFor emitPredecessorHeadConnector Work.loop₀
          Work.limit₀,
        BinaryRoutine.clear Work.loop₀,
        BinaryRoutine.clear Work.limit₀,
        BinaryRoutine.clear Work.temporary₃]).requires values := by
  let afterMembers :=
    (emitPredecessorHeadMembers stateCount directionCode).effect values
  let afterIdentity := (emitConstantGate false).effect afterMembers
  let afterLimit := setPredecessorHorizonLimit.effect afterIdentity
  let afterTemporary :=
    (BinaryRoutine.set Work.temporary₃ 2).effect afterLimit
  have hafterMembers : afterMembers =
      Function.update
        (Function.update values Work.available
          (values Work.available + (values Work.horizon + 1)))
        Work.limit₀ (values Work.horizon + 1) :=
    emitPredecessorHeadMembers_effect_internal stateCount directionCode values
      hclean hhorizon htarget
  have hafterIdentity : afterIdentity =
      Function.update afterMembers Work.available
        (afterMembers Work.available + 1) :=
    emitConstantFalse_effect afterMembers
  have hafterLimit : afterLimit =
      Function.update afterIdentity Work.limit₀
        (afterIdentity Work.horizon + 1) :=
    setPredecessorHorizonLimit_effect_internal afterIdentity
  have hafterTemporary : afterTemporary =
      Function.update afterLimit Work.temporary₃ 2 := rfl
  have hemitMembers : afterMembers Work.emitCounter = 0 := by
    rw [hafterMembers]
    simpa [Work.available, Work.limit₀, Work.emitCounter] using
      hclean.emitCounter
  have hconstant : (emitConstantGate false).requires afterMembers := by
    change CircuitCode.Machine.RawGateStepDistinct Work.emitCounter
        Work.available Work.reference₀ Work.reference₀ ∧
      afterMembers Work.emitCounter = 0
    exact ⟨⟨by decide, by decide, by decide, by decide, by decide⟩,
      hemitMembers⟩
  have hcopyIdentity : afterIdentity Work.copyCounter = 0 := by
    rw [hafterIdentity, hafterMembers]
    simpa [Work.available, Work.limit₀, Work.copyCounter] using
      hclean.copyCounter
  have hloop₀Temporary : afterTemporary Work.loop₀ = 0 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simpa [Work.horizon, Work.available, Work.loop₀, Work.limit₀,
      Work.temporary₃] using hclean.loop₀
  have hlimitTemporary :
      afterTemporary Work.limit₀ = values Work.horizon + 1 := by
    rw [hafterTemporary, hafterLimit]
    simp [Work.horizon, Work.limit₀, Work.temporary₃]
  have hloop₁Temporary : afterTemporary Work.loop₁ = 0 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simpa [Work.horizon, Work.available, Work.limit₀, Work.loop₁,
      Work.temporary₃] using hclean.loop₁
  have href₀Temporary : afterTemporary Work.reference₀ = 0 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simpa [Work.horizon, Work.available, Work.limit₀, Work.reference₀,
      Work.temporary₃] using hclean.reference₀
  have href₁Temporary : afterTemporary Work.reference₁ = 0 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simpa [Work.horizon, Work.available, Work.limit₀, Work.reference₁,
      Work.temporary₃] using hclean.reference₁
  have hcopyTemporary : afterTemporary Work.copyCounter = 0 := by
    rw [hafterTemporary, hafterLimit]
    simpa [Work.limit₀, Work.temporary₃, Work.copyCounter] using hcopyIdentity
  have hemitTemporary : afterTemporary Work.emitCounter = 0 := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simpa [Work.horizon, Work.available, Work.limit₀, Work.temporary₃,
      Work.emitCounter] using hclean.emitCounter
  have havailableTemporary : 1 ≤ afterTemporary Work.available := by
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    simp [Work.horizon, Work.available, Work.limit₀, Work.temporary₃]
  have hloopLe : afterTemporary Work.loop₀ ≤ afterTemporary Work.limit₀ := by
    rw [hloop₀Temporary, hlimitTemporary]
    omega
  have hoffset : ∀ count,
      count < afterTemporary Work.limit₀ - afterTemporary Work.loop₀ →
        afterTemporary Work.temporary₃ + 2 * count ≤
          afterTemporary Work.available + count := by
    intro count hcount
    rw [hafterTemporary, hafterLimit, hafterIdentity, hafterMembers]
    have hloop' : values 14 = 0 := by
      simpa [Work.loop₀] using hclean.loop₀
    simp only [Work.horizon, Work.available, Work.loop₀, Work.limit₀,
      Work.temporary₃, Function.update_apply]
    simp [hloop'] at hcount ⊢
    omega
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  exact
    ⟨emitPredecessorHeadMembers_requires_internal stateCount directionCode
        values hclean hhorizon htarget,
      hconstant,
      setPredecessorHorizonLimit_requires_internal afterIdentity
        hcopyIdentity,
      trivial,
      emitPredecessorHeadConnectors_requires_internal afterTemporary hloopLe
        hloop₁Temporary href₀Temporary href₁Temporary hcopyTemporary
        hemitTemporary havailableTemporary hoffset,
      trivial, trivial, trivial, trivial⟩

theorem emitPredecessorHeadFormula_requires_internal
    (stateCount directionCode : ℕ) (values : BinaryValues WorkCount) :
    (emitPredecessorHeadFormula stateCount directionCode).requires values ↔
      PredecessorHeadClean values ∧ 0 < values Work.horizon ∧
        values Work.position ≤ values Work.horizon := by
  rfl

private theorem predecessor_sound_with_stronger_requires
    (routine : BinaryRoutine WorkCount)
    (requires : BinaryValues WorkCount → Prop) (hsound : routine.Sound)
    (hrequires : ∀ values, requires values → routine.requires values) :
    ({ routine with requires := requires } : BinaryRoutine WorkCount).Sound := by
  refine
    { isTransducer := hsound.isTransducer
      hoareTimeSpace := ?_ }
  intro values inp₀ ys inputLength initialSpace hdomain hparked
    hinitialSpace hinputHead
  exact hsound.hoareTimeSpace values inp₀ ys inputLength initialSpace
    (hrequires values hdomain) hparked hinitialSpace hinputHead

theorem emitPredecessorHeadFormula_sound_internal
    (stateCount directionCode : ℕ) :
    (emitPredecessorHeadFormula stateCount directionCode).Sound := by
  let routine := BinaryRoutine.seqList
    [emitPredecessorHeadMembers stateCount directionCode,
      emitConstantGate false,
      setPredecessorHorizonLimit,
      BinaryRoutine.set Work.temporary₃ 2,
      BinaryRoutine.binaryFor emitPredecessorHeadConnector Work.loop₀
        Work.limit₀,
      BinaryRoutine.clear Work.loop₀,
      BinaryRoutine.clear Work.limit₀,
      BinaryRoutine.clear Work.temporary₃]
  have hroutine : routine.Sound := by
    apply BinaryRoutine.seqList_sound
    intro member hmember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
    rcases hmember with h | h | h | h | h | h | h | h
    · subst member
      exact emitPredecessorHeadMembers_sound_internal stateCount directionCode
    · subst member
      exact emitConstantGate_sound false
    · subst member
      exact setPredecessorHorizonLimit_sound_internal
    · subst member
      exact BinaryRoutine.set_sound Work.temporary₃ 2
    · subst member
      exact emitPredecessorHeadConnector_sound_internal.binaryFor Work.loop₀
        Work.limit₀
    all_goals
      subst member
      exact BinaryRoutine.clear_sound _
  have hrestricted := predecessor_sound_with_stronger_requires routine
    (fun values =>
      PredecessorHeadClean values ∧ 0 < values Work.horizon ∧
        values Work.position ≤ values Work.horizon) hroutine (by
          intro values hdomain
          exact predecessorHeadRoutine_requires stateCount directionCode
            values hdomain.1 hdomain.2.1 hdomain.2.2)
  simpa [emitPredecessorHeadFormula, routine] using hrestricted

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
