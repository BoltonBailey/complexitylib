/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Offset.Defs
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Primitive
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Control

/-!
# Dynamic recent-wire offsets -- proof internals
-/

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

private theorem sound_with_stronger_requires (routine : BinaryRoutine WorkCount)
    (requires : BinaryValues WorkCount → Prop) (hsound : routine.Sound)
    (hrequires : ∀ values, requires values → routine.requires values) :
    ({ routine with requires := requires } : BinaryRoutine WorkCount).Sound := by
  refine
    { isTransducer := hsound.isTransducer
      hoareTimeSpace := ?_ }
  intro values inp₀ ys inputLength initialSpace hdomain hparked hinitialSpace
    hinputHead
  exact hsound.hoareTimeSpace values inp₀ ys inputLength initialSpace
    (hrequires values hdomain) hparked hinitialSpace hinputHead

private theorem binaryForPredValues (reference counter : Fin WorkCount)
    (hreferenceCounter : reference ≠ counter) : ∀ values count,
    BinaryRoutine.binaryForValues (BinaryRoutine.binaryPred reference)
        counter values count =
      Function.update
        (Function.update values reference (values reference - count))
        counter (values counter + count) := by
  intro values count
  induction count with
  | zero =>
      simp [BinaryRoutine.binaryForValues]
  | succ count ih =>
      rw [BinaryRoutine.binaryForValues, BinaryRoutine.binaryForStep, ih]
      simp only [BinaryRoutine.binaryPred]
      funext i
      by_cases hiReference : i = reference
      · subst i
        simp [hreferenceCounter]
        omega
      · by_cases hiCounter : i = counter
        · subst i
          simp [hreferenceCounter]
          omega
        · simp [hiReference, hiCounter]

private theorem binaryForPredEmitted (reference counter : Fin WorkCount) :
    ∀ values count,
      BinaryRoutine.binaryForEmitted (BinaryRoutine.binaryPred reference)
        counter values count = [] := by
  intro values count
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [BinaryRoutine.binaryForEmitted, ih]
      rfl

private theorem binaryForPredRequires (reference offset counter : Fin WorkCount)
    (hcounterOffset : counter ≠ offset)
    (hreferenceCounter : reference ≠ counter)
    (hreferenceOffset : reference ≠ offset)
    (values : BinaryValues WorkCount) :
    (BinaryRoutine.binaryFor (BinaryRoutine.binaryPred reference) counter
        offset).requires values ↔
      values counter ≤ values offset ∧
        values offset - values counter ≤ values reference := by
  rw [BinaryRoutine.binaryFor]
  constructor
  · rintro ⟨_, hcounterLimit, hbody⟩
    refine ⟨hcounterLimit, ?_⟩
    let count := values offset - values counter
    by_cases hcount : count = 0
    · simp [count, hcount]
    · have hlast : count - 1 <
          BinaryRoutine.binaryForCount counter offset values := by
        simp only [BinaryRoutine.binaryForCount]
        omega
      have hrequired := (hbody (count - 1) hlast).1
      rw [binaryForPredValues reference counter hreferenceCounter] at hrequired
      simp only [BinaryRoutine.binaryPred, Function.update_apply] at hrequired
      simp [hreferenceCounter] at hrequired
      omega
  · rintro ⟨hcounterLimit, hreference⟩
    refine ⟨hcounterOffset, hcounterLimit, ?_⟩
    intro count hcount
    rw [binaryForPredValues reference counter hreferenceCounter]
    have hcountReference : count < values reference := by
      rw [BinaryRoutine.binaryForCount] at hcount
      omega
    constructor
    · simp [BinaryRoutine.binaryPred, hreferenceCounter, hcountReference]
    · constructor
      · simp [BinaryRoutine.binaryPred, hreferenceCounter,
          Ne.symm hreferenceCounter]
      · simp [BinaryRoutine.binaryPred, Ne.symm hreferenceOffset,
          Ne.symm hcounterOffset]

theorem decrementReferenceBy_requires_internal
    (reference offset counter : Fin WorkCount)
    (values : BinaryValues WorkCount) :
    (decrementReferenceBy reference offset counter).requires values ↔
      DecrementReferenceDistinct reference offset counter ∧
        values counter = 0 ∧ values offset ≤ values reference := by
  rfl

theorem decrementReferenceBy_effect_internal
    (reference offset counter : Fin WorkCount)
    (values : BinaryValues WorkCount)
    (hdistinct : DecrementReferenceDistinct reference offset counter)
    (hcounter : values counter = 0) :
    (decrementReferenceBy reference offset counter).effect values =
      Function.update
        (Function.update values reference
          (values reference - values offset)) counter 0 := by
  rw [decrementReferenceBy]
  change Function.update
      (BinaryRoutine.binaryForValues (BinaryRoutine.binaryPred reference)
        counter values (BinaryRoutine.binaryForCount counter offset values))
      counter 0 = _
  rw [binaryForPredValues reference counter hdistinct.reference_ne_counter]
  funext i
  simp only [BinaryRoutine.binaryForCount, Function.update_apply]
  split_ifs <;> simp_all

theorem decrementReferenceBy_emitted_internal
    (reference offset counter : Fin WorkCount)
    (values : BinaryValues WorkCount) :
    (decrementReferenceBy reference offset counter).emitted values = [] := by
  rw [decrementReferenceBy]
  change
    BinaryRoutine.binaryForEmitted (BinaryRoutine.binaryPred reference)
      counter values (BinaryRoutine.binaryForCount counter offset values) ++
        [] = []
  rw [binaryForPredEmitted]
  rfl

theorem decrementReferenceBy_sound_internal
    (reference offset counter : Fin WorkCount) :
    (decrementReferenceBy reference offset counter).Sound := by
  let loop := BinaryRoutine.binaryFor (BinaryRoutine.binaryPred reference)
    counter offset
  let routine := BinaryRoutine.seq loop (BinaryRoutine.clear counter)
  have hloop : loop.Sound :=
    (BinaryRoutine.binaryPred_sound reference).binaryFor counter offset
  have hroutine : routine.Sound :=
    hloop.seq (BinaryRoutine.clear_sound counter)
  refine
    { isTransducer := by
        simpa [decrementReferenceBy, routine, loop] using hroutine.isTransducer
      hoareTimeSpace := ?_ }
  intro values inp₀ ys inputLength initialSpace hrequires hparked
    hinitialSpace hinputHead
  apply hroutine.hoareTimeSpace values inp₀ ys inputLength initialSpace
    ?_ hparked hinitialSpace hinputHead
  change loop.requires values ∧ True
  refine ⟨?_, trivial⟩
  rcases hrequires with ⟨hdistinct, hcounter, hoffset⟩
  rw [show loop.requires values ↔
      values counter ≤ values offset ∧
        values offset - values counter ≤ values reference by
    exact binaryForPredRequires reference offset counter
      (Ne.symm hdistinct.offset_ne_counter)
      hdistinct.reference_ne_counter hdistinct.reference_ne_offset values]
  omega

theorem prepareDynamicRecentReference_requires_internal
    (reference offset counter : Fin WorkCount)
    (values : BinaryValues WorkCount) :
    (prepareDynamicRecentReference reference offset counter).requires values ↔
      DynamicRecentDistinct reference offset counter ∧
        values Work.copyCounter = 0 ∧ values counter = 0 ∧
        values offset ≤ values Work.available := by
  rfl

theorem prepareDynamicRecentReference_effect_internal
    (reference offset counter : Fin WorkCount)
    (values : BinaryValues WorkCount)
    (hdistinct : DynamicRecentDistinct reference offset counter)
    (hcounter : values counter = 0) :
    (prepareDynamicRecentReference reference offset counter).effect values =
      Function.update
        (Function.update values reference
          (values Work.available - values offset)) counter 0 := by
  rw [prepareDynamicRecentReference]
  change (decrementReferenceBy reference offset counter).effect
      (Function.update values reference (values Work.available)) = _
  rw [decrementReferenceBy_effect_internal reference offset counter
    (Function.update values reference (values Work.available))
    hdistinct.toDecrementReferenceDistinct]
  · simp only [Function.update_apply, if_pos]
    simp only [if_neg (Ne.symm hdistinct.reference_ne_offset)]
    rw [Function.update_idem]
  · simp [Ne.symm hdistinct.reference_ne_counter, hcounter]

theorem prepareDynamicRecentReference_emitted_internal
    (reference offset counter : Fin WorkCount)
    (values : BinaryValues WorkCount) :
    (prepareDynamicRecentReference reference offset counter).emitted values =
      [] := by
  rw [prepareDynamicRecentReference]
  change [] ++
      (decrementReferenceBy reference offset counter).emitted
        (Function.update values reference (values Work.available)) ++ [] = []
  rw [decrementReferenceBy_emitted_internal]
  rfl

theorem prepareDynamicRecentReference_sound_internal
    (reference offset counter : Fin WorkCount) :
    (prepareDynamicRecentReference reference offset counter).Sound := by
  let routine := BinaryRoutine.seqList
    [BinaryRoutine.binaryCopy Work.available reference Work.copyCounter,
      decrementReferenceBy reference offset counter]
  have hroutine : routine.Sound := by
    apply BinaryRoutine.seqList_sound
    intro member hmember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
    rcases hmember with hmember | hmember
    · subst member
      exact BinaryRoutine.binaryCopy_sound Work.available reference
        Work.copyCounter
    · subst member
      exact decrementReferenceBy_sound_internal reference offset counter
  apply sound_with_stronger_requires routine _ hroutine
  intro values hrequires
  rcases hrequires with ⟨hdistinct, hcopy, hcounter, hoffset⟩
  change
    (BinaryRoutine.binaryCopy Work.available reference
        Work.copyCounter).requires values ∧
      (decrementReferenceBy reference offset counter).requires
        (Function.update values reference (values Work.available)) ∧ True
  constructor
  · exact ⟨hdistinct.available_ne_reference,
      hdistinct.available_ne_copyCounter,
      hdistinct.reference_ne_copyCounter, hcopy⟩
  constructor
  · change
      DecrementReferenceDistinct reference offset counter ∧
        Function.update values reference (values Work.available) counter = 0 ∧
        Function.update values reference (values Work.available) offset ≤
          Function.update values reference (values Work.available) reference
    refine ⟨hdistinct.toDecrementReferenceDistinct, ?_, ?_⟩
    · simp [Ne.symm hdistinct.reference_ne_counter, hcounter]
    · simp [Ne.symm hdistinct.reference_ne_offset, hoffset]
  · trivial

theorem emitDynamicRecentGate_requires_internal (op : AndOrOp)
    (negated₀ negated₁ : Bool) (offset counter : Fin WorkCount)
    (fixedOffset₁ : ℕ) (values : BinaryValues WorkCount) :
    (emitDynamicRecentGate op negated₀ negated₁ offset counter
        fixedOffset₁).requires values ↔
      DynamicRecentGateDistinct offset counter ∧
        values Work.copyCounter = 0 ∧ values counter = 0 ∧
        values offset ≤ values Work.available ∧
        fixedOffset₁ ≤ values Work.available ∧
        values Work.emitCounter = 0 := by
  rfl

theorem emitDynamicRecentGate_effect_internal (op : AndOrOp)
    (negated₀ negated₁ : Bool) (offset counter : Fin WorkCount)
    (fixedOffset₁ : ℕ) (values : BinaryValues WorkCount)
    (hdistinct : DynamicRecentGateDistinct offset counter)
    (hcounter : values counter = 0) :
    (emitDynamicRecentGate op negated₀ negated₁ offset counter
        fixedOffset₁).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values counter 0) Work.available
              (values Work.available + 1)) Work.reference₀ 0)
        Work.reference₁ 0 := by
  simp only [emitDynamicRecentGate, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.emitRawGateStep, BinaryRoutine.clear,
    BinaryRoutine.identity, BinaryRoutine.emitBits, id_eq]
  rw [prepareDynamicRecentReference_effect_internal Work.reference₀ offset
    counter values hdistinct.toDynamicRecentDistinct hcounter]
  rw [prepareRecentReference_effect]
  funext i
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem emitDynamicRecentGate_emitted_internal (op : AndOrOp)
    (negated₀ negated₁ : Bool) (offset counter : Fin WorkCount)
    (fixedOffset₁ : ℕ) (values : BinaryValues WorkCount)
    (hdistinct : DynamicRecentGateDistinct offset counter)
    (hcounter : values counter = 0) :
    (emitDynamicRecentGate op negated₀ negated₁ offset counter
        fixedOffset₁).emitted values =
      CircuitCode.RawGate.encode
        { op := op
          input₀ := values Work.available - values offset
          input₁ := values Work.available - fixedOffset₁
          negated₀ := negated₀
          negated₁ := negated₁ } := by
  simp only [emitDynamicRecentGate, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.emitRawGateStep, BinaryRoutine.clear,
    BinaryRoutine.identity, BinaryRoutine.emitBits, id_eq]
  rw [prepareDynamicRecentReference_emitted_internal,
    prepareRecentReference_emitted,
    prepareDynamicRecentReference_effect_internal Work.reference₀ offset
      counter values hdistinct.toDynamicRecentDistinct hcounter,
    prepareRecentReference_effect]
  simp only [List.nil_append, List.append_nil, Function.update_apply]
  congr 1
  simp [hdistinct.reference_ne_counter,
    hdistinct.available_ne_counter, hdistinct.available_ne_reference,
    hdistinct.reference₀_ne_reference₁]

theorem emitDynamicRecentGate_sound_internal (op : AndOrOp)
    (negated₀ negated₁ : Bool) (offset counter : Fin WorkCount)
    (fixedOffset₁ : ℕ) :
    (emitDynamicRecentGate op negated₀ negated₁ offset counter
        fixedOffset₁).Sound := by
  let routine := BinaryRoutine.seqList
    [prepareDynamicRecentReference Work.reference₀ offset counter,
      prepareRecentReference Work.reference₁ fixedOffset₁,
      BinaryRoutine.emitRawGateStep op negated₀ negated₁
        Work.emitCounter Work.available Work.reference₀ Work.reference₁,
      BinaryRoutine.clear Work.reference₀,
      BinaryRoutine.clear Work.reference₁]
  have hroutine : routine.Sound := by
    apply BinaryRoutine.seqList_sound
    intro member hmember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
    rcases hmember with hmember | hmember | hmember | hmember | hmember
    · subst member
      exact prepareDynamicRecentReference_sound_internal Work.reference₀
        offset counter
    · subst member
      exact prepareRecentReference_sound Work.reference₁ fixedOffset₁
    · subst member
      exact BinaryRoutine.emitRawGateStep_sound op negated₀ negated₁
        Work.emitCounter Work.available Work.reference₀ Work.reference₁
    all_goals
      subst member
      exact BinaryRoutine.clear_sound _
  apply sound_with_stronger_requires routine _ hroutine
  intro values hrequires
  rcases hrequires with
    ⟨hdistinct, hcopy, hcounter, hoffset, hfixedOffset, hemit⟩
  simp only [routine, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.clear, BinaryRoutine.identity, BinaryRoutine.emitBits,
    and_true]
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨hdistinct.toDynamicRecentDistinct, hcopy, hcounter, hoffset⟩
  · apply (prepareRecentReference_requires Work.reference₁ fixedOffset₁
      _ (by decide) (by decide) (by decide)).2
    rw [prepareDynamicRecentReference_effect_internal Work.reference₀ offset
      counter values hdistinct.toDynamicRecentDistinct hcounter]
    constructor
    · simp [Ne.symm hdistinct.reference_ne_copyCounter,
        Ne.symm hdistinct.counter_ne_copyCounter, hcopy]
    · simp [hdistinct.available_ne_reference,
        hdistinct.available_ne_counter, hfixedOffset]
  · have hrawDistinct : CircuitCode.Machine.RawGateStepDistinct
        Work.emitCounter Work.available Work.reference₀ Work.reference₁ := by
      exact
        { emitCounter_ne_available := by decide
          emitCounter_ne_input₀ := by decide
          emitCounter_ne_input₁ := by decide
          available_ne_input₀ := by decide
          available_ne_input₁ := by decide }
    constructor
    · exact hrawDistinct
    · rw [prepareRecentReference_effect,
        prepareDynamicRecentReference_effect_internal Work.reference₀ offset
          counter values hdistinct.toDynamicRecentDistinct hcounter]
      simp [Ne.symm hdistinct.reference₁_ne_emitCounter,
        Ne.symm hdistinct.reference₀_ne_emitCounter,
        Ne.symm hdistinct.counter_ne_emitCounter, hemit]

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
