/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.PolynomialOffset
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.PackedCopy.Defs

/-!
# Delayed packed-formula copies -- proof internals
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

theorem emitPackedFormulaCopy_requires_internal
    (sizePolynomial : Polynomial ℕ) (values : BinaryValues WorkCount) :
    (emitPackedFormulaCopy sizePolynomial).requires values ↔
      values Work.temporary₃ = 0 ∧
        values Work.polynomialScratch = 0 ∧
        values Work.multiplyCounter = 0 ∧
        values Work.addCounter = 0 ∧
        values Work.copyCounter = 0 ∧
        values Work.emitCounter = 0 ∧
        0 < sizePolynomial.eval (values Work.horizon) := by
  rfl

theorem emitPackedFormulaCopy_effect_internal
    (sizePolynomial : Polynomial ℕ) (values : BinaryValues WorkCount) :
    (emitPackedFormulaCopy sizePolynomial).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.gateCount
              (values Work.gateCount +
                sizePolynomial.eval (values Work.horizon)))
            Work.available (values Work.available + 1)) Work.reference₀ 0)
        Work.temporary₃ 0 := by
  simp only [emitPackedFormulaCopy, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.add, BinaryRoutine.binaryCopy, BinaryRoutine.binaryPred,
    BinaryRoutine.emitRawGateStep, BinaryRoutine.clear,
    BinaryRoutine.identity, BinaryRoutine.emitBits, id_eq]
  rw [preparePolynomialOffset_effect]
  funext i
  simp only [Function.update_apply]
  split_ifs <;> simp_all [Work.gateCount, Work.available,
    Work.reference₀, Work.temporary₃]

theorem emitPackedFormulaCopy_emitted_internal
    (sizePolynomial : Polynomial ℕ) (values : BinaryValues WorkCount) :
    (emitPackedFormulaCopy sizePolynomial).emitted values =
      (CircuitCode.RawGate.copy
        (values Work.gateCount +
          sizePolynomial.eval (values Work.horizon) - 1)).encode := by
  simp only [emitPackedFormulaCopy, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.add, BinaryRoutine.binaryCopy, BinaryRoutine.binaryPred,
    BinaryRoutine.emitRawGateStep, BinaryRoutine.clear,
    BinaryRoutine.identity, BinaryRoutine.emitBits, List.nil_append,
    List.append_nil]
  rw [preparePolynomialOffset_emitted, preparePolynomialOffset_effect]
  simp [CircuitCode.RawGate.copy, Work.temporary₃, Work.gateCount,
    Work.reference₀]

theorem emitPackedFormulaCopy_sound_internal
    (sizePolynomial : Polynomial ℕ) :
    (emitPackedFormulaCopy sizePolynomial).Sound := by
  let routine := BinaryRoutine.seqList
    [preparePolynomialOffset sizePolynomial,
      BinaryRoutine.add Work.temporary₃ Work.gateCount Work.addCounter,
      BinaryRoutine.binaryCopy Work.gateCount Work.reference₀
        Work.copyCounter,
      BinaryRoutine.binaryPred Work.reference₀,
      BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
        Work.available Work.reference₀ Work.reference₀,
      BinaryRoutine.clear Work.reference₀,
      BinaryRoutine.clear Work.temporary₃]
  have hroutine : routine.Sound := by
    apply BinaryRoutine.seqList_sound
    intro member hmember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
    rcases hmember with hmember | hmember | hmember | hmember | hmember |
      hmember | hmember
    · subst member
      exact preparePolynomialOffset_sound sizePolynomial
    · subst member
      exact BinaryRoutine.add_sound Work.temporary₃ Work.gateCount
        Work.addCounter
    · subst member
      exact BinaryRoutine.binaryCopy_sound Work.gateCount Work.reference₀
        Work.copyCounter
    · subst member
      exact BinaryRoutine.binaryPred_sound Work.reference₀
    · subst member
      exact BinaryRoutine.emitRawGateStep_sound .and false false
        Work.emitCounter Work.available Work.reference₀ Work.reference₀
    all_goals
      subst member
      exact BinaryRoutine.clear_sound _
  apply sound_with_stronger_requires routine _ hroutine
  intro values hrequires
  rcases hrequires with
    ⟨htemporary, hscratch, hmultiply, hadd, hcopy, hemit, hpositive⟩
  simp only [routine, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.clear, BinaryRoutine.identity, BinaryRoutine.emitBits,
    and_true]
  rw [preparePolynomialOffset_requires,
    preparePolynomialOffset_effect]
  simp [BinaryRoutine.add, BinaryRoutine.binaryCopy,
    BinaryRoutine.binaryPred, BinaryRoutine.emitRawGateStep,
    Work.horizon, Work.temporary₃, Work.polynomialScratch,
    Work.multiplyCounter, Work.addCounter, Work.gateCount,
    Work.copyCounter, Work.reference₀, Work.emitCounter, Work.available]
  refine ⟨⟨htemporary, hscratch, hmultiply, hadd⟩, hadd, hcopy,
    Or.inr hpositive, ?_, hemit⟩
  exact
    { emitCounter_ne_available := by decide
      emitCounter_ne_input₀ := by decide
      emitCounter_ne_input₁ := by decide
      available_ne_input₀ := by decide
      available_ne_input₁ := by decide }

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
