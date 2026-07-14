/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Offset
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.PolynomialOffset.Defs

/-!
# Polynomial recent-wire offsets -- proof internals
-/

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

private theorem polynomialOffsetDistinct :
    DynamicRecentGateDistinct Work.temporary₃ Work.loop₃ := by
  apply DynamicRecentGateDistinct.mk
  · apply DynamicRecentDistinct.mk
    · exact ⟨by decide, by decide, by decide⟩
    all_goals decide
  all_goals decide

private theorem polynomialEvaluationDistinct :
    TM.BinaryPolynomialDistinct Work.horizon Work.temporary₃
      Work.polynomialScratch Work.multiplyCounter Work.addCounter := by
  constructor <;> decide

theorem preparePolynomialOffset_sound_internal (polynomial : Polynomial ℕ)
    (extra : ℕ) :
    (preparePolynomialOffset polynomial extra).Sound :=
  (BinaryRoutine.evalPolynomial_sound Work.horizon Work.temporary₃
    Work.polynomialScratch Work.multiplyCounter Work.addCounter
    polynomial).seq (BinaryRoutine.addConst_sound Work.temporary₃ extra)

theorem preparePolynomialOffset_requires_internal
    (polynomial : Polynomial ℕ) (extra : ℕ)
    (values : BinaryValues WorkCount) :
    (preparePolynomialOffset polynomial extra).requires values ↔
      values Work.temporary₃ = 0 ∧
        values Work.polynomialScratch = 0 ∧
        values Work.multiplyCounter = 0 ∧
        values Work.addCounter = 0 := by
  simp only [preparePolynomialOffset, BinaryRoutine.seq,
    BinaryRoutine.evalPolynomial, BinaryRoutine.addConst]
  simp only [polynomialEvaluationDistinct, true_and, and_true]

theorem preparePolynomialOffset_effect_internal
    (polynomial : Polynomial ℕ) (extra : ℕ)
    (values : BinaryValues WorkCount) :
    (preparePolynomialOffset polynomial extra).effect values =
      Function.update values Work.temporary₃
        (polynomial.eval (values Work.horizon) + extra) := by
  simp [preparePolynomialOffset, BinaryRoutine.seq,
    BinaryRoutine.evalPolynomial, BinaryRoutine.addConst]

theorem preparePolynomialOffset_emitted_internal
    (polynomial : Polynomial ℕ) (extra : ℕ)
    (values : BinaryValues WorkCount) :
    (preparePolynomialOffset polynomial extra).emitted values = [] := by
  simp [preparePolynomialOffset, BinaryRoutine.seq,
    BinaryRoutine.evalPolynomial, BinaryRoutine.addConst]

theorem emitPolynomialRecentGate_sound_internal
    (polynomial : Polynomial ℕ) (extra : ℕ) (op : AndOrOp)
    (negated₀ negated₁ : Bool) (fixedOffset₁ : ℕ) :
    (emitPolynomialRecentGate polynomial extra op negated₀ negated₁
        fixedOffset₁).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with hroutine | hroutine | hroutine
  · subst routine
    exact preparePolynomialOffset_sound_internal polynomial extra
  · subst routine
    exact emitDynamicRecentGate_sound op negated₀ negated₁ Work.temporary₃
      Work.loop₃ fixedOffset₁
  · subst routine
    exact BinaryRoutine.clear_sound Work.temporary₃

theorem emitPolynomialRecentGate_requires_internal
    (polynomial : Polynomial ℕ) (extra : ℕ) (op : AndOrOp)
    (negated₀ negated₁ : Bool) (fixedOffset₁ : ℕ)
    (values : BinaryValues WorkCount) :
    (emitPolynomialRecentGate polynomial extra op negated₀ negated₁
        fixedOffset₁).requires values ↔
      values Work.temporary₃ = 0 ∧
        values Work.polynomialScratch = 0 ∧
        values Work.multiplyCounter = 0 ∧
        values Work.addCounter = 0 ∧
        values Work.copyCounter = 0 ∧
        values Work.loop₃ = 0 ∧
        polynomial.eval (values Work.horizon) + extra ≤
          values Work.available ∧
        fixedOffset₁ ≤ values Work.available ∧
        values Work.emitCounter = 0 := by
  simp only [emitPolynomialRecentGate, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.clear, BinaryRoutine.identity,
    BinaryRoutine.emitBits, and_true]
  rw [preparePolynomialOffset_requires_internal,
    emitDynamicRecentGate_requires,
    preparePolynomialOffset_effect_internal]
  simp only [polynomialOffsetDistinct, true_and]
  simp [Work.temporary₃, Work.loop₃,
    Work.copyCounter, Work.available, Work.emitCounter]
  tauto

theorem emitPolynomialRecentGate_effect_internal
    (polynomial : Polynomial ℕ) (extra : ℕ) (op : AndOrOp)
    (negated₀ negated₁ : Bool) (fixedOffset₁ : ℕ)
    (values : BinaryValues WorkCount) (hloop : values Work.loop₃ = 0) :
    (emitPolynomialRecentGate polynomial extra op negated₀ negated₁
        fixedOffset₁).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update values Work.loop₃ 0) Work.available
                (values Work.available + 1)) Work.reference₀ 0)
          Work.reference₁ 0) Work.temporary₃ 0 := by
  simp only [emitPolynomialRecentGate, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.clear, BinaryRoutine.identity,
    BinaryRoutine.emitBits, id_eq]
  rw [preparePolynomialOffset_effect_internal]
  rw [emitDynamicRecentGate_effect op negated₀ negated₁ Work.temporary₃
    Work.loop₃ fixedOffset₁ _ polynomialOffsetDistinct]
  · funext i
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · simpa using hloop

theorem emitPolynomialRecentGate_emitted_internal
    (polynomial : Polynomial ℕ) (extra : ℕ) (op : AndOrOp)
    (negated₀ negated₁ : Bool) (fixedOffset₁ : ℕ)
    (values : BinaryValues WorkCount) (hloop : values Work.loop₃ = 0) :
    (emitPolynomialRecentGate polynomial extra op negated₀ negated₁
        fixedOffset₁).emitted values =
      CircuitCode.RawGate.encode
        { op := op
          input₀ := values Work.available -
            (polynomial.eval (values Work.horizon) + extra)
          input₁ := values Work.available - fixedOffset₁
          negated₀ := negated₀
          negated₁ := negated₁ } := by
  simp only [emitPolynomialRecentGate, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.clear, BinaryRoutine.identity,
    BinaryRoutine.emitBits, List.append_nil]
  rw [preparePolynomialOffset_emitted_internal,
    preparePolynomialOffset_effect_internal]
  rw [emitDynamicRecentGate_emitted op negated₀ negated₁ Work.temporary₃
    Work.loop₃ fixedOffset₁ _ polynomialOffsetDistinct]
  · simp [Work.temporary₃, Work.available]
  · simpa using hloop

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
