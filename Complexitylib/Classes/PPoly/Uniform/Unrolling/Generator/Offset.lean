/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Offset.Defs
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Offset.Internal

/-!
# Dynamic recent-wire offsets

Proof-carrying helpers for subtracting a run-time wire offset and emitting a
raw gate with one dynamic and one fixed recent-wire reference.
-/

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Dynamic reference subtraction is sound on its explicit domain. -/
theorem decrementReferenceBy_sound (reference offset counter : Fin WorkCount) :
    (decrementReferenceBy reference offset counter).Sound :=
  decrementReferenceBy_sound_internal reference offset counter

/-- The subtraction domain explicitly requires distinct registers, a zero
controller, and an offset no larger than the starting reference. -/
theorem decrementReferenceBy_requires (reference offset counter : Fin WorkCount)
    (values : BinaryValues WorkCount) :
    (decrementReferenceBy reference offset counter).requires values ↔
      DecrementReferenceDistinct reference offset counter ∧
        values counter = 0 ∧ values offset ≤ values reference :=
  decrementReferenceBy_requires_internal reference offset counter values

/-- Exact dynamic subtraction with the count-up controller restored to zero. -/
theorem decrementReferenceBy_effect (reference offset counter : Fin WorkCount)
    (values : BinaryValues WorkCount)
    (hdistinct : DecrementReferenceDistinct reference offset counter)
    (hcounter : values counter = 0) :
    (decrementReferenceBy reference offset counter).effect values =
      Function.update
        (Function.update values reference
          (values reference - values offset)) counter 0 :=
  decrementReferenceBy_effect_internal reference offset counter values
    hdistinct hcounter

/-- Dynamic subtraction emits no circuit-code bits. -/
@[simp] theorem decrementReferenceBy_emitted
    (reference offset counter : Fin WorkCount)
    (values : BinaryValues WorkCount) :
    (decrementReferenceBy reference offset counter).emitted values = [] :=
  decrementReferenceBy_emitted_internal reference offset counter values

/-- Dynamic recent-reference preparation is sound on its explicit domain. -/
theorem prepareDynamicRecentReference_sound
    (reference offset counter : Fin WorkCount) :
    (prepareDynamicRecentReference reference offset counter).Sound :=
  prepareDynamicRecentReference_sound_internal reference offset counter

/-- The preparation domain records every register separation, both zero
controllers, and the valid dynamic offset. -/
theorem prepareDynamicRecentReference_requires
    (reference offset counter : Fin WorkCount)
    (values : BinaryValues WorkCount) :
    (prepareDynamicRecentReference reference offset counter).requires values ↔
      DynamicRecentDistinct reference offset counter ∧
        values Work.copyCounter = 0 ∧ values counter = 0 ∧
        values offset ≤ values Work.available :=
  prepareDynamicRecentReference_requires_internal reference offset counter
    values

/-- Exact dynamic recent-wire reference with its controller restored to zero. -/
theorem prepareDynamicRecentReference_effect
    (reference offset counter : Fin WorkCount)
    (values : BinaryValues WorkCount)
    (hdistinct : DynamicRecentDistinct reference offset counter)
    (hcounter : values counter = 0) :
    (prepareDynamicRecentReference reference offset counter).effect values =
      Function.update
        (Function.update values reference
          (values Work.available - values offset)) counter 0 :=
  prepareDynamicRecentReference_effect_internal reference offset counter values
    hdistinct hcounter

/-- Dynamic recent-reference preparation emits no circuit-code bits. -/
@[simp] theorem prepareDynamicRecentReference_emitted
    (reference offset counter : Fin WorkCount)
    (values : BinaryValues WorkCount) :
    (prepareDynamicRecentReference reference offset counter).emitted values =
      [] :=
  prepareDynamicRecentReference_emitted_internal reference offset counter values

/-- One-dynamic-offset raw-gate emission is sound. -/
theorem emitDynamicRecentGate_sound (op : AndOrOp)
    (negated₀ negated₁ : Bool) (offset counter : Fin WorkCount)
    (fixedOffset₁ : ℕ) :
    (emitDynamicRecentGate op negated₀ negated₁ offset counter
        fixedOffset₁).Sound :=
  emitDynamicRecentGate_sound_internal op negated₀ negated₁ offset counter
    fixedOffset₁

/-- Exact domain for one-dynamic-offset raw-gate emission. -/
theorem emitDynamicRecentGate_requires (op : AndOrOp)
    (negated₀ negated₁ : Bool) (offset counter : Fin WorkCount)
    (fixedOffset₁ : ℕ) (values : BinaryValues WorkCount) :
    (emitDynamicRecentGate op negated₀ negated₁ offset counter
        fixedOffset₁).requires values ↔
      DynamicRecentGateDistinct offset counter ∧
        values Work.copyCounter = 0 ∧ values counter = 0 ∧
        values offset ≤ values Work.available ∧
        fixedOffset₁ ≤ values Work.available ∧
        values Work.emitCounter = 0 :=
  emitDynamicRecentGate_requires_internal op negated₀ negated₁ offset
    counter fixedOffset₁ values

/-- Dynamic recent-gate emission advances `available`, restores the loop
controller, and clears both reference tapes. -/
theorem emitDynamicRecentGate_effect (op : AndOrOp)
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
        Work.reference₁ 0 :=
  emitDynamicRecentGate_effect_internal op negated₀ negated₁ offset
    counter fixedOffset₁ values hdistinct hcounter

/-- Exact raw gate emitted from the dynamic and fixed recent-wire offsets. -/
theorem emitDynamicRecentGate_emitted (op : AndOrOp)
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
          negated₁ := negated₁ } :=
  emitDynamicRecentGate_emitted_internal op negated₀ negated₁ offset
    counter fixedOffset₁ values hdistinct hcounter

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
