/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.PackedCopy.Defs
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.PackedCopy.Internal

/-!
# Delayed packed-formula copies

An executable proof-carrying primitive that advances the rolling formula
cursor and emits the corresponding packed-output copy gate.
-/

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Delayed packed-formula copy emission is sound. -/
theorem emitPackedFormulaCopy_sound (sizePolynomial : Polynomial ℕ) :
    (emitPackedFormulaCopy sizePolynomial).Sound :=
  emitPackedFormulaCopy_sound_internal sizePolynomial

/-- Exact zero-scratch and positive-formula-size domain. -/
theorem emitPackedFormulaCopy_requires (sizePolynomial : Polynomial ℕ)
    (values : BinaryValues WorkCount) :
    (emitPackedFormulaCopy sizePolynomial).requires values ↔
      values Work.temporary₃ = 0 ∧
        values Work.polynomialScratch = 0 ∧
        values Work.multiplyCounter = 0 ∧
        values Work.addCounter = 0 ∧
        values Work.copyCounter = 0 ∧
        values Work.emitCounter = 0 ∧
        0 < sizePolynomial.eval (values Work.horizon) :=
  emitPackedFormulaCopy_requires_internal sizePolynomial values

/-- The rolling formula cursor and wire frontier each advance exactly once;
the reference and polynomial scratch registers are restored to zero. -/
@[simp] theorem emitPackedFormulaCopy_effect (sizePolynomial : Polynomial ℕ)
    (values : BinaryValues WorkCount) :
    (emitPackedFormulaCopy sizePolynomial).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.gateCount
              (values Work.gateCount +
                sizePolynomial.eval (values Work.horizon)))
            Work.available (values Work.available + 1)) Work.reference₀ 0)
        Work.temporary₃ 0 :=
  emitPackedFormulaCopy_effect_internal sizePolynomial values

/-- Exact non-negated copy gate for the output wire of the newly traversed
formula block. -/
@[simp] theorem emitPackedFormulaCopy_emitted (sizePolynomial : Polynomial ℕ)
    (values : BinaryValues WorkCount) :
    (emitPackedFormulaCopy sizePolynomial).emitted values =
      (CircuitCode.RawGate.copy
        (values Work.gateCount +
          sizePolynomial.eval (values Work.horizon) - 1)).encode :=
  emitPackedFormulaCopy_emitted_internal sizePolynomial values

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
