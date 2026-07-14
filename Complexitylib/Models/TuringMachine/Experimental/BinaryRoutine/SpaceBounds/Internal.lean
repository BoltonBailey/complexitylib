/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.SpaceBounds.Defs

/-!
# Pointwise envelopes for binary-loop space bounds -- proof internals
-/

namespace Complexity

namespace BinaryRoutine

private theorem binaryForIterationSpaceMax_le_of_iteration
    (body : BinaryRoutine n) (counterIdx : Fin n) (initialSpace : ℕ)
    (initial : BinaryValues n) (bound : ℕ) : ∀ total,
    initialSpace ≤ bound →
      (∀ count, count < total →
        binaryForIterationSpace body counterIdx initialSpace initial count ≤
          bound) →
      binaryForIterationSpaceMax body counterIdx initialSpace initial total ≤
        bound := by
  intro total hinitial hiteration
  induction total with
  | zero =>
      simpa [binaryForIterationSpaceMax] using hinitial
  | succ total ih =>
      rw [binaryForIterationSpaceMax]
      apply max_le
      · exact ih fun count hcount => hiteration count (by omega)
      · exact hiteration total (by omega)

theorem BinaryForSpaceEnvelope.iterationSpaceMax_le_internal
    {body : BinaryRoutine n} {counterIdx limitIdx : Fin n}
    {initialSpace : ℕ} {initial : BinaryValues n} {bound : ℕ}
    (envelope : BinaryForSpaceEnvelope body counterIdx limitIdx initialSpace
      initial bound) :
    binaryForIterationSpaceMax body counterIdx initialSpace initial
        (binaryForCount counterIdx limitIdx initial) ≤ bound := by
  apply binaryForIterationSpaceMax_le_of_iteration body counterIdx initialSpace
    initial bound _ envelope.initialSpace_le
  intro count hcount
  rw [binaryForIterationSpace]
  exact max_le (envelope.bodySpace count hcount)
    (envelope.successorSpace count hcount)

theorem BinaryForSpaceEnvelope.binaryForSpace_le_internal
    {body : BinaryRoutine n} {counterIdx limitIdx : Fin n}
    {initialSpace : ℕ} {initial : BinaryValues n} {bound : ℕ}
    (envelope : BinaryForSpaceEnvelope body counterIdx limitIdx initialSpace
      initial bound) :
    binaryForSpace body counterIdx limitIdx initialSpace initial ≤ bound := by
  rw [binaryForSpace]
  exact max_le envelope.compareSpace envelope.iterationSpaceMax_le_internal

theorem BinaryForSpaceEnvelope.spaceBound_le_internal
    {body : BinaryRoutine n} {counterIdx limitIdx : Fin n}
    {initialSpace : ℕ} {initial : BinaryValues n} {bound : ℕ}
    (envelope : BinaryForSpaceEnvelope body counterIdx limitIdx initialSpace
      initial bound) :
    (binaryFor body counterIdx limitIdx).spaceBound initialSpace initial ≤
      bound :=
  envelope.binaryForSpace_le_internal

end BinaryRoutine

end Complexity
