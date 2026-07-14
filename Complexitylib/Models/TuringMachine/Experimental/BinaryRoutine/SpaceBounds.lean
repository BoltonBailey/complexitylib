/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.SpaceBounds.Defs
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.SpaceBounds.Internal

/-!
# Pointwise envelopes for binary-loop space bounds

This module collapses the recursive maximum in `binaryForSpace` to four
local pointwise obligations. In particular, the number of loop iterations
does not appear additively in the resulting space bound.
-/

namespace Complexity

namespace BinaryRoutine

/-- A pointwise logarithmic envelope proves logarithmic routine space along a
fixed input-indexed trajectory. -/
theorem SpaceBoundInLogAt.of_le
    {routine : BinaryRoutine n} {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {bound : ℕ → ℕ}
    (hle : ∀ inputLength,
      routine.spaceBound (initialSpace inputLength) (values inputLength) ≤
        bound inputLength)
    (hbound : bound =O (fun inputLength => Nat.log 2 inputLength)) :
    SpaceBoundInLogAt routine initialSpace values :=
  SpaceBoundInLogAt.of_le_internal hle hbound

/-- Strengthening a precondition preserves an asymptotic space certificate. -/
theorem SpaceBoundInLogAt.restrict
    {routine : BinaryRoutine n} {requires : BinaryValues n → Prop}
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues n}
    (hspace : SpaceBoundInLogAt routine initialSpace values) :
    SpaceBoundInLogAt (routine.restrict requires) initialSpace values :=
  hspace.restrict_internal

/-- Sequential phases preserve logarithmic space when the second certificate
is stated along the first phase's exact pure effect. -/
theorem SpaceBoundInLogAt.seq
    {first second : BinaryRoutine n} {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n}
    (hfirst : SpaceBoundInLogAt first initialSpace values)
    (hsecond : SpaceBoundInLogAt second initialSpace
      (fun inputLength => first.effect (values inputLength))) :
    SpaceBoundInLogAt (seq first second) initialSpace values :=
  hfirst.seq_internal hsecond

/-- Both branches sharing one logarithmic envelope make a zero branch
logarithmic, independently of which branch is selected at each input. -/
theorem SpaceBoundInLogAt.branchZero
    {onZero onPositive : BinaryRoutine n} (idx : Fin n)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues n}
    (hzero : SpaceBoundInLogAt onZero initialSpace values)
    (hpositive : SpaceBoundInLogAt onPositive initialSpace values) :
    SpaceBoundInLogAt (branchZero idx onZero onPositive) initialSpace values :=
  SpaceBoundInLogAt.branchZero_internal idx hzero hpositive

/-- A logarithmic pointwise envelope for all reachable comparisons,
iterations, and successors proves logarithmic space for a binary loop. -/
theorem SpaceBoundInLogAt.binaryFor_of_envelope
    {body : BinaryRoutine n} {counterIdx limitIdx : Fin n}
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues n}
    {bound : ℕ → ℕ}
    (henvelope : ∀ inputLength,
      BinaryForSpaceEnvelope body counterIdx limitIdx
        (initialSpace inputLength) (values inputLength) (bound inputLength))
    (hbound : bound =O (fun inputLength => Nat.log 2 inputLength)) :
    SpaceBoundInLogAt (binaryFor body counterIdx limitIdx) initialSpace
      values :=
  SpaceBoundInLogAt.binaryFor_of_envelope_internal henvelope hbound

/-- A pointwise envelope bounds the recursive maximum over all reachable
iterations. -/
theorem BinaryForSpaceEnvelope.iterationSpaceMax_le
    {body : BinaryRoutine n} {counterIdx limitIdx : Fin n}
    {initialSpace : ℕ} {initial : BinaryValues n} {bound : ℕ}
    (envelope : BinaryForSpaceEnvelope body counterIdx limitIdx initialSpace
      initial bound) :
    binaryForIterationSpaceMax body counterIdx initialSpace initial
        (binaryForCount counterIdx limitIdx initial) ≤ bound :=
  envelope.iterationSpaceMax_le_internal

/-- A pointwise envelope bounds the complete comparison-plus-iteration space
formula of a binary count-up loop. -/
theorem BinaryForSpaceEnvelope.binaryForSpace_le
    {body : BinaryRoutine n} {counterIdx limitIdx : Fin n}
    {initialSpace : ℕ} {initial : BinaryValues n} {bound : ℕ}
    (envelope : BinaryForSpaceEnvelope body counterIdx limitIdx initialSpace
      initial bound) :
    binaryForSpace body counterIdx limitIdx initialSpace initial ≤ bound :=
  envelope.binaryForSpace_le_internal

/-- A pointwise envelope directly bounds the advertised space budget of the
corresponding proof-carrying binary loop. -/
theorem BinaryForSpaceEnvelope.spaceBound_le
    {body : BinaryRoutine n} {counterIdx limitIdx : Fin n}
    {initialSpace : ℕ} {initial : BinaryValues n} {bound : ℕ}
    (envelope : BinaryForSpaceEnvelope body counterIdx limitIdx initialSpace
      initial bound) :
    (binaryFor body counterIdx limitIdx).spaceBound initialSpace initial ≤
      bound :=
  envelope.spaceBound_le_internal

end BinaryRoutine

end Complexity
