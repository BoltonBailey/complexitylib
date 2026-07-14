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
