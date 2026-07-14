/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.List.Defs
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.List.Internal

/-!
# Finite composition of proof-carrying binary routines

Fixed machine-dependent state, symbol, tape, and transition-case phases can be
unrolled into ordinary lists. This module proves their composition sound once,
leaving only genuinely input-dependent ranges to the binary loop adapter.
-/

namespace Complexity

namespace BinaryRoutine

/-- A fixed list of sound routines composes to a sound routine. -/
theorem seqList_sound
    (routines : List (BinaryRoutine n))
    (hsound : ∀ routine ∈ routines, routine.Sound) :
    (seqList routines).Sound :=
  seqList_sound_internal routines hsound

/-- Fixed finite repetition preserves routine soundness. -/
theorem repeatRoutine_sound (count : ℕ) (routine : BinaryRoutine n)
    (hsound : routine.Sound) :
    (repeatRoutine count routine).Sound :=
  repeatRoutine_sound_internal count routine hsound

end BinaryRoutine

end Complexity
