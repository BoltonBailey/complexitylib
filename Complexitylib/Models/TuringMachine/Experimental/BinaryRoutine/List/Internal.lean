/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.List.Defs

/-!
# Finite composition of proof-carrying binary routines -- proof internals
-/

namespace Complexity

namespace BinaryRoutine

theorem seqList_sound_internal
    (routines : List (BinaryRoutine n))
    (hsound : ∀ routine ∈ routines, routine.Sound) :
    (seqList routines).Sound := by
  induction routines with
  | nil => exact identity_sound
  | cons routine routines ih =>
      exact (hsound routine (by simp)).seq
        (ih fun next hnext => hsound next (by simp [hnext]))

theorem repeatRoutine_sound_internal (count : ℕ) (routine : BinaryRoutine n)
    (hsound : routine.Sound) :
    (repeatRoutine count routine).Sound := by
  apply seqList_sound_internal
  intro next hnext
  simp at hnext
  rcases hnext with ⟨_, rfl⟩
  exact hsound

end BinaryRoutine

end Complexity
