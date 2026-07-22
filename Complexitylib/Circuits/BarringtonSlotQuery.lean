/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonSlotQuery.Defs
import Complexitylib.Circuits.BarringtonSlotQuery.Internal

/-!
# Direct queries into fixed-address Barrington slots

`barringtonCompileSlot?` locates one instruction in the depth-bounded fixed
schedule without constructing the complete recursive list. Its structural
first- and last-occupied-address recurrences are independent of the target
permutation, so they are suitable for a finite-state machine controller.

## Main results

- `barringtonFirstOccupiedSlot?_eq` -- the structural first address is exact.
- `barringtonLastOccupiedSlot?_eq` -- the structural last address is exact.
- `barringtonCompileSlot?_eq_instruction?` -- every direct query agrees with
  the list-valued fixed-slot compiler.
-/

namespace Complexity

/-- The structural first-address recurrence finds the first occupied slot of
the list-valued fixed schedule. -/
theorem barringtonFirstOccupiedSlot?_eq (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5)) :
    barringtonFirstOccupiedSlot? fuel formula =
      BPSlots.firstOccupiedSlot?
        (barringtonCompileSlots fuel formula target) :=
  (barringtonOccupiedSlots_correct_internal fuel formula target).1

/-- The structural last-address recurrence finds the last occupied slot of
the list-valued fixed schedule. -/
theorem barringtonLastOccupiedSlot?_eq (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5)) :
    barringtonLastOccupiedSlot? fuel formula =
      BPSlots.lastOccupiedSlot?
        (barringtonCompileSlots fuel formula target) :=
  (barringtonOccupiedSlots_correct_internal fuel formula target).2

/-- Every direct fixed-address query agrees with the corresponding query into
the list-valued fixed schedule. -/
theorem barringtonCompileSlot?_eq_instruction? (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5)) (slot : ℕ) :
    barringtonCompileSlot? fuel formula target slot =
      BPSlots.instruction?
        (barringtonCompileSlots fuel formula target) slot :=
  barringtonCompileSlot?_correct_internal fuel formula target slot

end Complexity
