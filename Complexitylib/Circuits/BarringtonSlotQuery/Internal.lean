/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonSlotQuery.Defs
import Complexitylib.Circuits.BarringtonSlots.Internal

/-!
# Direct queries into fixed-address Barrington slots -- proof internals
-/

namespace Complexity

namespace BPSlots

@[simp] theorem firstOccupiedSlot?_replicate_none_internal (count : ℕ) :
    firstOccupiedSlot?
      (List.replicate count (none : Option (BPInstr w))) = none := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (firstOccupiedSlot?
        (List.replicate count (none : Option (BPInstr w)))).map Nat.succ = none
      rw [ih]
      rfl

@[simp] theorem lastOccupiedSlot?_replicate_none_internal (count : ℕ) :
    lastOccupiedSlot?
      (List.replicate count (none : Option (BPInstr w))) = none := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (match lastOccupiedSlot?
        (List.replicate count (none : Option (BPInstr w))) with
        | some last => some (last + 1)
        | none => none) = none
      rw [ih]

theorem firstOccupiedSlot?_append_internal
    (left right : BPSlots w) :
    firstOccupiedSlot? (left ++ right) =
      match firstOccupiedSlot? left with
      | some slot => some slot
      | none => (firstOccupiedSlot? right).map (left.length + ·) := by
  induction left with
  | nil => simp [firstOccupiedSlot?]
  | cons slot left ih =>
      cases slot with
      | none =>
          simp only [List.cons_append, firstOccupiedSlot?, List.length_cons]
          rw [ih]
          cases hleft : firstOccupiedSlot? left with
          | none =>
              cases hright : firstOccupiedSlot? right with
              | none => simp
              | some rightSlot => simp; omega
          | some leftSlot =>
              cases hright : firstOccupiedSlot? right <;> simp
      | some instruction => rfl

theorem lastOccupiedSlot?_append_internal
    (left right : BPSlots w) :
    lastOccupiedSlot? (left ++ right) =
      match lastOccupiedSlot? right with
      | some slot => some (left.length + slot)
      | none => lastOccupiedSlot? left := by
  induction left with
  | nil =>
      simp only [List.nil_append, List.length_nil, Nat.zero_add]
      cases lastOccupiedSlot? right <;> rfl
  | cons slot left ih =>
      simp only [List.cons_append, lastOccupiedSlot?, List.length_cons]
      rw [ih]
      cases hright : lastOccupiedSlot? right with
      | some rightSlot => simp; omega
      | none => rfl

theorem firstOccupiedSlot?_eq_none_iff_internal (slots : BPSlots w) :
    firstOccupiedSlot? slots = none ↔ slots.filterMap id = [] := by
  induction slots with
  | nil => simp [firstOccupiedSlot?]
  | cons slot slots ih =>
      cases slot <;> simp [firstOccupiedSlot?, ih]

theorem lastOccupiedSlot?_eq_none_iff_internal (slots : BPSlots w) :
    lastOccupiedSlot? slots = none ↔ slots.filterMap id = [] := by
  induction slots with
  | nil => simp [lastOccupiedSlot?]
  | cons slot slots ih =>
      cases hlast : lastOccupiedSlot? slots with
      | none =>
          have hfilter : slots.filterMap id = [] :=
            (ih.mp hlast)
          cases slot with
          | none =>
              rw [List.filterMap_cons_none rfl]
              constructor
              · intro _
                exact hfilter
              · intro _
                simp [lastOccupiedSlot?, hlast]
          | some instruction =>
              change lastOccupiedSlot? (some instruction :: slots) = none ↔
                instruction :: slots.filterMap id = []
              constructor <;> intro h
              · simp [lastOccupiedSlot?, hlast] at h
              · simp at h
      | some last =>
          have hfilter : slots.filterMap id ≠ [] := by
            intro hempty
            exact Option.some_ne_none last
              (hlast.symm.trans (ih.mpr hempty))
          cases slot with
          | none =>
              rw [List.filterMap_cons_none rfl]
              constructor
              · intro hnone
                simp [lastOccupiedSlot?, hlast] at hnone
              · intro hempty
                exact (hfilter hempty).elim
          | some instruction =>
              change lastOccupiedSlot? (some instruction :: slots) = none ↔
                instruction :: slots.filterMap id = []
              constructor
              · intro hnone
                simp [lastOccupiedSlot?, hlast] at hnone
              · intro hempty
                simp at hempty

theorem lastOccupiedSlot?_eq_none_iff_first_internal (slots : BPSlots w) :
    lastOccupiedSlot? slots = none ↔ firstOccupiedSlot? slots = none :=
  (lastOccupiedSlot?_eq_none_iff_internal slots).trans
    (firstOccupiedSlot?_eq_none_iff_internal slots).symm

theorem firstOccupiedSlot?_lt_length_internal
    {slots : BPSlots w} {slot : ℕ}
    (hslot : firstOccupiedSlot? slots = some slot) :
    slot < slots.length := by
  induction slots generalizing slot with
  | nil => simp [firstOccupiedSlot?] at hslot
  | cons head slots ih =>
      cases head with
      | none =>
          simp only [firstOccupiedSlot?] at hslot
          cases hfirst : firstOccupiedSlot? slots with
          | none => simp [hfirst] at hslot
          | some first =>
              simp [hfirst] at hslot
              subst slot
              simpa using Nat.succ_lt_succ (ih hfirst)
      | some instruction =>
          simp [firstOccupiedSlot?] at hslot
          subst slot
          simp

theorem lastOccupiedSlot?_lt_length_internal
    {slots : BPSlots w} {slot : ℕ}
    (hslot : lastOccupiedSlot? slots = some slot) :
    slot < slots.length := by
  induction slots generalizing slot with
  | nil => simp [lastOccupiedSlot?] at hslot
  | cons head slots ih =>
      simp only [lastOccupiedSlot?] at hslot
      cases hlast : lastOccupiedSlot? slots with
      | some last =>
          simp [hlast] at hslot
          subst slot
          simpa using Nat.succ_lt_succ (ih hlast)
      | none =>
          simp only [hlast] at hslot
          split at hslot
          · simp at hslot
            subst slot
            simp
          · simp at hslot

theorem firstOccupiedSlot?_map_internal
    (slots : BPSlots w) (f : BPInstr w → BPInstr v) :
    firstOccupiedSlot? (slots.map (Option.map f)) =
      firstOccupiedSlot? slots := by
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
      cases slot <;> simp [firstOccupiedSlot?, ih]

theorem lastOccupiedSlot?_map_internal
    (slots : BPSlots w) (f : BPInstr w → BPInstr v) :
    lastOccupiedSlot? (slots.map (Option.map f)) =
      lastOccupiedSlot? slots := by
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
      cases slot <;> simp [lastOccupiedSlot?, ih]

theorem firstOccupiedSlot?_reverse_internal (slots : BPSlots w) :
    firstOccupiedSlot? slots.reverse =
      (lastOccupiedSlot? slots).map fun slot =>
        slots.length - 1 - slot := by
  induction slots with
  | nil => rfl
  | cons head slots ih =>
      rw [List.reverse_cons, firstOccupiedSlot?_append_internal, ih]
      cases hlast : lastOccupiedSlot? slots with
      | some last =>
          simp only [lastOccupiedSlot?, hlast, Option.map_some,
            List.length_cons]
          congr 1
          rw [Nat.add_sub_cancel, Nat.sub_sub]
          simp [Nat.add_comm]
      | none =>
          cases head <;>
            simp [firstOccupiedSlot?, lastOccupiedSlot?, hlast]

theorem lastOccupiedSlot?_reverse_internal (slots : BPSlots w) :
    lastOccupiedSlot? slots.reverse =
      (firstOccupiedSlot? slots).map fun slot =>
        slots.length - 1 - slot := by
  induction slots with
  | nil => rfl
  | cons head slots ih =>
      rw [List.reverse_cons, lastOccupiedSlot?_append_internal]
      cases head with
      | some instruction => simp [firstOccupiedSlot?, lastOccupiedSlot?]
      | none =>
          cases hfirst : firstOccupiedSlot? slots with
          | none =>
              simp [lastOccupiedSlot?, firstOccupiedSlot?, ih, hfirst]
          | some first =>
              have hlt := firstOccupiedSlot?_lt_length_internal hfirst
              simp [lastOccupiedSlot?, firstOccupiedSlot?, ih, hfirst]
              omega

theorem firstOccupiedSlot?_inverse_internal (slots : BPSlots w) :
    firstOccupiedSlot? slots.inverse =
      (lastOccupiedSlot? slots).map fun slot =>
        slots.length - 1 - slot := by
  rw [BPSlots.inverse, firstOccupiedSlot?_reverse_internal,
    lastOccupiedSlot?_map_internal]
  simp

theorem lastOccupiedSlot?_inverse_internal (slots : BPSlots w) :
    lastOccupiedSlot? slots.inverse =
      (firstOccupiedSlot? slots).map fun slot =>
        slots.length - 1 - slot := by
  rw [BPSlots.inverse, lastOccupiedSlot?_reverse_internal,
    firstOccupiedSlot?_map_internal]
  simp

theorem firstOccupiedSlot?_postMulFirst_internal (slots : BPSlots w)
    (permutation : Equiv.Perm (Fin w)) :
    firstOccupiedSlot? (postMulFirst permutation slots) =
      firstOccupiedSlot? slots := by
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
      cases slot <;> simp [postMulFirst, firstOccupiedSlot?, ih]

theorem lastOccupiedSlot?_postMulFirst_internal (slots : BPSlots w)
    (permutation : Equiv.Perm (Fin w)) :
    lastOccupiedSlot? (postMulFirst permutation slots) =
      lastOccupiedSlot? slots := by
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
      cases slot <;> simp [postMulFirst, lastOccupiedSlot?, ih]

theorem firstOccupiedSlot?_postMul_internal (slots : BPSlots w)
    (permutation : Equiv.Perm (Fin w)) (hne : slots ≠ []) :
    firstOccupiedSlot? (slots.postMul permutation) =
      some ((firstOccupiedSlot? slots).getD 0) := by
  rw [BPSlots.postMul.eq_def]
  split
  · rename_i hempty
    cases slots with
    | nil => exact (hne rfl).elim
    | cons slot slots =>
        have hfirst : firstOccupiedSlot? (slot :: slots) = none :=
          firstOccupiedSlot?_eq_none_iff_internal _ |>.2 hempty
        cases slot with
        | none =>
            have htail : firstOccupiedSlot? slots = none := by
              simpa [firstOccupiedSlot?] using hfirst
            simp [firstOccupiedSlot?, htail]
        | some instruction => simp [firstOccupiedSlot?] at hfirst
  · rename_i hnonempty
    rw [firstOccupiedSlot?_reverse_internal,
      lastOccupiedSlot?_postMulFirst_internal,
      lastOccupiedSlot?_reverse_internal]
    cases hfirst : firstOccupiedSlot? slots with
    | none =>
        exact (hnonempty
          (firstOccupiedSlot?_eq_none_iff_internal _ |>.1 hfirst)).elim
    | some first =>
        have hlt := firstOccupiedSlot?_lt_length_internal hfirst
        simp only [Option.map_some, List.length_reverse,
          BPSlots.length_postMulFirst_internal, Option.getD_some]
        congr 2
        omega

theorem lastOccupiedSlot?_postMul_internal (slots : BPSlots w)
    (permutation : Equiv.Perm (Fin w)) (hne : slots ≠ []) :
    lastOccupiedSlot? (slots.postMul permutation) =
      some ((lastOccupiedSlot? slots).getD 0) := by
  rw [BPSlots.postMul.eq_def]
  split
  · rename_i hempty
    cases slots with
    | nil => exact (hne rfl).elim
    | cons slot slots =>
        have hrest : slots.filterMap id = [] := by
          cases slot with
          | none => simpa using hempty
          | some instruction => simp at hempty
        have hlast : lastOccupiedSlot? slots = none :=
          lastOccupiedSlot?_eq_none_iff_internal _ |>.2 hrest
        cases slot with
        | none => simp [lastOccupiedSlot?, hlast]
        | some instruction => simp at hempty
  · rename_i hnonempty
    rw [lastOccupiedSlot?_reverse_internal,
      firstOccupiedSlot?_postMulFirst_internal,
      firstOccupiedSlot?_reverse_internal]
    cases hlast : lastOccupiedSlot? slots with
    | none =>
        exact (hnonempty
          (lastOccupiedSlot?_eq_none_iff_internal _ |>.1 hlast)).elim
    | some last =>
        have hlt := lastOccupiedSlot?_lt_length_internal hlast
        simp only [Option.map_some, List.length_reverse,
          BPSlots.length_postMulFirst_internal, Option.getD_some]
        congr 2
        omega

theorem instruction?_append_internal (left right : BPSlots w)
    (slot : ℕ) :
    instruction? (left ++ right) slot =
      if slot < left.length then instruction? left slot
      else instruction? right (slot - left.length) := by
  rw [instruction?, List.getElem?_append]
  split <;> rfl

@[simp] theorem instruction?_replicate_none_internal
    (count slot : ℕ) :
    instruction?
      (List.replicate count (none : Option (BPInstr w))) slot = none := by
  rw [instruction?, List.getElem?_replicate]
  split <;> rfl

theorem instruction?_singletonAt_internal (fuel : ℕ)
    (instruction : BPInstr w) (slot : ℕ) :
    instruction? (singletonAt fuel instruction) slot =
      if slot = 0 then some instruction else none := by
  cases slot with
  | zero => rfl
  | succ slot =>
      rw [if_neg (by omega)]
      exact instruction?_replicate_none_internal _ _

theorem instruction?_emptyAt_internal (fuel slot : ℕ) :
    instruction? (emptyAt fuel : BPSlots w) slot = none :=
  instruction?_replicate_none_internal _ _

theorem instruction?_eq_none_of_first_eq_none_internal
    {slots : BPSlots w}
    (hfirst : firstOccupiedSlot? slots = none) (slot : ℕ) :
    instruction? slots slot = none := by
  induction slots generalizing slot with
  | nil => simp [instruction?]
  | cons head slots ih =>
      cases head with
      | some instruction => simp [firstOccupiedSlot?] at hfirst
      | none =>
          have htail : firstOccupiedSlot? slots = none := by
            simpa [firstOccupiedSlot?] using hfirst
          cases slot with
          | zero => rfl
          | succ slot =>
              simpa [instruction?] using ih htail slot

theorem instruction?_postMulFirst_internal (slots : BPSlots w)
    (permutation : Equiv.Perm (Fin w)) (slot : ℕ) :
    instruction? (postMulFirst permutation slots) slot =
      match firstOccupiedSlot? slots with
      | none => instruction? slots slot
      | some first =>
          (instruction? slots slot).map fun instruction =>
            if slot = first then instruction.postMul permutation
            else instruction := by
  induction slots generalizing slot with
  | nil => simp [postMulFirst, firstOccupiedSlot?, instruction?]
  | cons head slots ih =>
      cases head with
      | some instruction =>
          cases slot <;>
            simp [postMulFirst, firstOccupiedSlot?, instruction?]
      | none =>
          cases slot with
          | zero =>
              simp only [postMulFirst, firstOccupiedSlot?, instruction?]
              cases firstOccupiedSlot? slots <;> rfl
          | succ slot =>
              change instruction? (postMulFirst permutation slots) slot =
                match (firstOccupiedSlot? slots).map Nat.succ with
                | none => instruction? slots slot
                | some first =>
                    (instruction? slots slot).map fun instruction =>
                      if slot + 1 = first then
                        instruction.postMul permutation else instruction
              rw [ih]
              cases hfirst : firstOccupiedSlot? slots with
              | none => rfl
              | some first => simp

theorem instruction?_reverse_internal (slots : BPSlots w) (slot : ℕ) :
    instruction? slots.reverse slot =
      if slot < slots.length then
        instruction? slots (slots.length - 1 - slot)
      else
        none := by
  by_cases hslot : slot < slots.length
  · rw [if_pos hslot, instruction?,
      List.getElem?_reverse (l := slots) (i := slot) hslot]
    rfl
  · rw [if_neg hslot, instruction?]
    have hlength : slots.reverse.length ≤ slot := by simp; omega
    rw [List.getElem?_eq_none hlength]
    rfl

theorem instruction?_inverse_internal (slots : BPSlots w) (slot : ℕ) :
    instruction? slots.inverse slot =
      if slot < slots.length then
        (instruction? slots (slots.length - 1 - slot)).map
          BPInstr.inverse
      else
        none := by
  rw [BPSlots.inverse]
  by_cases hslot : slot < slots.length
  · rw [if_pos hslot]
    have hmapLength :
        (slots.map fun entry => entry.map BPInstr.inverse).length =
          slots.length := by simp
    have hreverse := List.getElem?_reverse
      (l := slots.map fun entry => entry.map BPInstr.inverse)
      (i := slot) (by simpa [hmapLength] using hslot)
    simp only [instruction?, hreverse, hmapLength, List.getElem?_map]
    cases slots[slots.length - 1 - slot]? <;> rfl
  · rw [if_neg hslot]
    apply Option.eq_none_iff_forall_not_mem.mpr
    intro instruction hinstruction
    have hlength :
        (slots.map fun entry => entry.map BPInstr.inverse).reverse.length ≤
          slot := by simp; omega
    rw [instruction?, List.getElem?_eq_none hlength] at hinstruction
    simp at hinstruction

theorem barringtonPostMulSlot?_correct_internal
    (slots : BPSlots 5) (permutation : Equiv.Perm (Fin 5))
    (slot : ℕ) (hne : slots ≠ []) :
    barringtonPostMulSlot? (instruction? slots)
        (lastOccupiedSlot? slots) permutation slot =
      instruction? (slots.postMul permutation) slot := by
  rw [BPSlots.postMul.eq_def]
  by_cases hempty : slots.filterMap id = []
  · rw [if_pos hempty]
    have hlast : lastOccupiedSlot? slots = none :=
      lastOccupiedSlot?_eq_none_iff_internal slots |>.2 hempty
    rw [barringtonPostMulSlot?.eq_def, hlast]
    cases slots with
    | nil => exact (hne rfl).elim
    | cons head slots =>
        have hhead : head = none := by
          have hall := List.filterMap_eq_nil_iff.mp hempty head
            (by simp)
          simpa using hall
        subst head
        have hrestFilter : slots.filterMap id = [] := by
          simpa using hempty
        have hrestFirst : firstOccupiedSlot? slots = none :=
          firstOccupiedSlot?_eq_none_iff_internal slots |>.2 hrestFilter
        cases slot with
        | zero => rfl
        | succ slot =>
            rw [if_neg (by omega)]
            simpa [instruction?] using
              (instruction?_eq_none_of_first_eq_none_internal
                hrestFirst slot).symm
  · rw [if_neg hempty]
    cases hlast : lastOccupiedSlot? slots with
    | none =>
        exact (hempty
          (lastOccupiedSlot?_eq_none_iff_internal slots |>.1 hlast)).elim
    | some last =>
        have hlastLt := lastOccupiedSlot?_lt_length_internal hlast
        simp only [barringtonPostMulSlot?.eq_def]
        by_cases hslot : slot < slots.length
        · rw [instruction?_reverse_internal]
          rw [if_pos (by
            simpa [BPSlots.length_postMulFirst_internal] using hslot)]
          simp only [List.length_reverse,
            BPSlots.length_postMulFirst_internal]
          rw [instruction?_postMulFirst_internal,
            firstOccupiedSlot?_reverse_internal, hlast]
          simp only [Option.map_some]
          have hreversedLt : slots.length - 1 - slot < slots.length := by
            omega
          rw [instruction?_reverse_internal,
            if_pos hreversedLt]
          have hdouble :
              slots.length - 1 - (slots.length - 1 - slot) = slot := by
            omega
          rw [hdouble]
          by_cases heq : slot = last
          · subst last
            simp
          · have hreverseNe :
                slots.length - 1 - slot ≠
                  slots.length - 1 - last := by
              omega
            simp [heq, hreverseNe]
        · have hquery : instruction? slots slot = none := by
            rw [instruction?]
            exact congrArg Option.join
              (List.getElem?_eq_none (by omega))
          rw [hquery]
          simp only [Option.map_none]
          rw [instruction?_reverse_internal]
          rw [if_neg (by
            simp [BPSlots.length_postMulFirst_internal]
            omega)]

theorem barringtonInverseSlot?_correct_internal
    (slots : BPSlots 5) (slot : ℕ) :
    barringtonInverseSlot? slots.length (instruction? slots) slot =
      instruction? slots.inverse slot := by
  rw [barringtonInverseSlot?, instruction?_inverse_internal]

theorem instruction?_fourBlocks_internal
    (left right : BPSlots 5) (blockSize slot : ℕ)
    (hleftLength : left.length = blockSize)
    (hrightLength : right.length = blockSize) :
    instruction?
        (left ++ right ++ left.inverse ++ right.inverse) slot =
      if slot < blockSize then
        instruction? left slot
      else if slot < 2 * blockSize then
        instruction? right (slot - blockSize)
      else if slot < 3 * blockSize then
        instruction? left.inverse (slot - 2 * blockSize)
      else if slot < 4 * blockSize then
        instruction? right.inverse (slot - 3 * blockSize)
      else
        none := by
  rw [instruction?_append_internal]
  simp only [List.length_append, BPSlots.length_inverse_internal,
    hleftLength, hrightLength]
  by_cases hthree : slot < 3 * blockSize
  · rw [if_pos (by omega)]
    rw [instruction?_append_internal]
    simp only [List.length_append, hleftLength, hrightLength]
    by_cases htwo : slot < 2 * blockSize
    · rw [if_pos (by omega)]
      rw [instruction?_append_internal]
      simp only [hleftLength]
      by_cases hone : slot < blockSize
      · simp [hone]
      · simp [hone, htwo]
    · rw [if_neg (by omega)]
      have hone : ¬slot < blockSize := by omega
      have hsub : slot - (blockSize + blockSize) =
          slot - 2 * blockSize := by omega
      rw [if_neg hone, hsub]
      rw [if_neg htwo, if_pos hthree]
  · by_cases hfour : slot < 4 * blockSize
    · rw [if_neg (by omega)]
      have hone : ¬slot < blockSize := by omega
      have htwo : ¬slot < 2 * blockSize := by omega
      have hsub : slot - (blockSize + blockSize + blockSize) =
          slot - 3 * blockSize := by omega
      rw [if_neg hone, if_neg htwo, hsub]
      rw [if_neg hthree, if_pos hfour]
    · rw [if_neg (by omega)]
      have hout : right.inverse.length ≤
          slot - (blockSize + blockSize + blockSize) := by
        rw [BPSlots.length_inverse_internal, hrightLength]
        omega
      rw [instruction?, List.getElem?_eq_none hout]
      have hone : ¬slot < blockSize := by omega
      have htwo : ¬slot < 2 * blockSize := by omega
      rw [if_neg hone, if_neg htwo]
      rw [if_neg hthree, if_neg hfour]
      rfl

end BPSlots

private theorem barringtonCompileSlots_ne_nil_query_internal
    (fuel : ℕ) (formula : BoolFormula)
    (target : Equiv.Perm (Fin 5)) :
    barringtonCompileSlots fuel formula target ≠ [] := by
  intro hempty
  have hlength := barringtonCompileSlots_length_internal fuel formula target
  rw [hempty] at hlength
  have hpositive : 0 < 4 ^ fuel := pow_pos (by omega) fuel
  simp at hlength
  omega

/-- The structural first/last recurrences identify the exact occupied
extremes of the list-valued fixed-slot compiler. -/
theorem barringtonOccupiedSlots_correct_internal (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5)) :
    barringtonFirstOccupiedSlot? fuel formula =
        BPSlots.firstOccupiedSlot?
          (barringtonCompileSlots fuel formula target) ∧
      barringtonLastOccupiedSlot? fuel formula =
        BPSlots.lastOccupiedSlot?
          (barringtonCompileSlots fuel formula target) := by
  induction fuel generalizing formula target with
  | zero =>
      cases formula <;>
        simp [barringtonFirstOccupiedSlot?, barringtonLastOccupiedSlot?,
          barringtonCompileSlots, BPSlots.singletonAt, BPSlots.emptyAt,
          BPSlots.firstOccupiedSlot?, BPSlots.lastOccupiedSlot?]
  | succ fuel ih =>
      cases formula with
      | var index =>
          simp [barringtonFirstOccupiedSlot?, barringtonLastOccupiedSlot?,
            barringtonCompileSlots, BPSlots.singletonAt,
            BPSlots.firstOccupiedSlot?, BPSlots.lastOccupiedSlot?]
      | tru =>
          simp [barringtonFirstOccupiedSlot?, barringtonLastOccupiedSlot?,
            barringtonCompileSlots, BPSlots.singletonAt,
            BPSlots.firstOccupiedSlot?, BPSlots.lastOccupiedSlot?]
      | fls =>
          simp [barringtonFirstOccupiedSlot?, barringtonLastOccupiedSlot?,
            barringtonCompileSlots, BPSlots.emptyAt]
      | neg formula =>
          obtain ⟨hfirst, hlast⟩ := ih formula target⁻¹
          have hne := barringtonCompileSlots_ne_nil_query_internal
            fuel formula target⁻¹
          constructor
          · simp [barringtonFirstOccupiedSlot?, barringtonCompileSlots,
              BPSlots.firstOccupiedSlot?_append_internal,
              BPSlots.firstOccupiedSlot?_postMul_internal, hne,
              hfirst]
          · simp [barringtonLastOccupiedSlot?, barringtonCompileSlots,
              BPSlots.lastOccupiedSlot?_append_internal,
              BPSlots.lastOccupiedSlot?_postMul_internal, hne,
              hlast]
      | conj left right =>
          obtain ⟨hleftFirst, hleftLast⟩ :=
            ih left (barringtonLeft target)
          obtain ⟨hrightFirst, hrightLast⟩ :=
            ih right (barringtonRight target)
          cases hleft : barringtonFirstOccupiedSlot? fuel left <;>
            cases hright : barringtonFirstOccupiedSlot? fuel right
          all_goals
            have hleftActual := hleftFirst.symm.trans hleft
            have hrightActual := hrightFirst.symm.trans hright
            have hleftEmpty :=
              BPSlots.lastOccupiedSlot?_eq_none_iff_first_internal
                (barringtonCompileSlots fuel left (barringtonLeft target))
            have hrightEmpty :=
              BPSlots.lastOccupiedSlot?_eq_none_iff_first_internal
                (barringtonCompileSlots fuel right (barringtonRight target))
            simp [hleftActual] at hleftEmpty
            simp [hrightActual] at hrightEmpty
            constructor
            · simp [barringtonFirstOccupiedSlot?,
                barringtonCompileSlots,
                BPSlots.firstOccupiedSlot?_append_internal,
                BPSlots.firstOccupiedSlot?_inverse_internal,
                BPSlots.length_inverse_internal,
                barringtonCompileSlots_length_internal, hleft, hright,
                hleftActual, hrightActual, hleftEmpty, hrightEmpty]
            · simp [barringtonLastOccupiedSlot?,
                barringtonCompileSlots,
                BPSlots.lastOccupiedSlot?_append_internal,
                BPSlots.lastOccupiedSlot?_inverse_internal,
                BPSlots.length_inverse_internal,
                barringtonCompileSlots_length_internal, hleft, hright,
                hleftActual, hrightActual, hleftEmpty, hrightEmpty]
              all_goals ring_nf
      | disj left right =>
          let innerTarget := target⁻¹
          let leftTarget := barringtonLeft innerTarget
          let rightTarget := barringtonRight innerTarget
          let leftBase :=
            barringtonCompileSlots fuel left leftTarget⁻¹
          let rightBase :=
            barringtonCompileSlots fuel right rightTarget⁻¹
          let leftSlots := leftBase.postMul leftTarget
          let rightSlots := rightBase.postMul rightTarget
          let commSlots := leftSlots ++ rightSlots ++ leftSlots.inverse ++
            rightSlots.inverse
          obtain ⟨hleftFirst, hleftLast⟩ := ih left leftTarget⁻¹
          obtain ⟨hrightFirst, hrightLast⟩ := ih right rightTarget⁻¹
          have hleftNe : leftBase ≠ [] := by
            exact barringtonCompileSlots_ne_nil_query_internal
              fuel left leftTarget⁻¹
          have hrightNe : rightBase ≠ [] := by
            exact barringtonCompileSlots_ne_nil_query_internal
              fuel right rightTarget⁻¹
          have hleftSlotsFirst : BPSlots.firstOccupiedSlot? leftSlots =
              some ((BPSlots.firstOccupiedSlot? leftBase).getD 0) := by
            exact BPSlots.firstOccupiedSlot?_postMul_internal
              leftBase leftTarget hleftNe
          have hrightSlotsFirst : BPSlots.firstOccupiedSlot? rightSlots =
              some ((BPSlots.firstOccupiedSlot? rightBase).getD 0) := by
            exact BPSlots.firstOccupiedSlot?_postMul_internal
              rightBase rightTarget hrightNe
          have hcommNe : commSlots ≠ [] := by
            intro hempty
            have hlength := congrArg List.length hempty
            simp [commSlots, leftSlots, leftBase,
              BPSlots.length_postMul_internal,
              barringtonCompileSlots_length_internal] at hlength
          have hcommFirst : BPSlots.firstOccupiedSlot? commSlots =
              some ((BPSlots.firstOccupiedSlot? leftBase).getD 0) := by
            simp [commSlots, BPSlots.firstOccupiedSlot?_append_internal,
              hleftSlotsFirst]
          have hcommLast : BPSlots.lastOccupiedSlot? commSlots =
              some (3 * 4 ^ fuel +
                (4 ^ fuel - 1 -
                  (BPSlots.firstOccupiedSlot? rightBase).getD 0)) := by
            rw [show commSlots =
              (leftSlots ++ rightSlots ++ leftSlots.inverse) ++
                rightSlots.inverse by simp [commSlots, List.append_assoc]]
            rw [BPSlots.lastOccupiedSlot?_append_internal,
              BPSlots.lastOccupiedSlot?_inverse_internal,
              hrightSlotsFirst]
            simp only [Option.map_some]
            simp [leftSlots, rightSlots, leftBase, rightBase,
              BPSlots.length_postMul_internal,
              BPSlots.length_inverse_internal,
              barringtonCompileSlots_length_internal]
            ring_nf
          have hfinalFirst := BPSlots.firstOccupiedSlot?_postMul_internal
            commSlots target hcommNe
          have hfinalLast := BPSlots.lastOccupiedSlot?_postMul_internal
            commSlots target hcommNe
          rw [show barringtonCompileSlots (fuel + 1) (.disj left right)
            target = commSlots.postMul target from rfl]
          constructor
          · rw [hfinalFirst, hcommFirst]
            simpa [barringtonFirstOccupiedSlot?, leftBase] using
              congrArg (Option.getD · 0) hleftFirst
          · rw [hfinalLast, hcommLast]
            simpa [barringtonLastOccupiedSlot?, rightBase] using
              congrArg (fun slot =>
                4 ^ fuel - 1 - slot.getD 0) hrightFirst

/-- The depth-bounded direct query returns exactly the instruction stored at
the corresponding address of the list-valued fixed-slot compiler. -/
theorem barringtonCompileSlot?_correct_internal (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5)) (slot : ℕ) :
    barringtonCompileSlot? fuel formula target slot =
      BPSlots.instruction?
        (barringtonCompileSlots fuel formula target) slot := by
  induction fuel generalizing formula target slot with
  | zero =>
      cases formula <;> cases slot <;>
        simp [barringtonCompileSlot?, barringtonCompileSlots,
          BPSlots.instruction?, BPSlots.singletonAt, BPSlots.emptyAt]
  | succ fuel ih =>
      cases formula with
      | var index =>
          simp [barringtonCompileSlot?, barringtonCompileSlots,
            BPSlots.instruction?_singletonAt_internal]
      | tru =>
          simp [barringtonCompileSlot?, barringtonCompileSlots,
            BPSlots.instruction?_singletonAt_internal]
      | fls =>
          simp [barringtonCompileSlot?, barringtonCompileSlots,
            BPSlots.instruction?_emptyAt_internal]
      | neg formula =>
          have hlast :=
            (barringtonOccupiedSlots_correct_internal fuel formula target⁻¹).2
          have hne := barringtonCompileSlots_ne_nil_query_internal
            fuel formula target⁻¹
          have hpostLength :
              ((barringtonCompileSlots fuel formula target⁻¹).postMul
                target).length = 4 ^ fuel := by
            rw [BPSlots.length_postMul_internal,
              barringtonCompileSlots_length_internal]
          have hquery :
              barringtonCompileSlot? fuel formula target⁻¹ =
                BPSlots.instruction?
                  (barringtonCompileSlots fuel formula target⁻¹) := by
            funext querySlot
            exact ih formula target⁻¹ querySlot
          by_cases hslot : slot < 4 ^ fuel
          · simp only [barringtonCompileSlot?, hslot, ↓reduceIte,
              barringtonCompileSlots,
              BPSlots.instruction?_append_internal, hpostLength]
            rw [hquery, hlast]
            exact BPSlots.barringtonPostMulSlot?_correct_internal
              (barringtonCompileSlots fuel formula target⁻¹)
              target slot hne
          · simp only [barringtonCompileSlot?, hslot, ↓reduceIte,
              barringtonCompileSlots,
              BPSlots.instruction?_append_internal, hpostLength]
            exact BPSlots.instruction?_replicate_none_internal _ _ |>.symm
      | conj left right =>
          let leftTarget := barringtonLeft target
          let rightTarget := barringtonRight target
          let leftSlots :=
            barringtonCompileSlots fuel left leftTarget
          let rightSlots :=
            barringtonCompileSlots fuel right rightTarget
          have hleftLength : leftSlots.length = 4 ^ fuel := by
            exact barringtonCompileSlots_length_internal
              fuel left leftTarget
          have hrightLength : rightSlots.length = 4 ^ fuel := by
            exact barringtonCompileSlots_length_internal
              fuel right rightTarget
          have hleftQuery :
              barringtonCompileSlot? fuel left leftTarget =
                BPSlots.instruction? leftSlots := by
            funext querySlot
            exact ih left leftTarget querySlot
          have hrightQuery :
              barringtonCompileSlot? fuel right rightTarget =
                BPSlots.instruction? rightSlots := by
            funext querySlot
            exact ih right rightTarget querySlot
          have hleftInverse (querySlot : ℕ) :
              barringtonInverseSlot? (4 ^ fuel)
                  (BPSlots.instruction? leftSlots) querySlot =
                BPSlots.instruction? leftSlots.inverse querySlot := by
            rw [← hleftLength]
            exact BPSlots.barringtonInverseSlot?_correct_internal
              leftSlots querySlot
          have hrightInverse (querySlot : ℕ) :
              barringtonInverseSlot? (4 ^ fuel)
                  (BPSlots.instruction? rightSlots) querySlot =
                BPSlots.instruction? rightSlots.inverse querySlot := by
            rw [← hrightLength]
            exact BPSlots.barringtonInverseSlot?_correct_internal
              rightSlots querySlot
          rw [show barringtonCompileSlots (fuel + 1) (.conj left right)
              target = leftSlots ++ rightSlots ++ leftSlots.inverse ++
                rightSlots.inverse from rfl]
          rw [BPSlots.instruction?_fourBlocks_internal leftSlots rightSlots
            (4 ^ fuel) slot hleftLength hrightLength]
          simp only [barringtonCompileSlot?]
          simp only [leftTarget, rightTarget] at hleftQuery hrightQuery
          simp only [hleftQuery, hrightQuery, hleftInverse, hrightInverse]
      | disj left right =>
          let innerTarget := target⁻¹
          let leftTarget := barringtonLeft innerTarget
          let rightTarget := barringtonRight innerTarget
          let leftBase :=
            barringtonCompileSlots fuel left leftTarget⁻¹
          let rightBase :=
            barringtonCompileSlots fuel right rightTarget⁻¹
          let leftSlots := leftBase.postMul leftTarget
          let rightSlots := rightBase.postMul rightTarget
          let commSlots := leftSlots ++ rightSlots ++ leftSlots.inverse ++
            rightSlots.inverse
          let leftQuery := barringtonPostMulSlot?
            (barringtonCompileSlot? fuel left leftTarget⁻¹)
            (barringtonLastOccupiedSlot? fuel left) leftTarget
          let rightQuery := barringtonPostMulSlot?
            (barringtonCompileSlot? fuel right rightTarget⁻¹)
            (barringtonLastOccupiedSlot? fuel right) rightTarget
          let commutatorQuery := fun localSlot =>
            if localSlot < 4 ^ fuel then
              leftQuery localSlot
            else if localSlot < 2 * 4 ^ fuel then
              rightQuery (localSlot - 4 ^ fuel)
            else if localSlot < 3 * 4 ^ fuel then
              barringtonInverseSlot? (4 ^ fuel) leftQuery
                (localSlot - 2 * 4 ^ fuel)
            else if localSlot < 4 * 4 ^ fuel then
              barringtonInverseSlot? (4 ^ fuel) rightQuery
                (localSlot - 3 * 4 ^ fuel)
            else
              none
          obtain ⟨hleftFirst, hleftLast⟩ :=
            barringtonOccupiedSlots_correct_internal
              fuel left leftTarget⁻¹
          obtain ⟨hrightFirst, hrightLast⟩ :=
            barringtonOccupiedSlots_correct_internal
              fuel right rightTarget⁻¹
          have hleftNe : leftBase ≠ [] := by
            exact barringtonCompileSlots_ne_nil_query_internal
              fuel left leftTarget⁻¹
          have hrightNe : rightBase ≠ [] := by
            exact barringtonCompileSlots_ne_nil_query_internal
              fuel right rightTarget⁻¹
          have hleftBaseQuery :
              barringtonCompileSlot? fuel left leftTarget⁻¹ =
                BPSlots.instruction? leftBase := by
            funext querySlot
            exact ih left leftTarget⁻¹ querySlot
          have hrightBaseQuery :
              barringtonCompileSlot? fuel right rightTarget⁻¹ =
                BPSlots.instruction? rightBase := by
            funext querySlot
            exact ih right rightTarget⁻¹ querySlot
          have hleftQuery : leftQuery =
              BPSlots.instruction? leftSlots := by
            funext querySlot
            simp only [leftQuery, leftSlots]
            rw [hleftBaseQuery, hleftLast]
            exact BPSlots.barringtonPostMulSlot?_correct_internal
              leftBase leftTarget querySlot hleftNe
          have hrightQuery : rightQuery =
              BPSlots.instruction? rightSlots := by
            funext querySlot
            simp only [rightQuery, rightSlots]
            rw [hrightBaseQuery, hrightLast]
            exact BPSlots.barringtonPostMulSlot?_correct_internal
              rightBase rightTarget querySlot hrightNe
          have hleftLength : leftSlots.length = 4 ^ fuel := by
            rw [BPSlots.length_postMul_internal]
            exact barringtonCompileSlots_length_internal
              fuel left leftTarget⁻¹
          have hrightLength : rightSlots.length = 4 ^ fuel := by
            rw [BPSlots.length_postMul_internal]
            exact barringtonCompileSlots_length_internal
              fuel right rightTarget⁻¹
          have hleftInverse (querySlot : ℕ) :
              barringtonInverseSlot? (4 ^ fuel)
                  (BPSlots.instruction? leftSlots) querySlot =
                BPSlots.instruction? leftSlots.inverse querySlot := by
            rw [← hleftLength]
            exact BPSlots.barringtonInverseSlot?_correct_internal
              leftSlots querySlot
          have hrightInverse (querySlot : ℕ) :
              barringtonInverseSlot? (4 ^ fuel)
                  (BPSlots.instruction? rightSlots) querySlot =
                BPSlots.instruction? rightSlots.inverse querySlot := by
            rw [← hrightLength]
            exact BPSlots.barringtonInverseSlot?_correct_internal
              rightSlots querySlot
          have hcommutatorQuery : commutatorQuery =
              BPSlots.instruction? commSlots := by
            funext querySlot
            simp only [commutatorQuery, hleftQuery, hrightQuery,
              hleftInverse, hrightInverse]
            rw [show commSlots =
              leftSlots ++ rightSlots ++ leftSlots.inverse ++
                rightSlots.inverse from rfl]
            exact (BPSlots.instruction?_fourBlocks_internal
              leftSlots rightSlots (4 ^ fuel) querySlot
              hleftLength hrightLength).symm
          have hrightSlotsFirst : BPSlots.firstOccupiedSlot? rightSlots =
              some ((BPSlots.firstOccupiedSlot? rightBase).getD 0) := by
            exact BPSlots.firstOccupiedSlot?_postMul_internal
              rightBase rightTarget hrightNe
          have hcommNe : commSlots ≠ [] := by
            intro hempty
            have hlength := congrArg List.length hempty
            simp [commSlots, hleftLength, hrightLength,
              BPSlots.length_inverse_internal] at hlength
          have hcommLastActual : BPSlots.lastOccupiedSlot? commSlots =
              some (3 * 4 ^ fuel +
                (4 ^ fuel - 1 -
                  (BPSlots.firstOccupiedSlot? rightBase).getD 0)) := by
            rw [show commSlots =
              (leftSlots ++ rightSlots ++ leftSlots.inverse) ++
                rightSlots.inverse by simp [commSlots, List.append_assoc]]
            rw [BPSlots.lastOccupiedSlot?_append_internal,
              BPSlots.lastOccupiedSlot?_inverse_internal,
              hrightSlotsFirst]
            simp only [Option.map_some]
            simp [hleftLength, hrightLength,
              BPSlots.length_inverse_internal]
            ring_nf
          have hcommLast :
              some (3 * 4 ^ fuel +
                (4 ^ fuel - 1 -
                  (barringtonFirstOccupiedSlot? fuel right).getD 0)) =
                BPSlots.lastOccupiedSlot? commSlots := by
            rw [hrightFirst, hcommLastActual]
          change barringtonPostMulSlot? commutatorQuery
              (some (3 * 4 ^ fuel +
                (4 ^ fuel - 1 -
                  (barringtonFirstOccupiedSlot? fuel right).getD 0)))
              target slot =
            BPSlots.instruction? (commSlots.postMul target) slot
          rw [hcommutatorQuery, hcommLast]
          exact BPSlots.barringtonPostMulSlot?_correct_internal
            commSlots target slot hcommNe

end Complexity
