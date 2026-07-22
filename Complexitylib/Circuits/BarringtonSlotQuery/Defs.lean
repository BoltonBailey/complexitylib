/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonSlots.Defs

/-!
# Direct queries into fixed-address Barrington slots -- definitions

The list-valued fixed-slot compiler is the extensional reference for uniform
generation, but a log-space controller must locate one slot without building
the full list. This file gives structural first/last occupied-slot recurrences
and a direct indexed query. Every recursive query descends under a strictly
smaller fuel bound; inverse blocks reverse the local address, while `postMul`
uses the structural last occupied address.
-/

namespace Complexity

namespace BPSlots

/-- Occupied instruction at a zero-based fixed-slot address. -/
def instruction? (slots : BPSlots w) (slot : ℕ) : Option (BPInstr w) :=
  slots[slot]?.join

/-- First occupied fixed-slot address, if one exists. -/
def firstOccupiedSlot? : BPSlots w → Option ℕ
  | [] => none
  | none :: slots => (firstOccupiedSlot? slots).map Nat.succ
  | some _ :: _ => some 0

/-- Last occupied fixed-slot address, if one exists. -/
def lastOccupiedSlot? : BPSlots w → Option ℕ
  | [] => none
  | slot :: slots =>
      match lastOccupiedSlot? slots with
      | some last => some (last + 1)
      | none => if slot.isSome then some 0 else none

end BPSlots

/-- Apply fixed-schedule `postMul` to one direct slot query. A missing last
occupied address means the underlying schedule is empty, so the wrapper places
its constant instruction in slot zero. -/
def barringtonPostMulSlot? (query : ℕ → Option (BPInstr 5))
    (lastOccupied : Option ℕ) (permutation : Equiv.Perm (Fin 5))
    (slot : ℕ) : Option (BPInstr 5) :=
  match lastOccupied with
  | none => if slot = 0 then some (BPInstr.const permutation) else none
  | some last =>
      (query slot).map fun instruction =>
        if slot = last then instruction.postMul permutation else instruction

/-- Query an inverse block of fixed size without constructing it. -/
def barringtonInverseSlot? (blockSize : ℕ)
    (query : ℕ → Option (BPInstr 5)) (slot : ℕ) :
    Option (BPInstr 5) :=
  if slot < blockSize then
    (query (blockSize - 1 - slot)).map BPInstr.inverse
  else
    none

/-- First occupied slot of the fixed-address compilation, if any. Occupancy is
independent of the target permutation. -/
def barringtonFirstOccupiedSlot? : ℕ → BoolFormula → Option ℕ
  | _, .var _ | _, .tru => some 0
  | _, .fls => none
  | 0, .neg _ | 0, .conj _ _ | 0, .disj _ _ => none
  | fuel + 1, .neg formula =>
      some ((barringtonFirstOccupiedSlot? fuel formula).getD 0)
  | fuel + 1, .conj left right =>
      match barringtonFirstOccupiedSlot? fuel left with
      | some slot => some slot
      | none =>
          (barringtonFirstOccupiedSlot? fuel right).map
            (4 ^ fuel + ·)
  | fuel + 1, .disj left _ =>
      some ((barringtonFirstOccupiedSlot? fuel left).getD 0)

/-- Last occupied slot of the fixed-address compilation, if any. Inverse
blocks turn a child's first occupied address into the block's last one. -/
def barringtonLastOccupiedSlot? : ℕ → BoolFormula → Option ℕ
  | _, .var _ | _, .tru => some 0
  | _, .fls => none
  | 0, .neg _ | 0, .conj _ _ | 0, .disj _ _ => none
  | fuel + 1, .neg formula =>
      some ((barringtonLastOccupiedSlot? fuel formula).getD 0)
  | fuel + 1, .conj left right =>
      let blockSize := 4 ^ fuel
      match barringtonFirstOccupiedSlot? fuel right with
      | some slot => some (3 * blockSize + (blockSize - 1 - slot))
      | none =>
          (barringtonFirstOccupiedSlot? fuel left).map fun slot =>
            2 * blockSize + (blockSize - 1 - slot)
  | fuel + 1, .disj _ right =>
      let blockSize := 4 ^ fuel
      let firstRight :=
        (barringtonFirstOccupiedSlot? fuel right).getD 0
      some (3 * blockSize + (blockSize - 1 - firstRight))

/-- Directly query one fixed-address compilation slot. This follows only the
selected base-four block. The finite permutation data and pending instruction
transformations can therefore live in a concrete controller's finite state. -/
def barringtonCompileSlot? : ℕ → BoolFormula →
    Equiv.Perm (Fin 5) → ℕ → Option (BPInstr 5)
  | _, .var index, target, slot =>
      if slot = 0 then some ⟨index, 1, target⟩ else none
  | _, .tru, target, slot =>
      if slot = 0 then some (BPInstr.const target) else none
  | _, .fls, _, _ => none
  | 0, .neg _, _, _ | 0, .conj _ _, _, _ | 0, .disj _ _, _, _ => none
  | fuel + 1, .neg formula, target, slot =>
      let blockSize := 4 ^ fuel
      if slot < blockSize then
        barringtonPostMulSlot?
          (barringtonCompileSlot? fuel formula target⁻¹)
          (barringtonLastOccupiedSlot? fuel formula) target slot
      else
        none
  | fuel + 1, .conj left right, target, slot =>
      let blockSize := 4 ^ fuel
      let leftQuery :=
        barringtonCompileSlot? fuel left (barringtonLeft target)
      let rightQuery :=
        barringtonCompileSlot? fuel right (barringtonRight target)
      if slot < blockSize then
        leftQuery slot
      else if slot < 2 * blockSize then
        rightQuery (slot - blockSize)
      else if slot < 3 * blockSize then
        barringtonInverseSlot? blockSize leftQuery
          (slot - 2 * blockSize)
      else if slot < 4 * blockSize then
        barringtonInverseSlot? blockSize rightQuery
          (slot - 3 * blockSize)
      else
        none
  | fuel + 1, .disj left right, target, slot =>
      let blockSize := 4 ^ fuel
      let innerTarget := target⁻¹
      let leftTarget := barringtonLeft innerTarget
      let rightTarget := barringtonRight innerTarget
      let leftQuery := barringtonPostMulSlot?
        (barringtonCompileSlot? fuel left leftTarget⁻¹)
        (barringtonLastOccupiedSlot? fuel left) leftTarget
      let rightQuery := barringtonPostMulSlot?
        (barringtonCompileSlot? fuel right rightTarget⁻¹)
        (barringtonLastOccupiedSlot? fuel right) rightTarget
      let commutatorQuery := fun localSlot =>
        if localSlot < blockSize then
          leftQuery localSlot
        else if localSlot < 2 * blockSize then
          rightQuery (localSlot - blockSize)
        else if localSlot < 3 * blockSize then
          barringtonInverseSlot? blockSize leftQuery
            (localSlot - 2 * blockSize)
        else if localSlot < 4 * blockSize then
          barringtonInverseSlot? blockSize rightQuery
            (localSlot - 3 * blockSize)
        else
          none
      let firstRight :=
        (barringtonFirstOccupiedSlot? fuel right).getD 0
      let commutatorLast :=
        3 * blockSize + (blockSize - 1 - firstRight)
      barringtonPostMulSlot? commutatorQuery (some commutatorLast)
        target slot

end Complexity
