/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.BinaryComparison.Defs

/-!
# Little-endian binary comparison -- proof internals
-/


public section

namespace Complexity

private theorem fromBitsLE_concat (bits : List Bool) (bit : Bool) :
    Nat.fromBitsLE (bits.concat bit) =
      Nat.fromBitsLE bits + if bit then 2 ^ bits.length else 0 := by
  cases bit with
  | false => simp [Nat.fromBitsLE, Nat.fromBits]
  | true =>
      simp [Nat.fromBitsLE, Nat.fromBits]
      omega

namespace BitString

theorem unsignedLE_eq_decide_internal {width : ℕ}
    (left right : BitString width) :
    unsignedLE left right =
      decide (left.unsignedValue ≤ right.unsignedValue) := by
  induction width with
  | zero =>
      simp [unsignedLE, unsignedValue, BitString.toList,
        Nat.fromBitsLE, Nat.fromBits]
  | succ width ih =>
      let leftLow : BitString width := fun i => left i.castSucc
      let rightLow : BitString width := fun i => right i.castSucc
      have hleftBound : leftLow.unsignedValue < 2 ^ width := by
        unfold unsignedValue
        simpa using Nat.fromBitsLE_lt_pow_length leftLow.toList
      have hrightBound : rightLow.unsignedValue < 2 ^ width := by
        unfold unsignedValue
        simpa using Nat.fromBitsLE_lt_pow_length rightLow.toList
      change Nat.fromBitsLE leftLow.toList < 2 ^ width at hleftBound
      change Nat.fromBitsLE rightLow.toList < 2 ^ width at hrightBound
      have hleftList : left.toList = leftLow.toList.concat (left (Fin.last width)) := by
        simpa [leftLow, BitString.toList] using List.ofFn_succ' left
      have hrightList : right.toList =
          rightLow.toList.concat (right (Fin.last width)) := by
        simpa [rightLow, BitString.toList] using List.ofFn_succ' right
      rw [unsignedValue, unsignedValue, hleftList, hrightList,
        fromBitsLE_concat, fromBitsLE_concat]
      change
        ((!left (Fin.last width) && right (Fin.last width)) ||
          ((left (Fin.last width) == right (Fin.last width)) &&
            unsignedLE leftLow rightLow)) = _
      rw [ih leftLow rightLow]
      cases hleft : left (Fin.last width) <;>
        cases hright : right (Fin.last width)
      · simp [BitString.unsignedValue]
      · simp [BitString.unsignedValue]
        omega
      · simp [BitString.unsignedValue]
        omega
      · simp [BitString.unsignedValue]

end BitString

namespace BoolFormula

theorem size_unsignedLEAux_internal (width leftBase rightBase : ℕ) :
    (unsignedLEAux width leftBase rightBase).size = 15 * width + 1 := by
  induction width with
  | zero => rfl
  | succ width ih =>
      simp only [unsignedLEAux, BoolFormula.size, ih]
      omega

theorem size_unsignedLE_internal (width : ℕ) :
    (unsignedLE width).size = 15 * width + 1 :=
  size_unsignedLEAux_internal width 0 width

theorem eval_unsignedLEAux_internal (width leftBase rightBase : ℕ)
    (assignment : ℕ → Bool) (left right : BitString width)
    (hleft : ∀ i, assignment (leftBase + i.val) = left i)
    (hright : ∀ i, assignment (rightBase + i.val) = right i) :
    (unsignedLEAux width leftBase rightBase).eval assignment =
      BitString.unsignedLE left right := by
  induction width with
  | zero => rfl
  | succ width ih =>
      let leftLow : BitString width := fun i => left i.castSucc
      let rightLow : BitString width := fun i => right i.castSucc
      have hleftHigh := hleft (Fin.last width)
      have hrightHigh := hright (Fin.last width)
      have hleftHigh' :
          assignment (leftBase + width) = left (Fin.last width) := by
        simpa using hleftHigh
      have hrightHigh' :
          assignment (rightBase + width) = right (Fin.last width) := by
        simpa using hrightHigh
      have hlow := ih leftLow rightLow
        (fun i => hleft i.castSucc) (fun i => hright i.castSucc)
      simp only [unsignedLEAux, BoolFormula.eval]
      change
        ((!assignment (leftBase + width) &&
            assignment (rightBase + width)) ||
          (((assignment (leftBase + width) &&
              assignment (rightBase + width)) ||
            (!assignment (leftBase + width) &&
              !assignment (rightBase + width))) &&
            (unsignedLEAux width leftBase rightBase).eval assignment)) = _
      rw [hleftHigh', hrightHigh', hlow]
      change
        ((!left (Fin.last width) && right (Fin.last width)) ||
          (((left (Fin.last width) && right (Fin.last width)) ||
            (!left (Fin.last width) && !right (Fin.last width))) &&
            BitString.unsignedLE leftLow rightLow)) =
          ((!left (Fin.last width) && right (Fin.last width)) ||
            ((left (Fin.last width) == right (Fin.last width)) &&
              BitString.unsignedLE leftLow rightLow))
      cases left (Fin.last width) <;> cases right (Fin.last width) <;>
        rfl

theorem eval_unsignedLE_internal (width : ℕ)
    (left right : BitString width) :
    (unsignedLE width).eval
        (BitString.toTotal (Fin.append left right)) =
      decide (left.unsignedValue ≤ right.unsignedValue) := by
  rw [unsignedLE]
  rw [eval_unsignedLEAux_internal width 0 width
    (BitString.toTotal (Fin.append left right)) left right]
  · exact BitString.unsignedLE_eq_decide_internal left right
  · intro i
    simp only [Nat.zero_add]
    rw [BitString.toTotal_of_lt _ i.val (by omega)]
    have hindex :
        (⟨i.val, by omega⟩ : Fin (width + width)) =
          Fin.castAdd width i := by
      apply Fin.ext
      rfl
    rw [hindex, Fin.append_left]
  · intro i
    rw [BitString.toTotal_of_lt _ (width + i.val) (by omega)]
    have hindex :
        (⟨width + i.val, by omega⟩ : Fin (width + width)) =
          Fin.natAdd width i := by
      apply Fin.ext
      rfl
    rw [hindex, Fin.append_right]

end BoolFormula

end Complexity
