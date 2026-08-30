/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Multiplexer.Defs

/-!
# Fixed-width multiplexers -- proof internals
-/


public section

namespace Complexity

namespace Circuit

theorem wireValue_multiplexer_left_internal (width : ℕ) [NeZero width]
    (input : BitString (1 + (width + width))) (coordinate : Fin width) :
    (multiplexer width).wireValue input
        ⟨1 + (width + width) + coordinate.val, by omega⟩ =
      (input ⟨0, by omega⟩ && input ⟨1 + coordinate.val, by omega⟩) := by
  have hnot : ¬(⟨1 + (width + width) + coordinate.val, by omega⟩ :
      Fin ((1 + (width + width)) + (width + width))).val <
        1 + (width + width) := by
    change ¬(1 + (width + width) + coordinate.val < 1 + (width + width))
    omega
  rw [Circuit.wireValue_of_not_lt _ _ _ hnot]
  have hindex :
      (⟨(1 + (width + width) + coordinate.val) -
          (1 + (width + width)), by omega⟩ : Fin (width + width)) =
        Fin.castAdd width coordinate := by
    apply Fin.ext
    simp
  rw [hindex]
  change (multiplexerInternalGate width
      (Fin.castAdd width coordinate)).val.eval
        ((multiplexer width).wireValue input) = _
  unfold multiplexerInternalGate
  have hleft : (Fin.castAdd width coordinate).val < width := coordinate.isLt
  rw [dif_pos hleft]
  unfold Gate.eval
  change AndOrOp.eval .and 2 _ = _
  rw [AndOrOp.eval_two_and]
  dsimp only
  simp only [Bool.false_xor]
  rw [if_pos (by omega : (0 : Fin 2).val = 0)]
  rw [if_neg (by omega : ¬(1 : Fin 2).val = 0)]
  rw [Circuit.wireValue_of_lt _ _ _ (by simp; omega)]
  rw [Circuit.wireValue_of_lt _ _ _ (by simp; omega)]
  simp

theorem wireValue_multiplexer_right_internal (width : ℕ) [NeZero width]
    (input : BitString (1 + (width + width))) (coordinate : Fin width) :
    (multiplexer width).wireValue input
        ⟨1 + (width + width) + width + coordinate.val, by omega⟩ =
      (!input ⟨0, by omega⟩ &&
        input ⟨1 + width + coordinate.val, by omega⟩) := by
  have hnot : ¬(⟨1 + (width + width) + width + coordinate.val, by omega⟩ :
      Fin ((1 + (width + width)) + (width + width))).val <
        1 + (width + width) := by
    change ¬(1 + (width + width) + width + coordinate.val <
      1 + (width + width))
    omega
  rw [Circuit.wireValue_of_not_lt _ _ _ hnot]
  have hindex :
      (⟨(1 + (width + width) + width + coordinate.val) -
          (1 + (width + width)), by omega⟩ : Fin (width + width)) =
        Fin.natAdd width coordinate := by
    apply Fin.ext
    simp
    omega
  rw [hindex]
  change (multiplexerInternalGate width
      (Fin.natAdd width coordinate)).val.eval
        ((multiplexer width).wireValue input) = _
  unfold multiplexerInternalGate
  have hright : ¬(Fin.natAdd width coordinate).val < width := by
    simp
  rw [dif_neg hright]
  unfold Gate.eval
  change AndOrOp.eval .and 2 _ = _
  rw [AndOrOp.eval_two_and]
  dsimp only
  rw [if_pos (by omega : (0 : Fin 2).val = 0)]
  rw [if_neg (by omega : ¬(1 : Fin 2).val = 0)]
  rw [Circuit.wireValue_of_lt _ _ _ (by simp; omega)]
  rw [Circuit.wireValue_of_lt _ _ _ (by simp; omega)]
  simp

theorem eval_multiplexer_packed_internal (width : ℕ) [NeZero width]
    (input : BitString (1 + (width + width))) (coordinate : Fin width) :
    (multiplexer width).eval input coordinate =
      if input ⟨0, by omega⟩ then
        input ⟨1 + coordinate.val, by omega⟩
      else
        input ⟨1 + width + coordinate.val, by omega⟩ := by
  unfold Circuit.eval
  change (multiplexerOutputGate width coordinate).eval
      ((multiplexer width).wireValue input) = _
  unfold Gate.eval multiplexerOutputGate
  change AndOrOp.eval .or 2 _ = _
  rw [AndOrOp.eval_two_or]
  dsimp only
  simp only [Bool.false_xor]
  rw [if_pos (by omega : (0 : Fin 2).val = 0)]
  rw [if_neg (by omega : ¬(1 : Fin 2).val = 0)]
  rw [wireValue_multiplexer_left_internal]
  rw [wireValue_multiplexer_right_internal]
  cases input ⟨0, by omega⟩ <;> simp

theorem eval_multiplexer_internal (width : ℕ) [NeZero width]
    (control : Bool) (left right : BitString width) :
    (multiplexer width).eval
        (BitString.multiplexerInput control left right) =
      if control then left else right := by
  funext coordinate
  rw [eval_multiplexer_packed_internal]
  cases control <;>
    simp [BitString.multiplexerInput, Fin.append, Fin.addCases]
  rw [dif_neg (by omega)]
  apply congrArg right
  apply Fin.ext
  simp
  omega

end Circuit

end Complexity
