/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.BinaryMinimum.Defs
public import Complexitylib.Circuits.Composition
public import Complexitylib.Circuits.InputProjection
public import Complexitylib.Circuits.Multiplexer

/-!
# Unsigned binary minimum -- proof internals
-/


public section

namespace Complexity

namespace BitString

theorem unsignedValue_unsignedMin_internal {width : ℕ}
    (left right : BitString width) :
    (unsignedMin left right).unsignedValue =
      min left.unsignedValue right.unsignedValue := by
  unfold unsignedMin
  rw [Nat.min_def]
  split_ifs <;> rfl

end BitString

namespace Circuit

theorem eval_unsignedLEWithPayload_internal (width : ℕ) [NeZero width]
    (left right : BitString width) :
    (unsignedLEWithPayload width).eval (Fin.append left right) =
      BitString.multiplexerInput
        (decide (left.unsignedValue ≤ right.unsignedValue)) left right := by
  unfold unsignedLEWithPayload
  rw [Circuit.eval_parallel]
  rw [Circuit.eval_projectInputs]
  funext index
  refine Fin.addCases ?_ ?_ index
  · intro comparison
    have hcomparison : comparison = 0 := Subsingleton.elim _ _
    subst comparison
    simp [BitString.multiplexerInput]
  · intro payload
    simp [BitString.multiplexerInput, Function.comp_def]

theorem eval_unsignedMin_internal (width : ℕ) [NeZero width]
    (left right : BitString width) :
    (unsignedMin width).eval (Fin.append left right) =
      BitString.unsignedMin left right := by
  unfold unsignedMin
  rw [Circuit.eval_compose]
  rw [eval_unsignedLEWithPayload_internal]
  rw [Circuit.eval_multiplexer]
  simp [BitString.unsignedMin]

end Circuit

end Complexity
