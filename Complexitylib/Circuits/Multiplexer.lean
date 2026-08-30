/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Multiplexer.Defs
public import Complexitylib.Circuits.Multiplexer.Internal

/-!
# Fixed-width multiplexers

This module exposes a fan-in-two circuit selecting one of two fixed-width
payloads. The control bit chooses the left payload when true and the right
payload when false. The construction has exactly three gates per payload bit.
-/


public section

namespace Complexity

namespace Circuit

/-- Pointwise semantics on the multiplexer circuit's packed input. -/
theorem eval_multiplexer_packed (width : ℕ) [NeZero width]
    (input : BitString (1 + (width + width))) (coordinate : Fin width) :
    (multiplexer width).eval input coordinate =
      if input ⟨0, by omega⟩ then
        input ⟨1 + coordinate.val, by omega⟩
      else
        input ⟨1 + width + coordinate.val, by omega⟩ :=
  eval_multiplexer_packed_internal width input coordinate

/-- The multiplexer selects the left payload exactly when its control is true. -/
@[simp] theorem eval_multiplexer (width : ℕ) [NeZero width]
    (control : Bool) (left right : BitString width) :
    (multiplexer width).eval
        (BitString.multiplexerInput control left right) =
      if control then left else right :=
  eval_multiplexer_internal width control left right

/-- A `width`-bit multiplexer has exactly three gates per payload bit. -/
@[simp] theorem size_multiplexer (width : ℕ) [NeZero width] :
    (multiplexer width).size = 3 * width := by
  simp [Circuit.size]
  omega

end Circuit

end Complexity
