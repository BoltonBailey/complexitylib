/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.BinaryMinimum.Defs
public import Complexitylib.Circuits.BinaryMinimum.Internal

/-!
# Unsigned binary minimum

This module exposes a linear-size fan-in-two circuit that compares two
little-endian words and returns the word with smaller unsigned value.
-/


public section

namespace Complexity

namespace BitString

/-- Selecting the smaller word also selects the minimum unsigned value. -/
@[simp] theorem unsignedValue_unsignedMin {width : ℕ}
    (left right : BitString width) :
    (unsignedMin left right).unsignedValue =
      min left.unsignedValue right.unsignedValue :=
  unsignedValue_unsignedMin_internal left right

end BitString

namespace Circuit

/-- The comparator-with-payload circuit has exact linear size. -/
@[simp] theorem size_unsignedLEWithPayload (width : ℕ) [NeZero width] :
    (unsignedLEWithPayload width).size = 17 * width + 1 := by
  rw [unsignedLEWithPayload, Circuit.size_parallel,
    Circuit.size_unsignedLE, Circuit.size_projectInputs]
  omega

/-- Comparator-with-payload emits its decision bit before the original words. -/
@[simp] theorem eval_unsignedLEWithPayload (width : ℕ) [NeZero width]
    (left right : BitString width) :
    (unsignedLEWithPayload width).eval (Fin.append left right) =
      BitString.multiplexerInput
        (decide (left.unsignedValue ≤ right.unsignedValue)) left right :=
  eval_unsignedLEWithPayload_internal width left right

/-- The unsigned-minimum selector has exact linear size. -/
@[simp] theorem size_unsignedMin (width : ℕ) [NeZero width] :
    (unsignedMin width).size = 20 * width + 1 := by
  rw [unsignedMin, Circuit.size_compose,
    size_unsignedLEWithPayload, Circuit.size_multiplexer]
  omega

/-- The selector returns the smaller unsigned word, choosing left on ties. -/
@[simp] theorem eval_unsignedMin (width : ℕ) [NeZero width]
    (left right : BitString width) :
    (unsignedMin width).eval (Fin.append left right) =
      BitString.unsignedMin left right :=
  eval_unsignedMin_internal width left right

end Circuit

end Complexity
