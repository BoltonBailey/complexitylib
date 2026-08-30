/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.BinaryComparison.Defs
public import Complexitylib.Circuits.BinaryComparison.Internal

/-!
# Little-endian binary comparison

This module exposes unsigned semantics for fixed-width little-endian words and
a linear-size Boolean formula comparing two consecutive input words.
-/


public section

namespace Complexity

namespace BitString

/-- Recursive most-significant-bit comparison agrees with unsigned natural
comparison. -/
theorem unsignedLE_eq_decide {width : ℕ} (left right : BitString width) :
    unsignedLE left right =
      decide (left.unsignedValue ≤ right.unsignedValue) :=
  unsignedLE_eq_decide_internal left right

end BitString

namespace BoolFormula

/-- The unsigned-comparison formula has exactly fifteen nodes per input bit,
plus its base constant. -/
@[simp] theorem size_unsignedLE (width : ℕ) :
    (unsignedLE width).size = 15 * width + 1 :=
  size_unsignedLE_internal width

/-- The formula compares two consecutive fixed-width little-endian input
words as unsigned naturals. -/
@[simp] theorem eval_unsignedLE (width : ℕ)
    (left right : BitString width) :
    (unsignedLE width).eval
        (BitString.toTotal (Fin.append left right)) =
      decide (left.unsignedValue ≤ right.unsignedValue) :=
  eval_unsignedLE_internal width left right

end BoolFormula

end Complexity
