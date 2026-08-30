/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.KeyedMinimum.Defs
public import Complexitylib.Circuits.KeyedMinimum.Internal

/-!
# Keyed unsigned minimum

This module exposes a linear-size selector that compares two unsigned keys and
returns the winning key with its associated payload.
-/


public section

namespace Complexity

namespace Circuit

/-- Comparator-with-records has exact size linear in key and payload widths. -/
@[simp] theorem size_unsignedLEWithKeyedPayload
    (keyWidth payloadWidth : ℕ) [NeZero keyWidth] :
    (unsignedLEWithKeyedPayload keyWidth payloadWidth).size =
      17 * keyWidth + 2 * payloadWidth + 1 := by
  rw [unsignedLEWithKeyedPayload, Circuit.size_parallel,
    Circuit.size_reindexInputs, Circuit.size_unsignedLE,
    Circuit.size_projectInputs]
  omega

/-- Comparator-with-records emits its decision before the two complete records. -/
@[simp] theorem eval_unsignedLEWithKeyedPayload
    (keyWidth payloadWidth : ℕ) [NeZero keyWidth]
    (leftKey : BitString keyWidth) (leftPayload : BitString payloadWidth)
    (rightKey : BitString keyWidth) (rightPayload : BitString payloadWidth) :
    (unsignedLEWithKeyedPayload keyWidth payloadWidth).eval
        (BitString.keyedMinimumInput
          leftKey leftPayload rightKey rightPayload) =
      BitString.multiplexerInput
        (decide (leftKey.unsignedValue ≤ rightKey.unsignedValue))
        (Fin.append leftKey leftPayload) (Fin.append rightKey rightPayload) :=
  eval_unsignedLEWithKeyedPayload_internal keyWidth payloadWidth
    leftKey leftPayload rightKey rightPayload

/-- The keyed selector has exact size linear in key and payload widths. -/
@[simp] theorem size_unsignedKeyedMin
    (keyWidth payloadWidth : ℕ) [NeZero keyWidth] :
    (unsignedKeyedMin keyWidth payloadWidth).size =
      20 * keyWidth + 5 * payloadWidth + 1 := by
  rw [unsignedKeyedMin, Circuit.size_compose,
    size_unsignedLEWithKeyedPayload, Circuit.size_multiplexer]
  omega

/-- The selector returns the record with smaller key, choosing left on ties. -/
@[simp] theorem eval_unsignedKeyedMin
    (keyWidth payloadWidth : ℕ) [NeZero keyWidth]
    (leftKey : BitString keyWidth) (leftPayload : BitString payloadWidth)
    (rightKey : BitString keyWidth) (rightPayload : BitString payloadWidth) :
    (unsignedKeyedMin keyWidth payloadWidth).eval
        (BitString.keyedMinimumInput
          leftKey leftPayload rightKey rightPayload) =
      BitString.unsignedKeyedMin leftKey leftPayload rightKey rightPayload :=
  eval_unsignedKeyedMin_internal keyWidth payloadWidth
    leftKey leftPayload rightKey rightPayload

end Circuit

end Complexity
