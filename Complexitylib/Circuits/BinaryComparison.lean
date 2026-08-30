/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.ToCircuit
public import Complexitylib.Circuits.BinaryComparison.Defs
public import Complexitylib.Circuits.BinaryComparison.Internal

/-!
# Little-endian binary comparison

This module exposes unsigned semantics for fixed-width little-endian words, a
linear-size Boolean formula comparing two consecutive input words, and its
verified compilation to a typed fan-in-two circuit.
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

namespace CircuitCode

/-- Exact raw gate count for the unsigned-comparison construction. -/
@[simp] theorem length_unsignedLERawCircuit (width : ℕ) :
    (unsignedLERawCircuit width).length = 15 * width + 1 :=
  length_unsignedLERawCircuit_internal width

/-- The raw unsigned-comparison construction is a valid single-output circuit
for every positive word width. -/
theorem unsignedLERawCircuit_wellFormed (width : ℕ) [NeZero width] :
    (unsignedLERawCircuit width).WellFormed (width + width) :=
  unsignedLERawCircuit_wellFormed_internal width

end CircuitCode

namespace Circuit

/-- Typed fan-in-two circuit comparing two consecutive `width`-bit unsigned
little-endian words. -/
noncomputable def unsignedLE (width : ℕ) [NeZero width] :
    Circuit Basis.andOr2 (width + width) 1
      ((CircuitCode.unsignedLERawCircuit width).length - 1) :=
  (CircuitCode.unsignedLERawCircuit width).toCircuit (width + width)
    (CircuitCode.unsignedLERawCircuit_wellFormed_internal width)

/-- Exact size of the typed unsigned-comparison circuit. -/
@[simp] theorem size_unsignedLE (width : ℕ) [NeZero width] :
    (unsignedLE width).size = 15 * width + 1 := by
  rw [unsignedLE, CircuitCode.RawCircuit.size_toCircuit,
    CircuitCode.length_unsignedLERawCircuit_internal]

/-- The typed circuit returns the unsigned comparison of its two input words. -/
@[simp] theorem eval_unsignedLE (width : ℕ) [NeZero width]
    (left right : BitString width) :
    ((unsignedLE width).eval (Fin.append left right)) 0 =
      decide (left.unsignedValue ≤ right.unsignedValue) := by
  have hbridge := CircuitCode.RawCircuit.eval?_toCircuit (width + width)
    (CircuitCode.unsignedLERawCircuit width)
    (CircuitCode.unsignedLERawCircuit_wellFormed_internal width)
    (Fin.append left right)
  rw [CircuitCode.eval?_unsignedLERawCircuit_internal] at hbridge
  exact (Option.some.inj hbridge).symm

end Circuit

end Complexity
