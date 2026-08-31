/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.BitString
public import Complexitylib.Circuits.Encoding.Fragment.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Ring.BooleanRing

/-!
# Raw parity-circuit fragments -- definitions

This module builds an appendable fan-in-two circuit for the XOR of selected
existing wires. One false initializer and three gates per selected wire give a
linear construction that retains sharing, unlike expansion into a Boolean
formula tree.
-/


@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Parity

/-- XOR of a fixed-width Boolean vector, defined from its first coordinate
toward its last coordinate. -/
def foldXor : (count : ℕ) → (Fin count → Bool) → Bool
  | 0, _ => false
  | count + 1, bits => (bits 0).xor (foldXor count (fun i => bits i.succ))

/-- Accumulator wire before processing the selected wire at `step`. -/
def accumulatorWire (available step : ℕ) : ℕ :=
  available + 3 * step

/-- First wire emitted while folding one selected bit into the accumulator. -/
def orWire (available step : ℕ) : ℕ :=
  available + 1 + 3 * step

/-- Second wire emitted while folding one selected bit into the accumulator. -/
def andWire (available step : ℕ) : ℕ :=
  orWire available step + 1

/-- The three gates computing `accumulator XOR input` with shared
intermediates. -/
def xorGates (available step input : ℕ) : RawCircuit :=
  [{ op := .or
     input₀ := accumulatorWire available step
     input₁ := input
     negated₀ := false
     negated₁ := false },
   { op := .and
     input₀ := accumulatorWire available step
     input₁ := input
     negated₀ := false
     negated₁ := false },
   { op := .and
     input₀ := orWire available step
     input₁ := andWire available step
     negated₀ := false
     negated₁ := true }]

/-- Process successive selected wires, starting at the supplied fold step. -/
def steps (available step : ℕ) :
    (count : ℕ) → (Fin count → ℕ) → RawCircuit
  | 0, _ => []
  | count + 1, refs =>
      xorGates available step (refs 0) ++
        steps available (step + 1) count (fun i => refs i.succ)

/-- Absolute wire carrying the final parity value. -/
def outputWire (available inputCount : ℕ) : ℕ :=
  accumulatorWire available inputCount

/-- Compile the XOR of selected existing wires as an appendable raw fragment.

The fragment first creates a false accumulator and then uses three shared
gates per selected wire. -/
def compileRaw (available : ℕ) {inputCount : ℕ}
    (refs : Fin inputCount → ℕ) : RawCircuit :=
  [RawGate.constant 0 false] ++ steps available 0 inputCount refs

end Parity

end CircuitCode

end Complexity
