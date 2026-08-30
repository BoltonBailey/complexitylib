/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AndOrNot.Defs

/-!
# Fixed-width multiplexers -- definitions

A `width`-bit multiplexer consumes one control bit, a left payload, and a
right payload. Each output bit uses two internal AND gates and one output OR
gate. Free edge negation supplies the negated control edge.
-/


@[expose] public section

namespace Complexity

namespace BitString

/-- Canonical input order for a fixed-width multiplexer: control, left
payload, then right payload. -/
def multiplexerInput {width : ℕ} (control : Bool)
    (left right : BitString width) : BitString (1 + (width + width)) :=
  Fin.addCases (fun _ : Fin 1 => control) (Fin.append left right)

end BitString

namespace Circuit

/-- One internal conjunction in the multiplexer. The first block selects left
payload bits under the control; the second selects right payload bits under
the negated control. -/
def multiplexerInternalGate (width : ℕ) (index : Fin (width + width)) :
    {gate : Gate Basis.andOr2
        ((1 + (width + width)) + (width + width)) //
      ∀ input : Fin gate.fanIn,
        (gate.inputs input).val < 1 + (width + width) + index.val} := by
  if hleft : index.val < width then
    refine ⟨{
      op := .and
      fanIn := 2
      arityOk := rfl
      inputs := fun input =>
        if input.val = 0 then
          ⟨0, by omega⟩
        else
          ⟨1 + index.val, by omega⟩
      negated := fun _ => false
    }, ?_⟩
    intro input
    dsimp only
    split_ifs
    · change 0 < 1 + (width + width) + index.val
      omega
    · change 1 + index.val < 1 + (width + width) + index.val
      omega
  else
    refine ⟨{
      op := .and
      fanIn := 2
      arityOk := rfl
      inputs := fun input =>
        if input.val = 0 then
          ⟨0, by omega⟩
        else
          ⟨1 + width + (index.val - width), by omega⟩
      negated := fun input => input.val = 0
    }, ?_⟩
    intro input
    dsimp only
    split_ifs
    · change 0 < 1 + (width + width) + index.val
      omega
    · change 1 + width + (index.val - width) <
        1 + (width + width) + index.val
      omega

/-- Output disjunction joining the selected left and right contributions at
one payload coordinate. -/
def multiplexerOutputGate (width : ℕ) (coordinate : Fin width) :
    Gate Basis.andOr2 ((1 + (width + width)) + (width + width)) where
  op := .or
  fanIn := 2
  arityOk := rfl
  inputs := fun input =>
    if input.val = 0 then
      ⟨1 + (width + width) + coordinate.val, by omega⟩
    else
      ⟨1 + (width + width) + width + coordinate.val, by omega⟩
  negated := fun _ => false

/-- Fixed-width fan-in-two multiplexer. -/
def multiplexer (width : ℕ) [NeZero width] :
    Circuit Basis.andOr2 (1 + (width + width)) width (width + width) where
  gates index := (multiplexerInternalGate width index).val
  outputs coordinate := multiplexerOutputGate width coordinate
  acyclic index := (multiplexerInternalGate width index).property

end Circuit

end Complexity
