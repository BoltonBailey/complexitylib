/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.BinaryComparison.Defs
public import Complexitylib.Circuits.Encoding.FixedWidth.Conversion.Defs
public import Complexitylib.Circuits.Encoding.Formula.Batch.Defs

/-!
# Fixed-width binary-reference lookup formulas -- definitions

A lookup formula interprets a little-endian formula word as an index into a
finite family of one-bit source formulas. It disjoins one equality-guarded
source per index. Out-of-range words select no source and therefore evaluate
to false.

This construction is deliberately formula-level: clients may name primary
input wires and already-emitted gate wires uniformly before compiling the
result as the next appendable raw-circuit fragment.
-/


@[expose] public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace LookupFormula

/-- Evaluate a vector of bit formulas as one fixed-width word. -/
def evaluatedWord {width : Nat} (word : Fin width → BoolFormula)
    (assignment : Nat → Bool) : BitString width :=
  fun coordinate => (word coordinate).eval assignment

/-- Equality test between a formula word and one constant bit string. -/
def wordEqual {width : Nat} (word : Fin width → BoolFormula)
    (value : BitString width) : BoolFormula :=
  .conj
    (BoolFormula.unsignedLEOf word
      (fun coordinate => BoolFormula.ofBool (value coordinate)))
    (BoolFormula.unsignedLEOf
      (fun coordinate => BoolFormula.ofBool (value coordinate)) word)

/-- Equality-guarded source formula for one candidate index. -/
def candidate {width count : Nat}
    (word : Fin width → BoolFormula)
    (values : Fin count → BoolFormula) (index : Fin count) : BoolFormula :=
  .conj
    (wordEqual word (GateSlot.referenceBits width index.val))
    (values index)

/-- Select the source named by a fixed-width binary formula word. Words whose
unsigned value is outside `count` select no source and return false. -/
def select {width count : Nat}
    (word : Fin width → BoolFormula)
    (values : Fin count → BoolFormula) : BoolFormula :=
  BoolFormula.disjs <| List.ofFn fun index => candidate word values index

/-- Exact tree size of `select` when every input bit and source is a one-node
formula. -/
def selectSize (width count : Nat) : Nat :=
  1 + count * (30 * width + 6)

end LookupFormula

end FixedWidth

end CircuitCode

end Complexity
