/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Lookup.Defs
public import Complexitylib.Circuits.Encoding.FixedWidth.Lookup.Internal

/-!
# Fixed-width binary-reference lookup formulas

This module exposes semantics, exact size, and support bounds for selecting a
one-bit source with a fixed-width little-endian formula word.
-/


public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace LookupFormula

/-- A formula-word equality test agrees with extensional bit-string equality. -/
@[simp] theorem eval_wordEqual {width : Nat}
    (word : Fin width → BoolFormula) (value : BitString width)
    (assignment : Nat → Bool) :
    (wordEqual word value).eval assignment =
      decide (evaluatedWord word assignment = value) :=
  eval_wordEqual_internal word value assignment

/-- Lookup returns the selected source exactly when the unsigned reference is
in range, and false otherwise. -/
theorem eval_select {width count : Nat}
    (word : Fin width → BoolFormula)
    (values : Fin count → BoolFormula) (assignment : Nat → Bool)
    (hcount : count ≤ 2 ^ width) :
    (select word values).eval assignment =
      if hvalue : (evaluatedWord word assignment).unsignedValue < count then
        (values ⟨(evaluatedWord word assignment).unsignedValue,
          hvalue⟩).eval assignment
      else
        false :=
  eval_select_internal word values assignment hcount

/-- Exact lookup-formula size for one-node word bits and sources. -/
theorem size_select {width count : Nat}
    (word : Fin width → BoolFormula)
    (values : Fin count → BoolFormula)
    (hword : ∀ coordinate, (word coordinate).size = 1)
    (hvalues : ∀ index, (values index).size = 1) :
    (select word values).size = selectSize width count :=
  size_select_internal word values hword hvalues

/-- Lookup support stays inside any prefix containing every word bit and
source formula. -/
theorem vars_select_lt {width count available : Nat}
    (word : Fin width → BoolFormula)
    (values : Fin count → BoolFormula)
    (hword : ∀ coordinate wire,
      wire ∈ (word coordinate).vars → wire < available)
    (hvalues : ∀ index wire,
      wire ∈ (values index).vars → wire < available) :
    ∀ wire ∈ (select word values).vars, wire < available :=
  vars_select_lt_internal word values hword hvalues

end LookupFormula

end FixedWidth

end CircuitCode

end Complexity
