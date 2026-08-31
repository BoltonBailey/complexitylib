/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Validity.Defs
public import Complexitylib.Circuits.Encoding.FixedWidth.Validity.Internal

/-!
# Fixed-width description validity formulas

This module exposes the exact semantics, tree size, and variable support of
the structural-validity formula for bounded fixed-width circuit descriptions.
-/


public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace Description

namespace ValidityFormula

/-- The validity formula accepts exactly codes that decode to a structurally
valid fixed-width circuit description. -/
@[simp] theorem eval_wellFormed (inputWidth gateBound : Nat)
    (code : BitString (codeWidth inputWidth gateBound)) :
    (wellFormed inputWidth gateBound).eval code.toTotal =
      decide (EncodedWellFormed code) :=
  eval_wellFormed_internal inputWidth gateBound code

/-- Exact tree size of the complete fixed-width validity formula. -/
@[simp] theorem size_wellFormed (inputWidth gateBound : Nat) :
    (wellFormed inputWidth gateBound).size =
      wellFormedSize inputWidth gateBound :=
  size_wellFormed_internal inputWidth gateBound

/-- Every variable in the validity formula addresses one bit of the incoming
fixed-width description code. -/
theorem vars_wellFormed_lt (inputWidth gateBound : Nat) :
    ∀ wire ∈ (wellFormed inputWidth gateBound).vars,
      wire < codeWidth inputWidth gateBound :=
  vars_wellFormed_lt_internal inputWidth gateBound

end ValidityFormula

end Description

end FixedWidth

end CircuitCode

end Complexity
