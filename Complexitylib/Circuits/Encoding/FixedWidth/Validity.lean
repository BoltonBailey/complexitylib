/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Validity.Defs
public import Complexitylib.Circuits.Encoding.FixedWidth.Validity.Internal
public import Complexitylib.Circuits.Encoding.ToCircuit

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

/-- Formula compilation preserves the exact validity-formula size. -/
@[simp] theorem length_compileRaw (inputWidth gateBound : Nat) :
    (compileRaw inputWidth gateBound).length =
      wellFormedSize inputWidth gateBound :=
  length_compileRaw_internal inputWidth gateBound

/-- The compiled validity formula is a valid single-output raw circuit. -/
theorem compileRaw_wellFormed (inputWidth gateBound : Nat) :
    (compileRaw inputWidth gateBound).WellFormed
      (codeWidth inputWidth gateBound) :=
  compileRaw_wellFormed_internal inputWidth gateBound

/-- Raw evaluation accepts exactly structurally valid fixed-width codes. -/
@[simp] theorem eval?_compileRaw (inputWidth gateBound : Nat)
    (code : BitString (codeWidth inputWidth gateBound)) :
    (compileRaw inputWidth gateBound).eval? code.toList =
      some (decide (EncodedWellFormed code)) :=
  eval?_compileRaw_internal inputWidth gateBound code

end ValidityFormula

end Description

end FixedWidth

end CircuitCode

namespace Circuit

/-- Typed fan-in-two circuit deciding structural validity of a fixed-width
circuit description code. -/
noncomputable def fixedWidthDescriptionValidity
    (inputWidth gateBound : Nat) :
    Circuit Basis.andOr2
      (CircuitCode.FixedWidth.codeWidth inputWidth gateBound) 1
      ((CircuitCode.FixedWidth.Description.ValidityFormula.compileRaw
        inputWidth gateBound).length - 1) :=
  (CircuitCode.FixedWidth.Description.ValidityFormula.compileRaw
    inputWidth gateBound).toCircuit
      (CircuitCode.FixedWidth.codeWidth inputWidth gateBound)
      (CircuitCode.FixedWidth.Description.ValidityFormula.compileRaw_wellFormed_internal
        inputWidth gateBound)

/-- Exact size of the typed fixed-width description-validity circuit. -/
@[simp] theorem size_fixedWidthDescriptionValidity
    (inputWidth gateBound : Nat) :
    (fixedWidthDescriptionValidity inputWidth gateBound).size =
      CircuitCode.FixedWidth.Description.ValidityFormula.wellFormedSize
        inputWidth gateBound := by
  rw [fixedWidthDescriptionValidity,
    CircuitCode.RawCircuit.size_toCircuit,
    CircuitCode.FixedWidth.Description.ValidityFormula.length_compileRaw_internal]

/-- The typed circuit accepts exactly structurally valid fixed-width codes. -/
@[simp] theorem eval_fixedWidthDescriptionValidity
    (inputWidth gateBound : Nat)
    (code : BitString
      (CircuitCode.FixedWidth.codeWidth inputWidth gateBound)) :
    ((fixedWidthDescriptionValidity inputWidth gateBound).eval code) 0 =
      decide (CircuitCode.FixedWidth.Description.EncodedWellFormed code) := by
  have hbridge := CircuitCode.RawCircuit.eval?_toCircuit
    (CircuitCode.FixedWidth.codeWidth inputWidth gateBound)
    (CircuitCode.FixedWidth.Description.ValidityFormula.compileRaw
      inputWidth gateBound)
    (CircuitCode.FixedWidth.Description.ValidityFormula.compileRaw_wellFormed_internal
      inputWidth gateBound) code
  rw [CircuitCode.FixedWidth.Description.ValidityFormula.eval?_compileRaw_internal]
    at hbridge
  have hvalue := Option.some.inj hbridge
  simpa [fixedWidthDescriptionValidity] using hvalue.symm

end Circuit

end Complexity
