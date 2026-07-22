/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.BarringtonUniform.Defs
import Complexitylib.Classes.BarringtonUniform.Internal

/-!
# Log-space-uniform Barrington families

Formula and width-`5` branching-program families are uniform when an `FL`
transducer emits their canonical member code on unary input. The executable
Barrington compiler gives a concrete program family with one fixed decision
point, exact semantics, and polynomial length for every log-depth source
family.

The only missing forward-uniformity statement is isolated as
`UniformBarringtonCompilation`: the concrete compiled family of a uniform
log-depth formula family is itself uniform. The conditional containment theorem
shows that proving this one machine-level obligation completes the forward
uniform Barrington theorem. No claim is made that the unbounded formula-code
compiler lies in `FL` on arbitrary inputs.

## Main results

- `FormulaFamily.barringtonProgram_polynomialLength` -- explicit polynomial
  length.
- `FormulaFamily.barringtonProgram_decides` -- exact fixed-point semantics.
- `uniformFormulaNC1_subset_uniformWidth5BP_of_compilation` -- reduction of the
  uniform forward theorem to the named generator obligation.
-/

namespace Complexity

/-- Forgetting formula-family uniformity gives the nonuniform formula class. -/
theorem uniformFormulaNC1_subset_formulaNC1 :
    UniformFormulaNC1 ⊆ FormulaNC1 :=
  uniformFormulaNC1_subset_formulaNC1_internal

/-- Forgetting branching-program uniformity gives the nonuniform class. -/
theorem uniformWidth5BP_subset_width5BP :
    UniformWidth5BP ⊆ Width5BP :=
  uniformWidth5BP_subset_width5BP_internal

namespace FormulaFamily

/-- A log-depth formula family compiles through the executable construction to
a concrete polynomial-length width-`5` family. -/
theorem barringtonProgram_polynomialLength
    (family : FormulaFamily) (hdepth : family.LogDepth) :
    family.barringtonProgram.PolynomialLength :=
  family.barringtonProgram_polynomialLength_internal hdepth

/-- The concrete compiled family decides source-formula evaluation by testing
whether the fixed point zero moves. -/
theorem barringtonProgram_decides (family : FormulaFamily) :
    family.barringtonProgram.Decides (fun _ => 0)
      (fun n assignment => BoolFormula.eval assignment (family n)) :=
  family.barringtonProgram_decides_internal

/-- The concrete compiled family decides any function computed by the source
formula family. -/
theorem barringtonProgram_decides_of_computes
    {family : FormulaFamily} {function : ℕ → (ℕ → Bool) → Bool}
    (hcomputes : family.Computes function) :
    family.barringtonProgram.Decides (fun _ => 0) function :=
  family.barringtonProgram_decides_of_computes_internal hcomputes

end FormulaFamily

/-- Once explicit compilation is proved to preserve promised family
uniformity, uniform log-depth formulas are contained in uniform width-`5`
branching programs. -/
theorem uniformFormulaNC1_subset_uniformWidth5BP_of_compilation
    (hcompilation : UniformBarringtonCompilation) :
    UniformFormulaNC1 ⊆ UniformWidth5BP :=
  uniformFormulaNC1_subset_uniformWidth5BP_of_compilation_internal hcompilation

end Complexity
