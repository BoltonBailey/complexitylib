/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.BarringtonUniform.Defs

/-!
# Uniform Barrington classes -- proof internals
-/

namespace Complexity

/-- Internal forgetful containment for uniform formula families. -/
theorem uniformFormulaNC1_subset_formulaNC1_internal :
    UniformFormulaNC1 ⊆ FormulaNC1 := by
  rintro function ⟨family, hdepth, _huniform, hcomputes⟩
  exact ⟨family, hdepth, hcomputes⟩

/-- Internal forgetful containment for uniform branching-program families. -/
theorem uniformWidth5BP_subset_width5BP_internal :
    UniformWidth5BP ⊆ Width5BP := by
  rintro function ⟨family, point, hlength, _huniform, hdecides⟩
  exact ⟨family, point, hlength, hdecides⟩

/-- Internal polynomial-length theorem for the concrete compiled family. -/
theorem FormulaFamily.barringtonProgram_polynomialLength_internal
    (family : FormulaFamily) (hdepth : family.LogDepth) :
    family.barringtonProgram.PolynomialLength := by
  obtain ⟨constant, hconstant⟩ := hdepth
  refine ⟨4 ^ constant, 2 * constant, fun n => ?_⟩
  calc
    (family.barringtonProgram n).length ≤ 4 ^ (family n).depth :=
      barringtonCompile_length_le (family n) barringtonTargetBase
    _ ≤ 4 ^ (constant * Nat.log 2 n + constant) :=
      Nat.pow_le_pow_right (by omega) (hconstant n)
    _ ≤ 4 ^ constant * (n + 1) ^ (2 * constant) :=
      pow4_poly constant n

/-- Internal exact decision semantics of the concrete compiled family. -/
theorem FormulaFamily.barringtonProgram_decides_internal
    (family : FormulaFamily) :
    family.barringtonProgram.Decides (fun _ => 0)
      (fun n assignment => BoolFormula.eval assignment (family n)) := by
  intro n assignment
  change BP.eval assignment
      (barringtonCompile (family n) barringtonTargetBase) 0 ≠ 0 ↔
    BoolFormula.eval assignment (family n) = true
  rw [(barringtonCompile_computes (family n) barringtonTargetBase
    barringtonTargetBase_spec.1 barringtonTargetBase_spec.2) assignment]
  cases heval : BoolFormula.eval assignment (family n) <;>
    simp [heval, barringtonTargetBase_moves_zero]

/-- Internal decision theorem after identifying the formula family's semantic
function. -/
theorem FormulaFamily.barringtonProgram_decides_of_computes_internal
    {family : FormulaFamily} {function : ℕ → (ℕ → Bool) → Bool}
    (hcomputes : family.Computes function) :
    family.barringtonProgram.Decides (fun _ => 0) function := by
  intro n assignment
  simpa only [hcomputes n assignment] using
    family.barringtonProgram_decides_internal n assignment

/-- Internal reduction of uniform Barrington's forward direction to the one
named compilation-uniformity obligation. -/
theorem uniformFormulaNC1_subset_uniformWidth5BP_of_compilation_internal
    (hcompilation : UniformBarringtonCompilation) :
    UniformFormulaNC1 ⊆ UniformWidth5BP := by
  rintro function ⟨family, hdepth, huniform, hcomputes⟩
  refine ⟨family.barringtonProgram, fun _ => 0,
    family.barringtonProgram_polynomialLength_internal hdepth,
    hcompilation family hdepth huniform,
    family.barringtonProgram_decides_of_computes_internal hcomputes⟩

end Complexity
