/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonConverse.Internal

/-!
# The converse direction of Barrington's theorem

Polynomial-length width-`5` permutation branching programs are evaluated by
balanced Boolean formulas of logarithmic depth. Together with the existing
formula-to-program construction, this proves the full nonuniform Barrington
equivalence under the library's total-assignment family convention.

## Main results

- `BP.eval_reachesFormula` -- correctness of balanced state-to-state evaluation
- `BP.depth_reachesFormula_le` -- depth at most `(w + 1) * d + 1`
- `BP.eval_decisionFormula_eq_true` -- the decision formula detects movement
- `BP.depth_decisionFormula_le` -- logarithmic depth in program length
- `BPFamily.toFormulaFamily_logDepth` -- polynomial-length families give
  logarithmic-depth formula families
- `barrington_equivalence` -- `FormulaNC1 = Width5BP`
-/

namespace Complexity

namespace BP

/-- The balanced state-to-state formula correctly evaluates every program of
length at most `2 ^ d`. -/
theorem eval_reachesFormula {w : ℕ} (α : ℕ → Bool) (d : ℕ) (p : BP w)
    (x y : Fin w) (h : p.length ≤ 2 ^ d) :
    BoolFormula.eval α (reachesFormula d p x y) = true ↔ BP.eval α p x = y :=
  eval_reachesFormula_internal α d p x y h

/-- Balanced state-to-state evaluation has depth at most
`(w + 1) * d + 1`. -/
theorem depth_reachesFormula_le {w : ℕ} (d : ℕ) (p : BP w)
    (x y : Fin w) :
    (reachesFormula d p x y).depth ≤ (w + 1) * d + 1 :=
  depth_reachesFormula_le_internal d p x y

/-- The canonical decision formula is true exactly when the program moves its
designated query point. -/
theorem eval_decisionFormula_eq_true {w : ℕ} (α : ℕ → Bool)
    (p : BP w) (x : Fin w) :
    BoolFormula.eval α (decisionFormula p x) = true ↔ BP.eval α p x ≠ x :=
  eval_decisionFormula_eq_true_internal α p x

/-- The canonical decision formula has logarithmic depth in program length. -/
theorem depth_decisionFormula_le {w : ℕ} (p : BP w) (x : Fin w) :
    (decisionFormula p x).depth ≤ (w + 1) * Nat.clog 2 p.length + 2 :=
  depth_decisionFormula_le_internal p x

end BP

namespace BPFamily

/-- The balanced formula family computes every function family decided by the
source branching-program family. -/
theorem toFormulaFamily_computes {w : ℕ} {R : BPFamily w}
    {x : ℕ → Fin w} {f : ℕ → (ℕ → Bool) → Bool} (h : R.Decides x f) :
    (R.toFormulaFamily x).Computes f :=
  toFormulaFamily_computes_internal h

/-- A polynomial-length width-`5` branching-program family becomes a
logarithmic-depth Boolean-formula family. -/
theorem toFormulaFamily_logDepth {R : BPFamily 5} {x : ℕ → Fin 5}
    (h : R.PolynomialLength) :
    (R.toFormulaFamily x).LogDepth :=
  toFormulaFamily_logDepth_internal h

end BPFamily

/-- Every logarithmic-depth formula family has a polynomial-length width-`5`
permutation branching-program family. -/
theorem formulaNC1_subset_width5BP : FormulaNC1 ⊆ Width5BP :=
  formulaNC1_subset_width5BP_internal

/-- Every polynomial-length width-`5` permutation branching-program family has
an equivalent logarithmic-depth formula family. -/
theorem width5BP_subset_formulaNC1 : Width5BP ⊆ FormulaNC1 :=
  width5BP_subset_formulaNC1_internal

/-- **Barrington's theorem, nonuniform family form.** Logarithmic-depth Boolean
formula families are exactly polynomial-length width-`5` permutation
branching-program families. -/
theorem barrington_equivalence : FormulaNC1 = Width5BP :=
  Set.Subset.antisymm formulaNC1_subset_width5BP
    width5BP_subset_formulaNC1

end Complexity
