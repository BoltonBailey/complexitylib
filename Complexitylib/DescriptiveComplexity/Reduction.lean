/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.DescriptiveComplexity.Query
import Complexitylib.DescriptiveComplexity.FirstOrder

/-!
# First-order reductions and projections

A **first-order reduction** between decision problems (Boolean queries over finite
structures) is a first-order *interpretation*: the target structure is defined from
the source by FO formulas, one per target relation symbol. This module gives the
dimension-1 (universe-preserving) case — each target relation is an FO-definable
relation on the same universe — the foundational special case of the general
dimension-`k` interpretation (whose target universe is a definable subset of `domᵏ`,
recorded as a roadmap L6 milestone).

First-order reductions are the reductions of descriptive complexity: weak enough to
sit inside `FO`/`AC⁰`, yet enough to define completeness for the standard classes.
Their quantifier-free restriction — **first-order projections** — is weaker still and
is the notion under which many natural problems are complete.

Each Boolean query induces a machine-model `Language` via `queryLanguage`; the
string-level FO-reduction (an FO map on encodings) is a further step on track L6.

## Main definitions and results

- `FOInterpretation` — a dimension-1 first-order interpretation `V → W`.
- `FOInterpretation.apply` — the induced structure map, with `apply_idInterp`.
- `FOReduces` — first-order reducibility between Boolean queries; `FOReduces.refl`.
- `FOInterpretation.IsQuantifierFree`, `FOProjReduces` — first-order projections,
  with `FOProjReduces.toFOReduces` and `FOProjReduces.refl`.
-/

namespace Complexity

namespace DescriptiveComplexity

variable {V W : Vocabulary}

/-- A **(dimension-1) first-order interpretation** from vocabulary `V` to `W`: each
    target relation symbol is defined by an FO formula over `V` with one free variable
    per argument, and each target constant symbol is a source constant. Applying it to
    a `V`-structure yields a `W`-structure on the *same* universe. -/
structure FOInterpretation (V W : Vocabulary) where
  /-- The FO formula (over `V`) defining each target relation of `W`. -/
  relFormula : (i : Fin W.numRels) → Formula V (W.relArity i)
  /-- Each target constant of `W` is interpreted as a source constant of `V`. -/
  constMap : Fin W.numConsts → Fin V.numConsts

/-- Apply an interpretation to a source structure, producing a target structure on the
    same universe: each target relation holds exactly when its defining formula does. -/
def FOInterpretation.apply (I : FOInterpretation V W) (A : FinStruct V) : FinStruct W where
  card := A.card
  hcard := A.hcard
  rel := fun i args => Formula.Sat A args (I.relFormula i)
  const := fun c => A.const (I.constMap c)

/-- The **identity interpretation**: each relation is defined by its own atom
    `R(x₀, …, x_{a-1})` and each constant maps to itself. -/
def FOInterpretation.idInterp (V : Vocabulary) : FOInterpretation V V where
  relFormula := fun i => Formula.relApp i (fun j => Term.var j)
  constMap := fun c => c

/-- The identity interpretation acts as the identity on structures. -/
theorem FOInterpretation.apply_idInterp (A : FinStruct V) :
    (FOInterpretation.idInterp V).apply A = A := by
  cases A with
  | mk card hcard rel const =>
    simp only [FOInterpretation.apply, FOInterpretation.idInterp, Formula.Sat, Term.eval]

/-- **First-order reduction** between Boolean queries: an FO-interpretation carrying
    `Q₁`-membership to `Q₂`-membership on the interpreted structure. -/
def FOReduces (Q₁ : BooleanQuery V) (Q₂ : BooleanQuery W) : Prop :=
  ∃ I : FOInterpretation V W, ∀ A : FinStruct V, Q₁ A ↔ Q₂ (I.apply A)

/-- FO-reducibility is reflexive, via the identity interpretation. -/
theorem FOReduces.refl (Q : BooleanQuery V) : FOReduces Q Q :=
  ⟨FOInterpretation.idInterp V, fun A => by rw [FOInterpretation.apply_idInterp]⟩

/-- An interpretation is **quantifier-free** when every defining formula has quantifier
    rank `0` — the coarse form of a first-order projection. -/
def FOInterpretation.IsQuantifierFree (I : FOInterpretation V W) : Prop :=
  ∀ i, (I.relFormula i).quantifierRank = 0

/-- The identity interpretation is quantifier-free (each relation is a bare atom). -/
theorem FOInterpretation.idInterp_isQuantifierFree :
    (FOInterpretation.idInterp V).IsQuantifierFree :=
  fun _ => rfl

/-- A **first-order projection** reduction: an FO-reduction witnessed by a
    quantifier-free interpretation. -/
def FOProjReduces (Q₁ : BooleanQuery V) (Q₂ : BooleanQuery W) : Prop :=
  ∃ I : FOInterpretation V W, I.IsQuantifierFree ∧ ∀ A : FinStruct V, Q₁ A ↔ Q₂ (I.apply A)

/-- Every first-order projection is in particular a first-order reduction. -/
theorem FOProjReduces.toFOReduces {Q₁ : BooleanQuery V} {Q₂ : BooleanQuery W}
    (h : FOProjReduces Q₁ Q₂) : FOReduces Q₁ Q₂ :=
  let ⟨I, _, hI⟩ := h; ⟨I, hI⟩

/-- FO-projection reducibility is reflexive, via the (quantifier-free) identity. -/
theorem FOProjReduces.refl (Q : BooleanQuery V) : FOProjReduces Q Q :=
  ⟨FOInterpretation.idInterp V, FOInterpretation.idInterp_isQuantifierFree,
    fun A => by rw [FOInterpretation.apply_idInterp]⟩

end DescriptiveComplexity

end Complexity
