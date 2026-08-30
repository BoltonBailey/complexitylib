/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.DegreeReductionSound
public import Complexitylib.Classes.PCP.Internal.ExpanderizeCSP
public import Complexitylib.Classes.PCP.Internal.SelfLoops
public import Complexitylib.Classes.PCP.Internal.NumEnc

/-!
# Preprocessing, assembled

Dinur's powering step needs its input to be regular, to be an expander, and to
carry a self-loop at every vertex. `preprocess` produces all three from an
arbitrary constraint graph, by composing the three steps already built:

`preprocess G E = ((G.reduce E).expanderize E).addLoops`

Each step costs only a constant factor of the value and none of them can turn an
unsatisfiable system satisfiable, so the composite is a gap-preserving reduction
with a constant of its own, `preprocessConst`.

Degrees compose transparently: degree reduction gives `1 + E.degree`,
expanderizing adds `E.degree`, and the loops add one, for a final degree of
`2 + 2 · E.degree` — a constant, as the amplification bookkeeping requires. The
size is a constant multiple of the original too: the vertex set is fixed by the
last two steps, so it stays the `2 · numEdges` half-edges of the first.

## Main definitions

- `ConstraintGraph.preprocess` — the composite
- `ConstraintGraph.preprocessConst` — the constant factor it costs

## Main results

- `ConstraintGraph.deg_preprocess`, `order_preprocess`
- `ConstraintGraph.satisfiable_preprocess_of_satisfiable` — completeness
- `ConstraintGraph.le_unsatVal_preprocess` — soundness, with a constant factor
- `ConstraintGraph.spectralBound_preprocess` — the result is an expander, with a
  bound strictly below one
-/

@[expose] public section

namespace Complexity

namespace ConstraintGraph

variable {α : Type} [DecidableEq α] (G : ConstraintGraph α) (E : ExpanderFamily)

/-- The darts of a preprocessed system: the self-loop, the edge-link, the
cloud's and the expander's. Naming the type outright — rather than leaving it as
the composite the construction produces — keeps it independent of the graph. -/
abbrev PreDart (E : ExpanderFamily) : Type :=
  Unit ⊕ (Option (Fin E.degree) ⊕ Fin E.degree)

/-- Degree reduction, then expanderizing, then adding self-loops, with the dart
type named. -/
noncomputable def preprocess : RegCSP α where
  graph :=
    { V := G.HalfEdge
      D := PreDart E
      decEqV := inferInstance
      decEqD := inferInstance
      fintypeV := inferInstance
      fintypeD := inferInstance
      nonemptyD := ⟨Sum.inl ()⟩
      rot := (((G.reduce E).expanderize E).addLoops).graph.rot
      rot_involutive := (((G.reduce E).expanderize E).addLoops).graph.rot_involutive }
  rel := (((G.reduce E).expanderize E).addLoops).rel

/-- **It is the composite it is built from.** -/
theorem preprocess_eq : G.preprocess E = ((G.reduce E).expanderize E).addLoops := rfl

/-- The preprocessed system's vertices are the half-edges, which are numbered
by their edge and their side. -/
noncomputable instance : NumEnc (G.preprocess E).graph.V :=
  inferInstanceAs (NumEnc (Fin G.numEdges × Bool))

/-- Its darts are the self-loop, the edge-link, the cloud-links and the
expander's edges, in that order. -/
noncomputable instance : NumEnc (G.preprocess E).graph.D :=
  inferInstanceAs (NumEnc (Unit ⊕ (Option (Fin E.degree) ⊕ Fin E.degree)))

@[simp] theorem order_preprocess : (G.preprocess E).graph.order = 2 * G.numEdges := by
  show Fintype.card (Fin G.numEdges × Bool) = _
  simp [Nat.mul_comm]

@[simp] theorem deg_preprocess : (G.preprocess E).graph.deg = 2 + 2 * E.degree := by
  show Fintype.card (PreDart E) = _
  simp
  omega

/-- **Completeness.** -/
theorem satisfiable_preprocess_of_satisfiable (h : G.Satisfiable) :
    (G.preprocess E).Satisfiable := by
  rw [preprocess_eq, RegCSP.satisfiable_addLoops_iff, RegCSP.satisfiable_expanderize_iff]
  exact G.satisfiable_reduce_of_satisfiable E h

/-- The constant factor preprocessing costs. -/
noncomputable def preprocessConst (E : ExpanderFamily) (α : Type) [Fintype α] : ℝ :=
  reduceConst E α
    * (((1 + E.degree : ℕ) : ℝ) / ((1 + E.degree : ℕ) + (E.degree : ℝ)))
    * (((1 + 2 * E.degree : ℕ) : ℝ) / (((1 + 2 * E.degree : ℕ) : ℝ) + 1))

section Value

variable [Fintype α] [Nonempty α]

/-- The value after the two trivial-constraint steps, as a multiple of the value
after degree reduction. -/
theorem unsatVal_preprocess_eq :
    ((G.preprocess E).unsatVal : ℚ)
      = (G.reduce E).unsatVal
        * ((1 + E.degree : ℕ) : ℚ) / (((1 + E.degree : ℕ) : ℚ) + (E.degree : ℚ))
        * ((1 + 2 * E.degree : ℕ) : ℚ) / ((((1 + 2 * E.degree : ℕ) : ℚ)) + 1) := by
  have hdegR : (G.reduce E).graph.deg = 1 + E.degree := by
    rw [graph_reduce, deg_reduceGraph]
  have hdegX : ((G.reduce E).expanderize E).graph.deg = 1 + 2 * E.degree := by
    rw [RegCSP.graph_expanderize, ExpanderFamily.deg_expanderize, hdegR]
    ring
  rw [preprocess_eq, RegCSP.unsatVal_addLoops, hdegX, RegCSP.unsatVal_expanderize, hdegR]

/-- **Soundness of preprocessing.** -/
theorem le_unsatVal_preprocess :
    preprocessConst E α * ((G.unsatVal : ℚ) : ℝ)
      ≤ (((G.preprocess E).unsatVal : ℚ) : ℝ) := by
  set k₁ : ℝ := ((1 + E.degree : ℕ) : ℝ) / (((1 + E.degree : ℕ) : ℝ) + (E.degree : ℝ)) with hk₁
  set k₂ : ℝ := ((1 + 2 * E.degree : ℕ) : ℝ) / (((1 + 2 * E.degree : ℕ) : ℝ) + 1) with hk₂
  have hk₁nn : 0 ≤ k₁ := by rw [hk₁]; positivity
  have hk₂nn : 0 ≤ k₂ := by rw [hk₂]; positivity
  have hred := G.le_unsatVal_reduce E
  have heq : (((G.preprocess E).unsatVal : ℚ) : ℝ)
      = (((G.reduce E).unsatVal : ℚ) : ℝ) * k₁ * k₂ := by
    rw [G.unsatVal_preprocess_eq E, hk₁, hk₂]
    push_cast
    ring
  rw [heq, preprocessConst, ← hk₁, ← hk₂]
  calc reduceConst E α * k₁ * k₂ * ((G.unsatVal : ℚ) : ℝ)
      = (reduceConst E α * ((G.unsatVal : ℚ) : ℝ)) * k₁ * k₂ := by ring
    _ ≤ (((G.reduce E).unsatVal : ℚ) : ℝ) * k₁ * k₂ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hred hk₁nn) hk₂nn

end Value

/-! ### The spectral bound -/

/-- The spectral bound preprocessing achieves. -/
noncomputable def preprocessLam (E : ExpanderFamily) : ℝ :=
  (1 + (1 + 2 * (E.degree : ℝ))
      * (((1 + (E.degree : ℝ)) + (E.degree : ℝ) * E.lam) / ((1 + (E.degree : ℝ)) + E.degree)))
    / (1 + (1 + 2 * (E.degree : ℝ)))

/-- **The preprocessed system is an expander.** -/
theorem spectralBound_preprocess :
    (G.preprocess E).graph.SpectralBound (preprocessLam E) := by
  have hdegR : (G.reduce E).graph.deg = 1 + E.degree := by
    rw [graph_reduce, deg_reduceGraph]
  have hdegX : ((G.reduce E).expanderize E).graph.deg = 1 + 2 * E.degree := by
    rw [RegCSP.graph_expanderize, ExpanderFamily.deg_expanderize, hdegR]
    ring
  have hX := (G.reduce E).spectralBound_expanderize E
  rw [hdegR] at hX
  set mu : ℝ := (((1 + E.degree : ℕ) : ℝ) + (E.degree : ℝ) * E.lam)
    / (((1 + E.degree : ℕ) : ℝ) + (E.degree : ℝ)) with hmu
  have hmunn : 0 ≤ mu := by
    rw [hmu]
    have : (0 : ℝ) ≤ 1 - E.lam := by linarith [E.lam_lt_one]
    have hlam : 0 ≤ E.lam := E.lam_nonneg
    positivity
  have hL := ((G.reduce E).expanderize E).graph.spectralBound_addLoops hmunn hX
  rw [hdegX] at hL
  have hgoal : preprocessLam E
      = (1 + ((1 + 2 * E.degree : ℕ) : ℝ) * mu) / (1 + ((1 + 2 * E.degree : ℕ) : ℝ)) := by
    rw [preprocessLam, hmu]
    push_cast
    ring_nf
  rw [hgoal]
  exact hL

theorem preprocessLam_lt_one : preprocessLam E < 1 := by
  have hlam := E.lam_lt_one
  have hmu : ((1 + (E.degree : ℝ)) + (E.degree : ℝ) * E.lam)
      / ((1 + (E.degree : ℝ)) + E.degree) < 1 := by
    rw [div_lt_one (by positivity)]
    have hdpos : (0 : ℝ) < (E.degree : ℝ) := by exact_mod_cast E.degree_pos
    nlinarith
  rw [preprocessLam, div_lt_one (by positivity)]
  nlinarith [hmu]

end ConstraintGraph

end Complexity
