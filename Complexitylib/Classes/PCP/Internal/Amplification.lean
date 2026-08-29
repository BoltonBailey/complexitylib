/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.ConstraintGraph
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Gap amplification: the iteration spine of Dinur's proof

Dinur's proof of the PCP theorem rests on a single transformation of constraint
graphs over a *fixed* alphabet that

* blows the graph up by at most a constant factor,
* keeps satisfiable graphs satisfiable, and
* **doubles** the unsatisfiability value, until it reaches a universal
  constant `gap`.

This module packages those three properties as `Amplifier` and derives the
consequence that drives everything else: iterating the transformation
logarithmically many times turns *any* unsatisfiable graph into one whose value
is at least `gap`, while a satisfiable graph stays satisfiable. That is the
constant-gap dichotomy an `O(log n)`-randomness, `O(1)`-query verifier needs.

The construction of an `Amplifier` — degree reduction, expanderization,
powering, and alphabet reduction by composition — is the mathematical content
of the proof and lives in the sibling modules. Everything here is independent
of it, and independent of any machine model: the polynomial-time computability
of the iterated transformation is tracked separately.

## Main definitions

- `Amplifier` — the interface above
- `Amplifier.iter` — the `k`-fold iterate

## Main results

- `Amplifier.numEdges_iter_le` — the size grows by at most `edgeFactor ^ k`
- `Amplifier.satisfiable_iter` — satisfiability is preserved
- `Amplifier.unsatVal_iter_ge` — the value is at least `min gap (2 ^ k · v)`
- `Amplifier.gap_le_unsatVal_iter` — after `k` rounds with `numEdges ≤ 2 ^ k`,
  an unsatisfiable graph has value at least `gap`
- `Amplifier.dichotomy` — the two cases together
-/

@[expose] public section

namespace Complexity

open ConstraintGraph

/-- A gap amplifier for constraint graphs over the alphabet `α`: a
size-bounded, satisfiability-preserving transformation that doubles the
unsatisfiability value up to the threshold `gap`. -/
structure Amplifier (α : Type) [Fintype α] [Nonempty α] where
  /-- The transformation on constraint graphs. -/
  transform : ConstraintGraph α → ConstraintGraph α
  /-- The constant factor by which the number of edges may grow. -/
  edgeFactor : ℕ
  /-- The universal threshold beyond which the value need not grow. -/
  gap : ℚ
  /-- The threshold is positive. -/
  gap_pos : 0 < gap
  /-- The threshold is at most one, as any unsatisfiability value is. -/
  gap_le_one : gap ≤ 1
  /-- The transformation blows the graph up by at most a constant factor. -/
  numEdges_transform_le : ∀ G, (transform G).numEdges ≤ edgeFactor * G.numEdges
  /-- Satisfiable graphs stay satisfiable: this is perfect completeness. -/
  satisfiable_transform : ∀ G, G.Satisfiable → (transform G).Satisfiable
  /-- The value doubles, until it reaches `gap`. -/
  unsatVal_transform_ge : ∀ G, min gap (2 * G.unsatVal) ≤ (transform G).unsatVal

namespace Amplifier

variable {α : Type} [Fintype α] [Nonempty α] (A : Amplifier α)

/-- The `k`-fold iterate of the amplifier. -/
def iter (A : Amplifier α) (k : ℕ) (G : ConstraintGraph α) : ConstraintGraph α :=
  A.transform^[k] G

@[simp] theorem iter_zero (G : ConstraintGraph α) : A.iter 0 G = G := rfl

theorem iter_succ (k : ℕ) (G : ConstraintGraph α) :
    A.iter (k + 1) G = A.transform (A.iter k G) :=
  Function.iterate_succ_apply' _ _ _

/-! ### Size -/

theorem numEdges_iter_le (k : ℕ) (G : ConstraintGraph α) :
    (A.iter k G).numEdges ≤ A.edgeFactor ^ k * G.numEdges := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc (A.iter (k + 1) G).numEdges
          ≤ A.edgeFactor * (A.iter k G).numEdges := by
            rw [iter_succ]; exact A.numEdges_transform_le _
        _ ≤ A.edgeFactor * (A.edgeFactor ^ k * G.numEdges) := by
            exact Nat.mul_le_mul_left _ ih
        _ = A.edgeFactor ^ (k + 1) * G.numEdges := by ring

/-! ### Completeness -/

theorem satisfiable_iter {G : ConstraintGraph α} (h : G.Satisfiable) (k : ℕ) :
    (A.iter k G).Satisfiable := by
  induction k with
  | zero => simpa using h
  | succ k ih => rw [iter_succ]; exact A.satisfiable_transform _ ih

theorem unsatVal_iter_eq_zero_of_satisfiable {G : ConstraintGraph α}
    (h : G.Satisfiable) (k : ℕ) : (A.iter k G).unsatVal = 0 :=
  (unsatVal_eq_zero_iff_satisfiable _).mpr (A.satisfiable_iter h k)

/-! ### Soundness -/

/-- One doubling step, at the level of the truncated value `min gap ·`. -/
private theorem min_le_min_two_mul {g X : ℚ} (hg : 0 ≤ g) (hX : 0 ≤ X) :
    min g X ≤ min g (2 * min g X) := by
  refine le_min (min_le_left _ _) ?_
  have h1 : (0 : ℚ) ≤ min g X := le_min hg hX
  linarith

theorem unsatVal_iter_ge (k : ℕ) (G : ConstraintGraph α) :
    min A.gap (2 ^ k * G.unsatVal) ≤ (A.iter k G).unsatVal := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : min A.gap (2 * (A.iter k G).unsatVal) ≤ (A.iter (k + 1) G).unsatVal := by
        rw [iter_succ]; exact A.unsatVal_transform_ge _
      refine le_trans ?_ hstep
      have hmono : min A.gap (2 * min A.gap (2 ^ k * G.unsatVal))
          ≤ min A.gap (2 * (A.iter k G).unsatVal) := by
        refine le_min (min_le_left _ _) ?_
        have := min_le_right A.gap (2 * min A.gap (2 ^ k * G.unsatVal))
        linarith [this, ih]
      refine le_trans ?_ hmono
      have hX : (0 : ℚ) ≤ 2 ^ k * G.unsatVal := by
        have := G.unsatVal_nonneg
        positivity
      have := min_le_min_two_mul (g := A.gap) (X := 2 ^ k * G.unsatVal)
        (le_of_lt A.gap_pos) hX
      calc min A.gap (2 ^ (k + 1) * G.unsatVal)
          = min A.gap (2 * (2 ^ k * G.unsatVal)) := by ring_nf
        _ ≤ min A.gap (2 * min A.gap (2 ^ k * G.unsatVal)) := by
            refine le_min (min_le_left _ _) ?_
            rcases le_total A.gap (2 ^ k * G.unsatVal) with hle | hle
            · have : min A.gap (2 ^ k * G.unsatVal) = A.gap := min_eq_left hle
              rw [this]
              have : min A.gap (2 * (2 ^ k * G.unsatVal)) ≤ A.gap := min_le_left _ _
              linarith [A.gap_pos]
            · have : min A.gap (2 ^ k * G.unsatVal) = 2 ^ k * G.unsatVal := min_eq_right hle
              rw [this]
              exact min_le_right _ _

/-- After enough rounds an unsatisfiable graph has value at least `gap`. The
hypothesis `numEdges ≤ 2 ^ k` is what makes `k = O(log (size))` rounds
suffice. -/
theorem gap_le_unsatVal_iter {G : ConstraintGraph α} (h : ¬ G.Satisfiable) {k : ℕ}
    (hk : G.numEdges ≤ 2 ^ k) : A.gap ≤ (A.iter k G).unsatVal := by
  refine le_trans ?_ (A.unsatVal_iter_ge k G)
  refine le_min (le_refl _) ?_
  have hm : 0 < G.numEdges := numEdges_pos_of_not_satisfiable h
  have hmq : (0 : ℚ) < (G.numEdges : ℚ) := by exact_mod_cast hm
  have hkq : ((G.numEdges : ℚ)) ≤ 2 ^ k := by exact_mod_cast hk
  have hlow : 1 / (G.numEdges : ℚ) ≤ G.unsatVal := inv_numEdges_le_unsatVal h
  have h1 : (1 : ℚ) ≤ 2 ^ k * (1 / (G.numEdges : ℚ)) := by
    rw [mul_one_div, le_div_iff₀ hmq, one_mul]
    exact hkq
  have h2 : (2 : ℚ) ^ k * (1 / (G.numEdges : ℚ)) ≤ 2 ^ k * G.unsatVal := by
    have : (0 : ℚ) < 2 ^ k := by positivity
    exact mul_le_mul_of_nonneg_left hlow (le_of_lt this)
  linarith [A.gap_le_one]

/-- The constant-gap dichotomy delivered by logarithmically many rounds: a
satisfiable graph maps to a satisfiable graph, and an unsatisfiable one to a
graph of value at least `gap`. -/
theorem dichotomy (G : ConstraintGraph α) {k : ℕ} (hk : G.numEdges ≤ 2 ^ k) :
    (G.Satisfiable → (A.iter k G).Satisfiable) ∧
      (¬ G.Satisfiable → A.gap ≤ (A.iter k G).unsatVal) :=
  ⟨fun h => A.satisfiable_iter h k, fun h => A.gap_le_unsatVal_iter h hk⟩

end Amplifier

end Complexity
