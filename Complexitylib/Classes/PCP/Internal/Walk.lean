/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.Mixing
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Walks in a regular graph

Dinur's powering step replaces the edges of a constraint graph by its **walks**
of a fixed length `t`. This module gives walks their combinatorial form — a
starting vertex together with a tuple of `t` edge labels — and connects that
form to the analytic one: summing any function of the walk's endpoint over all
`deg ^ t` walks out of a vertex is `deg ^ t` times the `t`-step walk operator.

That identity, `sum_walkEnd`, is the bridge between the two views. The powering
construction is defined by quantifying over walk tuples, while every estimate
about it comes from the spectral bound through `Mixing`; `sum_mul_walkEnd`
performs the translation in the form the analysis needs.

## Main definitions

- `RegGraph.walkEnd` — the endpoint of the walk from `v` with label tuple `s`

## Main results

- `RegGraph.sum_walkEnd` — `∑ s, f (walkEnd v s) = d ^ t * stepIter t f v`
- `RegGraph.sum_mul_walkEnd` — the correlation of `f` at the start and `g` at
  the end of a random walk, as a multiple of the operator inner product
- `RegGraph.card_walks` — there are `deg ^ t` walks out of each vertex
-/

@[expose] public section

namespace Complexity

namespace RegGraph

variable (G : RegGraph)

/-- The endpoint of the walk that starts at `v` and follows the edge labels
`s 0, s 1, …, s (t-1)` in order. -/
def walkEnd (G : RegGraph) : ∀ (t : ℕ), G.V → (Fin t → G.D) → G.V
  | 0, v, _ => v
  | t + 1, v, s => walkEnd G t (G.nbr v (s 0)) (fun j => s j.succ)

@[simp] theorem walkEnd_zero (v : G.V) (s : Fin 0 → G.D) : G.walkEnd 0 v s = v := by
  simp [walkEnd]

theorem walkEnd_succ (t : ℕ) (v : G.V) (s : Fin (t + 1) → G.D) :
    G.walkEnd (t + 1) v s = G.walkEnd t (G.nbr v (s 0)) (fun j => s j.succ) := by
  simp [walkEnd]

theorem walkEnd_cons (t : ℕ) (v : G.V) (i : G.D) (s : Fin t → G.D) :
    G.walkEnd (t + 1) v (Fin.cons i s) = G.walkEnd t (G.nbr v i) s := by
  rw [walkEnd_succ]
  simp

/-- There are `deg ^ t` walks of length `t` out of a vertex. -/
theorem card_walks (t : ℕ) : Fintype.card (Fin t → G.D) = G.deg ^ t := by
  simp

/-- **The bridge between walks and the walk operator.** Averaging a function of
the endpoint over all walks of length `t` out of `v` is exactly the `t`-step
operator applied at `v`. -/
theorem sum_walkEnd (f : G.V → ℝ) (t : ℕ) (v : G.V) :
    ∑ s : Fin t → G.D, f (G.walkEnd t v s) = (G.deg : ℝ) ^ t * G.stepIter t f v := by
  induction t generalizing v with
  | zero => simp
  | succ t ih =>
      have hd : (G.deg : ℝ) ≠ 0 := G.deg_ne_zero
      have hsplit : ∑ s : Fin (t + 1) → G.D, f (G.walkEnd (t + 1) v s)
          = ∑ p : G.D × (Fin t → G.D), f (G.walkEnd (t + 1) v (Fin.cons p.1 p.2)) :=
        (Equiv.sum_comp (Fin.consEquiv fun _ => G.D)
          (fun s => f (G.walkEnd (t + 1) v s))).symm
      calc ∑ s : Fin (t + 1) → G.D, f (G.walkEnd (t + 1) v s)
          = ∑ p : G.D × (Fin t → G.D), f (G.walkEnd (t + 1) v (Fin.cons p.1 p.2)) :=
            hsplit
        _ = ∑ i : G.D, ∑ s : Fin t → G.D, f (G.walkEnd t (G.nbr v i) s) := by
            rw [Fintype.sum_prod_type]
            exact Finset.sum_congr rfl fun i _ =>
              Finset.sum_congr rfl fun s _ => by rw [walkEnd_cons]
        _ = ∑ i : G.D, (G.deg : ℝ) ^ t * G.stepIter t f (G.nbr v i) := by
            exact Finset.sum_congr rfl fun i _ => ih (G.nbr v i)
        _ = (G.deg : ℝ) ^ t * ∑ i : G.D, G.stepIter t f (G.nbr v i) := by
            rw [Finset.mul_sum]
        _ = (G.deg : ℝ) ^ (t + 1) * G.stepIter (t + 1) f v := by
            rw [stepIter_succ, step]
            field_simp
            ring

/-- The walk-form of the correlation between the start and the end of a random
walk: it is `deg ^ t` times the operator inner product, which `mixing_sq`
estimates. -/
theorem sum_mul_walkEnd (f g : G.V → ℝ) (t : ℕ) :
    ∑ v : G.V, ∑ s : Fin t → G.D, f v * g (G.walkEnd t v s)
      = (G.deg : ℝ) ^ t * ∑ v : G.V, f v * G.stepIter t g v := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Finset.mul_sum, G.sum_walkEnd g t v]
  ring

end RegGraph

end Complexity
