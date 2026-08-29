/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.Mixing

/-!
# Edge expansion from the spectral bound

Dinur's degree-reduction step needs expansion in its *combinatorial* form: a
vertex set with few outgoing edges must be almost everything or almost nothing.
This module derives that from `Mixing` by feeding it indicator functions.

Specialising `mixing_sq` to `1_S` and `1_T` says that the number of darts from
`S` to `T` is what independence predicts, `deg · |S| · |T| / n`, up to
`lam` times the two variances. Taking `T = Sᶜ`, both variances equal
`|S| |Sᶜ| / n`, so the error term's square root is rational in the data and no
`Real.sqrt` is needed: the number of darts leaving `S` is at least
`(1 - lam) · deg · |S| |Sᶜ| / n`.

That is exactly the statement degree reduction consumes: inside a cloud built on
an expander, the vertices disagreeing with the cloud's plurality label send out
proportionally many edges, each of which is an unsatisfied equality constraint.

## Main definitions

- `RegGraph.dartsBetween` — the darts from one vertex set to another

## Main results

- `RegGraph.sum_indicator_mul_step` — the dart count as an operator inner
  product
- `RegGraph.mixing_sq_indicator` — the mixing lemma for vertex sets
- `RegGraph.card_dartsBetween_compl_ge` — **edge expansion**: a set sends out at
  least `(1 - lam) · deg · |S| |Sᶜ| / n` darts
-/

@[expose] public section

namespace Complexity

namespace RegGraph

variable (G : RegGraph)

/-- The darts whose tail lies in `S` and whose head lies in `T`. -/
def dartsBetween (S T : Finset G.V) : Finset (G.V × G.D) :=
  Finset.univ.filter fun p => p.1 ∈ S ∧ G.nbr p.1 p.2 ∈ T

/-- The real-valued indicator of a vertex set. -/
def indicator (S : Finset G.V) : G.V → ℝ :=
  fun v => if v ∈ S then 1 else 0

@[simp] theorem sum_indicator (S : Finset G.V) :
    ∑ v : G.V, G.indicator S v = (S.card : ℝ) := by
  simp [indicator, Finset.sum_ite_mem]

@[simp] theorem sum_sq_indicator (S : Finset G.V) :
    ∑ v : G.V, (G.indicator S v) ^ 2 = (S.card : ℝ) := by
  have h : ∀ v : G.V, (G.indicator S v) ^ 2 = G.indicator S v := by
    intro v; by_cases hv : v ∈ S <;> simp [indicator, hv]
  rw [Finset.sum_congr rfl fun v _ => h v, sum_indicator]

/-- The dart count between two sets, as an inner product against the walk
operator. -/
theorem sum_indicator_mul_step (S T : Finset G.V) :
    ∑ v : G.V, G.indicator S v * G.step (G.indicator T) v
      = ((G.dartsBetween S T).card : ℝ) / (G.deg : ℝ) := by
  have hstep : ∀ v : G.V, G.indicator S v * G.step (G.indicator T) v
      = (∑ i : G.D, G.indicator S v * G.indicator T (G.nbr v i)) / (G.deg : ℝ) := by
    intro v
    rw [step, mul_div_assoc', Finset.mul_sum]
  rw [Finset.sum_congr rfl fun v _ => hstep v, ← Finset.sum_div]
  congr 1
  have hprod : ∑ v : G.V, ∑ i : G.D, G.indicator S v * G.indicator T (G.nbr v i)
      = ∑ p : G.V × G.D, G.indicator S p.1 * G.indicator T (G.nbr p.1 p.2) :=
    (Fintype.sum_prod_type
      (fun p : G.V × G.D => G.indicator S p.1 * G.indicator T (G.nbr p.1 p.2))).symm
  rw [hprod, dartsBetween, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h1 : p.1 ∈ S
  · by_cases h2 : G.nbr p.1 p.2 ∈ T <;> simp [indicator, h1, h2]
  · simp [indicator, h1]

/-- **The mixing lemma for vertex sets.** -/
theorem mixing_sq_indicator {lam : ℝ} (h : G.SpectralBound lam) (hn : 0 < G.order)
    (S T : Finset G.V) :
    (((G.dartsBetween S T).card : ℝ) / (G.deg : ℝ)
        - (S.card : ℝ) * (T.card : ℝ) / (G.order : ℝ)) ^ 2
      ≤ lam ^ 2 * ((S.card : ℝ) - (S.card : ℝ) ^ 2 / (G.order : ℝ))
        * ((T.card : ℝ) - (T.card : ℝ) ^ 2 / (G.order : ℝ)) := by
  have hmix := G.mixing_sq h hn 1 (G.indicator S) (G.indicator T)
  rw [stepIter_succ, stepIter_zero] at hmix
  rwa [G.sum_indicator_mul_step S T, sum_indicator, sum_indicator, sum_sq_indicator,
    sum_sq_indicator] at hmix

/-- **Edge expansion.** A vertex set sends out at least
`(1 - lam) · deg · |S| · |Sᶜ| / n` darts. -/
theorem card_dartsBetween_compl_ge {lam : ℝ} (hlam : 0 ≤ lam) (h : G.SpectralBound lam)
    (hn : 0 < G.order) (S : Finset G.V) :
    (1 - lam) * (G.deg : ℝ) * ((S.card : ℝ) * (Sᶜ.card : ℝ) / (G.order : ℝ))
      ≤ ((G.dartsBetween S Sᶜ).card : ℝ) := by
  have hnq : (0 : ℝ) < (G.order : ℝ) := by exact_mod_cast hn
  have hdq : (0 : ℝ) < (G.deg : ℝ) := by have := G.deg_pos; positivity
  set B : ℝ := (S.card : ℝ) * (Sᶜ.card : ℝ) / (G.order : ℝ) with hB
  have hBnn : 0 ≤ B := by positivity
  -- both variances are `B`
  have hcompl : (S.card : ℝ) + (Sᶜ.card : ℝ) = (G.order : ℝ) := by
    have h : S.card + Sᶜ.card = Fintype.card G.V := Finset.card_add_card_compl S
    rw [order]
    exact_mod_cast h
  have hvarS : (S.card : ℝ) - (S.card : ℝ) ^ 2 / (G.order : ℝ) = B := by
    rw [hB]
    field_simp
    nlinarith [hcompl]
  have hvarT : (Sᶜ.card : ℝ) - (Sᶜ.card : ℝ) ^ 2 / (G.order : ℝ) = B := by
    rw [hB]
    field_simp
    nlinarith [hcompl]
  have hmix := G.mixing_sq_indicator h hn S Sᶜ
  rw [hvarS, hvarT] at hmix
  -- the deviation is at most `lam * B`
  set X : ℝ := ((G.dartsBetween S Sᶜ).card : ℝ) / (G.deg : ℝ) with hX
  have hsq : (X - B) ^ 2 ≤ (lam * B) ^ 2 := by
    calc (X - B) ^ 2 ≤ lam ^ 2 * B * B := by
          rw [hB] at hmix ⊢
          exact hmix
      _ = (lam * B) ^ 2 := by ring
  have habs : B - X ≤ lam * B := by
    have h1 : (B - X) ^ 2 ≤ (lam * B) ^ 2 := by
      calc (B - X) ^ 2 = (X - B) ^ 2 := by ring
        _ ≤ (lam * B) ^ 2 := hsq
    exact le_of_sq_le_sq h1 (by positivity)
  have hXge : (1 - lam) * B ≤ X := by linarith
  calc (1 - lam) * (G.deg : ℝ) * B = (G.deg : ℝ) * ((1 - lam) * B) := by ring
    _ ≤ (G.deg : ℝ) * X := by exact mul_le_mul_of_nonneg_left hXge (le_of_lt hdq)
    _ = ((G.dartsBetween S Sᶜ).card : ℝ) := by rw [hX]; field_simp

end RegGraph

end Complexity
