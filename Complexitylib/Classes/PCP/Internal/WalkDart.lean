/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.WalkPath

/-!
# Each step of a random walk is a uniform dart

The counting fact behind every first-moment estimate in Dinur's powering
analysis: fix a step index `k < t`; then the map sending a walk `(v, s)` to its
`k`-th dart `(walkAt k, s k)` sends the uniform distribution on walks to the
uniform distribution on darts. Equivalently, summing any function of the `k`-th
dart over all `order · deg ^ t` walks gives `deg ^ (t-1)` times its sum over all
darts — every dart is the `k`-th dart of exactly `deg ^ (t-1)` walks.

The proof is an induction on `k` that peels the first label off the walk. Two
ingredients do the work: `walkAt_cons`, which says dropping the first label
shifts the trajectory by one, and `sum_nbr_nsmul`, the rotation-map form of
regularity, which reindexes the sum over `(v, i)` as `deg` copies of the sum
over vertices.

Stated for an arbitrary `AddCommMonoid`, since it is used both to count walks in
`ℕ` and to compute real-valued averages.

## Main results

- `RegGraph.walkAt_cons` — dropping the first label shifts the trajectory
- `RegGraph.sum_stepDart` — the `k`-th dart of a uniform walk is a uniform dart
- `RegGraph.sum_stepDart_fixed` — from a fixed start, the `k`-th dart is
  described by the `k`-step walk operator
- `RegGraph.card_walks_stepDart_mem` — how many walks have their `k`-th dart in
  a given set
-/

@[expose] public section

namespace Complexity

namespace RegGraph

variable (G : RegGraph)

/-- Dropping the first label of a walk shifts its trajectory by one step. -/
theorem walkAt_cons {t : ℕ} (v : G.V) (i : G.D) (s : Fin t → G.D) :
    ∀ m : ℕ, G.walkAt (t + 1) v (Fin.cons i s) (m + 1) = G.walkAt t (G.nbr v i) s m := by
  intro m
  induction m with
  | zero =>
      rw [G.walkAt_succ_of_lt _ _ (Nat.succ_pos t), walkAt_zero, walkAt_zero]
      congr 1
  | succ m ih =>
      rcases Nat.lt_or_ge m t with hlt | hge
      · rw [G.walkAt_succ_of_lt _ _ (by omega : m + 1 < t + 1), ih,
          G.walkAt_succ_of_lt _ _ hlt]
        congr 1
      · rw [G.walkAt_succ_of_ge _ _ (by omega : t + 1 ≤ m + 1), ih,
          G.walkAt_succ_of_ge _ _ hge]

/-- **The `k`-th dart of a uniform walk is a uniform dart.** -/
theorem sum_stepDart {M : Type*} [AddCommMonoid M] :
    ∀ (k t : ℕ) (hk : k < t) (f : G.V × G.D → M),
      (∑ v : G.V, ∑ s : Fin t → G.D, f (G.walkAt t v s k, s ⟨k, hk⟩))
        = (G.deg ^ (t - 1)) • ∑ p : G.V × G.D, f p := by
  intro k
  induction k with
  | zero =>
      intro t hk f
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      have hsplit : ∀ v : G.V, ∑ s : Fin (t' + 1) → G.D, f (G.walkAt (t' + 1) v s 0, s ⟨0, hk⟩)
          = ∑ p : G.D × (Fin t' → G.D), f (v, p.1) := by
        intro v
        rw [← Equiv.sum_comp (Fin.consEquiv fun _ => G.D)
          (fun s => f (G.walkAt (t' + 1) v s 0, s ⟨0, hk⟩))]
        refine Finset.sum_congr rfl fun p _ => ?_
        have h0 : (⟨0, hk⟩ : Fin (t' + 1)) = 0 := rfl
        simp only [Fin.consEquiv_apply, h0, Fin.cons_zero, walkAt_zero]
      calc ∑ v : G.V, ∑ s : Fin (t' + 1) → G.D, f (G.walkAt (t' + 1) v s 0, s ⟨0, hk⟩)
          = ∑ v : G.V, ∑ p : G.D × (Fin t' → G.D), f (v, p.1) :=
            Finset.sum_congr rfl fun v _ => hsplit v
        _ = ∑ v : G.V, ∑ i : G.D, ∑ _s : Fin t' → G.D, f (v, i) := by
            exact Finset.sum_congr rfl fun v _ =>
              Fintype.sum_prod_type (fun p : G.D × (Fin t' → G.D) => f (v, p.1))
        _ = ∑ v : G.V, ∑ i : G.D, (G.deg ^ t') • f (v, i) := by
            refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_const, Finset.card_univ, G.card_walks t']
        _ = (G.deg ^ t') • ∑ p : G.V × G.D, f p := by
            rw [Fintype.sum_prod_type (fun p : G.V × G.D => f p)]
            simp only [Finset.sum_nsmul]
        _ = (G.deg ^ (t' + 1 - 1)) • ∑ p : G.V × G.D, f p := by norm_num
  | succ k ih =>
      intro t hk f
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      have hkt : k < t' := by omega
      have ht' : 1 ≤ t' := by omega
      have hsplit : ∀ v : G.V,
          (∑ s : Fin (t' + 1) → G.D,
              f (G.walkAt (t' + 1) v s (k + 1), s ⟨k + 1, hk⟩))
            = ∑ i : G.D, ∑ s : Fin t' → G.D,
                f (G.walkAt t' (G.nbr v i) s k, s ⟨k, hkt⟩) := by
        intro v
        rw [← Equiv.sum_comp (Fin.consEquiv fun _ => G.D)
          (fun s => f (G.walkAt (t' + 1) v s (k + 1), s ⟨k + 1, hk⟩))]
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => ?_
        have hidx : (Fin.cons (α := fun _ => G.D) i s) ⟨k + 1, hk⟩ = s ⟨k, hkt⟩ := by
          rw [show (⟨k + 1, hk⟩ : Fin (t' + 1)) = Fin.succ ⟨k, hkt⟩ from rfl, Fin.cons_succ]
        show f (G.walkAt (t' + 1) v (Fin.cons i s) (k + 1),
            (Fin.cons (α := fun _ => G.D) i s) ⟨k + 1, hk⟩) = _
        rw [hidx, G.walkAt_cons v i s k]
      calc ∑ v : G.V, ∑ s : Fin (t' + 1) → G.D,
            f (G.walkAt (t' + 1) v s (k + 1), s ⟨k + 1, hk⟩)
          = ∑ v : G.V, ∑ i : G.D, ∑ s : Fin t' → G.D,
              f (G.walkAt t' (G.nbr v i) s k, s ⟨k, hkt⟩) :=
            Finset.sum_congr rfl fun v _ => hsplit v
        _ = G.deg • ∑ u : G.V, ∑ s : Fin t' → G.D,
              f (G.walkAt t' u s k, s ⟨k, hkt⟩) :=
            G.sum_nbr_nsmul (fun u => ∑ s : Fin t' → G.D, f (G.walkAt t' u s k, s ⟨k, hkt⟩))
        _ = G.deg • ((G.deg ^ (t' - 1)) • ∑ p : G.V × G.D, f p) := by
            rw [ih t' hkt f]
        _ = (G.deg ^ (t' + 1 - 1)) • ∑ p : G.V × G.D, f p := by
            rw [← mul_nsmul' (∑ p : G.V × G.D, f p) G.deg (G.deg ^ (t' - 1))]
            congr 1
            rw [← pow_succ']
            congr 1
            omega

/-- Summing over label tuples splits into the first label and the rest. -/
theorem sum_cons_split {M : Type*} [AddCommMonoid M] (m : ℕ) (F : (Fin (m + 1) → G.D) → M) :
    (∑ r : Fin (m + 1) → G.D, F r)
      = ∑ i : G.D, ∑ r : Fin m → G.D, F (Fin.cons i r) := by
  rw [← Equiv.sum_comp (Fin.consEquiv fun _ => G.D) F]
  exact Fintype.sum_prod_type (fun p : G.D × (Fin m → G.D) => F (Fin.cons p.1 p.2))

/-- **The `k`-th dart of a walk out of a *fixed* start.** Unlike `sum_stepDart`,
where the start is also averaged and the dart comes out uniform, here the dart's
vertex is distributed as the `k`-step walk from `x`, which the walk operator
describes exactly. This is what turns a correlation between two steps of a walk
into an operator inner product, where `Mixing` can bound it. -/
theorem sum_stepDart_fixed (h : G.V → G.D → ℝ) :
    ∀ (k m : ℕ) (hk : k < m) (x : G.V),
      (∑ r : Fin m → G.D, h (G.walkAt m x r k) (r ⟨k, hk⟩))
        = (G.deg : ℝ) ^ (m - 1) * ∑ a : G.D, G.stepIter k (fun y => h y a) x := by
  intro k
  induction k with
  | zero =>
      intro m hk x
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hsplit : (∑ r : Fin (m' + 1) → G.D, h (G.walkAt (m' + 1) x r 0) (r ⟨0, hk⟩))
          = ∑ a : G.D, ∑ _r : Fin m' → G.D, h x a := by
        rw [G.sum_cons_split m' (fun r => h (G.walkAt (m' + 1) x r 0) (r ⟨0, hk⟩))]
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun r _ => ?_
        have h0 : (⟨0, hk⟩ : Fin (m' + 1)) = 0 := rfl
        rw [h0, Fin.cons_zero, walkAt_zero]
      rw [hsplit]
      have hcard : ∀ a : G.D, (∑ _r : Fin m' → G.D, h x a) = (G.deg : ℝ) ^ m' * h x a := by
        intro a
        rw [Finset.sum_const, Finset.card_univ, G.card_walks m', nsmul_eq_mul]
        push_cast
        ring
      rw [Finset.sum_congr rfl fun a _ => hcard a, ← Finset.mul_sum]
      simp
  | succ k ih =>
      intro m hk x
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hkm : k < m' := by omega
      have hm1 : 1 ≤ m' := by omega
      have hd : (G.deg : ℝ) ≠ 0 := G.deg_ne_zero
      have hsplit : (∑ r : Fin (m' + 1) → G.D,
            h (G.walkAt (m' + 1) x r (k + 1)) (r ⟨k + 1, hk⟩))
          = ∑ i : G.D, ∑ r : Fin m' → G.D,
              h (G.walkAt m' (G.nbr x i) r k) (r ⟨k, hkm⟩) := by
        rw [G.sum_cons_split m' (fun r => h (G.walkAt (m' + 1) x r (k + 1)) (r ⟨k + 1, hk⟩))]
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun r _ => ?_
        have hidx : (Fin.cons (α := fun _ => G.D) i r) ⟨k + 1, hk⟩ = r ⟨k, hkm⟩ := by
          rw [show (⟨k + 1, hk⟩ : Fin (m' + 1)) = Fin.succ ⟨k, hkm⟩ from rfl, Fin.cons_succ]
        rw [hidx, G.walkAt_cons x i r k]
      rw [hsplit]
      have hstep : ∀ i : G.D, (∑ r : Fin m' → G.D,
            h (G.walkAt m' (G.nbr x i) r k) (r ⟨k, hkm⟩))
          = (G.deg : ℝ) ^ (m' - 1) * ∑ a : G.D, G.stepIter k (fun y => h y a) (G.nbr x i) :=
        fun i => ih m' hkm (G.nbr x i)
      rw [Finset.sum_congr rfl fun i _ => hstep i, ← Finset.mul_sum]
      have hswap : (∑ i : G.D, ∑ a : G.D, G.stepIter k (fun y => h y a) (G.nbr x i))
          = ∑ a : G.D, ∑ i : G.D, G.stepIter k (fun y => h y a) (G.nbr x i) :=
        Finset.sum_comm
      rw [hswap]
      have hnbr : ∀ a : G.D, (∑ i : G.D, G.stepIter k (fun y => h y a) (G.nbr x i))
          = (G.deg : ℝ) * G.stepIter (k + 1) (fun y => h y a) x := by
        intro a
        rw [stepIter_succ, step]
        field_simp
      rw [Finset.sum_congr rfl fun a _ => hnbr a, ← Finset.mul_sum, ← mul_assoc]
      congr 1
      rw [← pow_succ]
      congr 1
      omega

/-- **Two darts of a walk out of a fixed start.** The correlation between what
happens at step `k` and at step `l > k` is an operator expression: the walk
reaches step `k`, the constraint there is weighted, and the remaining `l-k-1`
steps are another application of the walk operator. Feeding this to `Mixing` is
how the second moment of the number of faulty steps gets bounded. -/
theorem sum_two_darts_fixed (h₁ h₂ : G.V → G.D → ℝ) :
    ∀ (k l m : ℕ) (hkl : k < l) (hl : l < m) (x : G.V),
      (∑ r : Fin m → G.D, h₁ (G.walkAt m x r k) (r ⟨k, by omega⟩)
          * h₂ (G.walkAt m x r l) (r ⟨l, by omega⟩))
        = (G.deg : ℝ) ^ (m - 2) * ∑ a : G.D, ∑ b : G.D,
            G.stepIter k
              (fun y => h₁ y a * G.stepIter (l - k - 1) (fun z => h₂ z b) (G.nbr y a)) x := by
  intro k
  induction k with
  | zero =>
      intro l m hkl hl x
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      have hl' : l' < m' := by omega
      have hsplit : (∑ r : Fin (m' + 1) → G.D,
            h₁ (G.walkAt (m' + 1) x r 0) (r ⟨0, by omega⟩)
              * h₂ (G.walkAt (m' + 1) x r (l' + 1)) (r ⟨l' + 1, by omega⟩))
          = ∑ a : G.D, ∑ r : Fin m' → G.D,
              h₁ x a * h₂ (G.walkAt m' (G.nbr x a) r l') (r ⟨l', hl'⟩) := by
        rw [G.sum_cons_split m' (fun r => h₁ (G.walkAt (m' + 1) x r 0) (r ⟨0, by omega⟩)
          * h₂ (G.walkAt (m' + 1) x r (l' + 1)) (r ⟨l' + 1, by omega⟩))]
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun r _ => ?_
        have h0 : (⟨0, by omega⟩ : Fin (m' + 1)) = 0 := rfl
        have hidx : (Fin.cons (α := fun _ => G.D) a r) ⟨l' + 1, by omega⟩ = r ⟨l', hl'⟩ := by
          rw [show (⟨l' + 1, by omega⟩ : Fin (m' + 1)) = Fin.succ ⟨l', hl'⟩ from rfl,
            Fin.cons_succ]
        rw [h0, Fin.cons_zero, walkAt_zero, hidx, G.walkAt_cons x a r l']
      rw [hsplit]
      have hinner : ∀ a : G.D, (∑ r : Fin m' → G.D,
            h₁ x a * h₂ (G.walkAt m' (G.nbr x a) r l') (r ⟨l', hl'⟩))
          = h₁ x a * ((G.deg : ℝ) ^ (m' - 1)
              * ∑ b : G.D, G.stepIter l' (fun z => h₂ z b) (G.nbr x a)) := by
        intro a
        rw [← Finset.mul_sum, G.sum_stepDart_fixed h₂ l' m' hl' (G.nbr x a)]
      rw [Finset.sum_congr rfl fun a _ => hinner a]
      have hpow : m' + 1 - 2 = m' - 1 := by omega
      rw [hpow, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      have hsub : l' + 1 - 0 - 1 = l' := by omega
      simp only [stepIter_zero, hsub, ← Finset.mul_sum]
      ring
  | succ k ih =>
      intro l m hkl hl x
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      have hkl' : k < l' := by omega
      have hl' : l' < m' := by omega
      have hd : (G.deg : ℝ) ≠ 0 := G.deg_ne_zero
      have hsplit : (∑ r : Fin (m' + 1) → G.D,
            h₁ (G.walkAt (m' + 1) x r (k + 1)) (r ⟨k + 1, by omega⟩)
              * h₂ (G.walkAt (m' + 1) x r (l' + 1)) (r ⟨l' + 1, by omega⟩))
          = ∑ i : G.D, ∑ r : Fin m' → G.D,
              h₁ (G.walkAt m' (G.nbr x i) r k) (r ⟨k, by omega⟩)
                * h₂ (G.walkAt m' (G.nbr x i) r l') (r ⟨l', hl'⟩) := by
        rw [G.sum_cons_split m' (fun r => h₁ (G.walkAt (m' + 1) x r (k + 1)) (r ⟨k + 1, by omega⟩)
          * h₂ (G.walkAt (m' + 1) x r (l' + 1)) (r ⟨l' + 1, by omega⟩))]
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun r _ => ?_
        have hk1 : (Fin.cons (α := fun _ => G.D) i r) ⟨k + 1, by omega⟩ = r ⟨k, by omega⟩ := by
          rw [show (⟨k + 1, by omega⟩ : Fin (m' + 1)) = Fin.succ ⟨k, by omega⟩ from rfl,
            Fin.cons_succ]
        have hl1 : (Fin.cons (α := fun _ => G.D) i r) ⟨l' + 1, by omega⟩ = r ⟨l', hl'⟩ := by
          rw [show (⟨l' + 1, by omega⟩ : Fin (m' + 1)) = Fin.succ ⟨l', hl'⟩ from rfl,
            Fin.cons_succ]
        rw [hk1, hl1, G.walkAt_cons x i r k, G.walkAt_cons x i r l']
      rw [hsplit]
      have hIH : ∀ i : G.D, (∑ r : Fin m' → G.D,
            h₁ (G.walkAt m' (G.nbr x i) r k) (r ⟨k, by omega⟩)
              * h₂ (G.walkAt m' (G.nbr x i) r l') (r ⟨l', hl'⟩))
          = (G.deg : ℝ) ^ (m' - 2) * ∑ a : G.D, ∑ b : G.D,
              G.stepIter k
                (fun y => h₁ y a * G.stepIter (l' - k - 1) (fun z => h₂ z b) (G.nbr y a))
                (G.nbr x i) :=
        fun i => ih l' m' hkl' hl' (G.nbr x i)
      rw [Finset.sum_congr rfl fun i _ => hIH i, ← Finset.mul_sum]
      have hswap : ∀ i : G.D, (∑ a : G.D, ∑ b : G.D,
            G.stepIter k (fun y => h₁ y a
              * G.stepIter (l' - k - 1) (fun z => h₂ z b) (G.nbr y a)) (G.nbr x i))
          = ∑ a : G.D, ∑ b : G.D,
            G.stepIter k (fun y => h₁ y a
              * G.stepIter (l' - k - 1) (fun z => h₂ z b) (G.nbr y a)) (G.nbr x i) := fun _ => rfl
      have hcomm : (∑ i : G.D, ∑ a : G.D, ∑ b : G.D,
            G.stepIter k (fun y => h₁ y a
              * G.stepIter (l' - k - 1) (fun z => h₂ z b) (G.nbr y a)) (G.nbr x i))
          = ∑ a : G.D, ∑ b : G.D, ∑ i : G.D,
            G.stepIter k (fun y => h₁ y a
              * G.stepIter (l' - k - 1) (fun z => h₂ z b) (G.nbr y a)) (G.nbr x i) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
      rw [hcomm]
      have hstep : ∀ a b : G.D, (∑ i : G.D,
            G.stepIter k (fun y => h₁ y a
              * G.stepIter (l' - k - 1) (fun z => h₂ z b) (G.nbr y a)) (G.nbr x i))
          = (G.deg : ℝ) * G.stepIter (k + 1) (fun y => h₁ y a
              * G.stepIter (l' - k - 1) (fun z => h₂ z b) (G.nbr y a)) x := by
        intro a b
        rw [stepIter_succ, step]
        field_simp
      rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hstep a b]
      have hsub : l' + 1 - (k + 1) - 1 = l' - k - 1 := by omega
      simp only [hsub]
      have hpow : (G.deg : ℝ) ^ (m' + 1 - 2) = (G.deg : ℝ) ^ (m' - 2) * (G.deg : ℝ) := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hpow]
      simp only [← Finset.mul_sum]
      ring

/-- The number of walks of length `t` whose `k`-th dart lies in `S`. -/
theorem card_walks_stepDart_mem {t : ℕ} {k : ℕ} (hk : k < t) (S : Finset (G.V × G.D)) :
    ∑ v : G.V, (Finset.univ.filter fun s : Fin t → G.D =>
        (G.walkAt t v s k, s ⟨k, hk⟩) ∈ S).card
      = G.deg ^ (t - 1) * S.card := by
  have hind : ∀ v : G.V, (Finset.univ.filter fun s : Fin t → G.D =>
      (G.walkAt t v s k, s ⟨k, hk⟩) ∈ S).card
      = ∑ s : Fin t → G.D, (if (G.walkAt t v s k, s ⟨k, hk⟩) ∈ S then 1 else 0) := by
    intro v
    rw [Finset.card_filter]
  rw [Finset.sum_congr rfl fun v _ => hind v]
  rw [G.sum_stepDart k t hk (fun p => if p ∈ S then 1 else 0)]
  rw [← Finset.card_filter (fun p => p ∈ S) Finset.univ]
  simp [smul_eq_mul]

end RegGraph

end Complexity
