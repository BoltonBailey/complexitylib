/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.Expander
public import Complexitylib.Classes.PCP.Internal.Mixing
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Data.Real.Sqrt

/-!
# Expanders on every vertex count, by merging

Explicit expander constructions come in special sizes — squares, powers — but
`ExpanderFamily` wants a member on *every* `n`. This module closes the gap: an
expander on `N` vertices with `2n ≤ N ≤ 3n` is folded onto `n` vertices by
identifying `u` with `u mod n`. Every new vertex absorbs two or three old ones,
so the degree triples, with self-loops padding the vertices that absorbed only
two.

The spectral bound survives, with an explicit loss. Write `f` for a mean-zero
function on the merged graph and `F = f ∘ π` for its lift. The merged step at
`v` is the average of the old steps at the two or three vertices over `v`,
together with `f v` itself for each padding loop, so by Jensen its square is at
most the average of their squares. Summing, the old steps contribute at most
`λ² ‖F‖² + (1 - λ²) N c²` where `c` is the mean of `F` — nonzero, because the
heavier fibres weigh more — and `N c²` is at most half of `‖f‖²` because the
heavy fibres number fewer than `n ≤ N / 2`. The padding loops contribute at
most `‖f‖²`. Altogether the new factor is `μ² = 1/2 + 5λ²/6`, below one as soon
as `λ² < 3/5`, which powering the base graph guarantees.

## Main definitions

- `Complexity.RegGraph.mergeRot` — the merged rotation map
- `Complexity.RegGraph.merged` — the merged graph

## Main results

- `Complexity.RegGraph.spectralBound_merged` — the spectral bound of the merge
- `Complexity.liftN`, `Complexity.card_liftN_none_le_one` — the balanced fibres
  a general merge needs
-/

@[expose] public section

namespace Complexity

namespace RegGraph

variable {N d n : ℕ}

/-! ### The merged rotation map -/

/-- The old vertex numbered `i` in the fibre over `v`, if it exists. -/
def lift (N n : ℕ) (v : Fin n) (i : Fin 3) : Option (Fin N) :=
  if h : v.val + i.val * n < N then some ⟨v.val + i.val * n, h⟩ else none

/-- The new vertex an old vertex lands on. -/
def proj (n : ℕ) (hn : 0 < n) (u : Fin N) : Fin n := ⟨u.val % n, Nat.mod_lt _ hn⟩

/-- The position of an old vertex in its fibre; below three when `N ≤ 3 n`. -/
def slot (n : ℕ) (hN : N ≤ 3 * n) (u : Fin N) : Fin 3 :=
  ⟨u.val / n, by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; omega
    · have := u.isLt
      rw [Nat.div_lt_iff_lt_mul h0]
      omega⟩

theorem lift_proj_slot (hn : 0 < n) (hN : N ≤ 3 * n) (u : Fin N) :
    lift N n (proj n hn u) (slot n hN u) = some u := by
  simp only [lift, proj, slot]
  have h : u.val % n + u.val / n * n = u.val := by
    rw [mul_comm]; exact Nat.mod_add_div u.val n
  rw [dif_pos (by rw [h]; exact u.isLt)]
  congr 1
  exact Fin.ext h

theorem proj_lift (hn : 0 < n) (v : Fin n) (i : Fin 3) (u : Fin N)
    (h : lift N n v i = some u) : proj n hn u = v := by
  simp only [lift] at h
  split_ifs at h with hlt
  · simp only [Option.some.injEq] at h
    rw [← h]
    simp only [proj]
    apply Fin.ext
    show (v.val + i.val * n) % n = v.val
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt v.isLt]

theorem slot_lift (hN : N ≤ 3 * n) (v : Fin n) (i : Fin 3) (u : Fin N)
    (h : lift N n v i = some u) : slot n hN u = i := by
  simp only [lift] at h
  split_ifs at h with hlt
  · simp only [Option.some.injEq] at h
    rw [← h]
    apply Fin.ext
    show (v.val + i.val * n) / n = i.val
    have hn : 0 < n := by omega
    rw [Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt v.isLt, zero_add]

/-- The merged rotation map: a real dart follows the old rotation and is
re-addressed; a padding dart is a self-loop. -/
def mergeRot (hn : 0 < n) (hN : N ≤ 3 * n) (rot : Fin N × Fin d → Fin N × Fin d)
    (x : Fin n × (Fin 3 × Fin d)) : Fin n × (Fin 3 × Fin d) :=
  match lift N n x.1 x.2.1 with
  | some u =>
      let y := rot (u, x.2.2)
      (proj n hn y.1, (slot n hN y.1, y.2))
  | none => x

theorem mergeRot_involutive (hn : 0 < n) (hN : N ≤ 3 * n)
    (rot : Fin N × Fin d → Fin N × Fin d) (hrot : Function.Involutive rot) :
    Function.Involutive (mergeRot hn hN rot) := by
  intro x
  obtain ⟨v, i, s⟩ := x
  simp only [mergeRot]
  cases hl : lift N n v i with
  | none => simp [hl]
  | some u =>
    simp only
    rw [lift_proj_slot hn hN]
    simp only
    rcases hrs : rot (u, s) with ⟨u', s'⟩
    have hy : rot (u', s') = (u, s) := by rw [← hrs]; exact hrot (u, s)
    simp only [hy, Prod.mk.injEq]
    exact ⟨proj_lift hn v i u hl, slot_lift hN v i u hl, trivial⟩

/-- **The merged graph**: `n` vertices of degree `3 d`. -/
def merged (hn : 0 < n) (hd : 0 < d) (hN : N ≤ 3 * n)
    (rot : Fin N × Fin d → Fin N × Fin d) (hrot : Function.Involutive rot) : RegGraph where
  V := Fin n
  D := Fin 3 × Fin d
  decEqV := inferInstance
  decEqD := inferInstance
  fintypeV := inferInstance
  fintypeD := inferInstance
  nonemptyD := ⟨(0, ⟨0, hd⟩)⟩
  rot := mergeRot hn hN rot
  rot_involutive := mergeRot_involutive hn hN rot hrot

/-! ### The spectral bound -/

section Spectral

/-- The base graph, on `Fin N`. -/
abbrev base (hd : 0 < d) (rot : Fin N × Fin d → Fin N × Fin d)
    (hrot : Function.Involutive rot) : RegGraph := ofRot d hd N rot hrot

/-- A term of the merged step at `v`: the old step at the `i`-th vertex over
`v`, or `f v` for a padding loop. -/
noncomputable def term (hn : 0 < n) (hd : 0 < d) (rot : Fin N × Fin d → Fin N × Fin d)
    (hrot : Function.Involutive rot) (f : Fin n → ℝ) (v : Fin n) (i : Fin 3) : ℝ :=
  match lift N n v i with
  | some u => (base hd rot hrot).step (fun w => f (proj n hn w)) u
  | none => f v

theorem deg_merged (hn : 0 < n) (hd : 0 < d) (hN : N ≤ 3 * n)
    (rot : Fin N × Fin d → Fin N × Fin d) (hrot : Function.Involutive rot) :
    (merged hn hd hN rot hrot).deg = 3 * d := by
  show Fintype.card (Fin 3 × Fin d) = 3 * d
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

/-- **The merged step is the average of its terms.** -/
theorem step_merged (hn : 0 < n) (hd : 0 < d) (hN : N ≤ 3 * n)
    (rot : Fin N × Fin d → Fin N × Fin d) (hrot : Function.Involutive rot)
    (f : Fin n → ℝ) (v : Fin n) :
    (merged hn hd hN rot hrot).step f v = (∑ i : Fin 3, term hn hd rot hrot f v i) / 3 := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [step, deg_merged]
  show (∑ x : Fin 3 × Fin d, f (mergeRot hn hN rot (v, x)).1) / ((3 * d : ℕ) : ℝ) = _
  rw [Fintype.sum_prod_type]
  have hinner : ∀ i : Fin 3, ∑ s : Fin d, f (mergeRot hn hN rot (v, (i, s))).1
      = d * term hn hd rot hrot f v i := by
    intro i
    simp only [mergeRot, term]
    cases hl : lift N n v i with
    | none =>
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    | some u =>
        simp only
        rw [step, deg_ofRot]
        show _ = (d : ℝ) * ((∑ i : Fin d, f (proj n hn (rot (u, i)).1)) / (d : ℝ))
        field_simp
  rw [Finset.sum_congr rfl fun i _ => hinner i, ← Finset.mul_sum]
  push_cast
  field_simp

/-- **Jensen**: the square of the average is at most the average of the squares. -/
theorem sq_step_merged_le (hn : 0 < n) (hd : 0 < d) (hN : N ≤ 3 * n)
    (rot : Fin N × Fin d → Fin N × Fin d) (hrot : Function.Involutive rot)
    (f : Fin n → ℝ) (v : Fin n) :
    ((merged hn hd hN rot hrot).step f v) ^ 2
      ≤ (∑ i : Fin 3, (term hn hd rot hrot f v i) ^ 2) / 3 := by
  rw [step_merged, div_pow]
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 3)))
    (f := term hn hd rot hrot f v)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have h3 : (0 : ℝ) < 3 ^ 2 := by norm_num
  rw [div_le_div_iff₀ h3 (by norm_num)]
  push_cast at h
  nlinarith [h]

/-- The pairs `(v, i)` naming an old vertex, as the image of the old vertices. -/
theorem sum_over_lift (hn : 0 < n) (hN : N ≤ 3 * n) (g : Fin N → ℝ) :
    ∑ p : Fin n × Fin 3, (match lift N n p.1 p.2 with | some u => g u | none => 0)
      = ∑ u : Fin N, g u := by
  classical
  have hinj : Function.Injective fun u : Fin N => (proj n hn u, slot n hN u) := by
    intro u u' h
    have h1 := lift_proj_slot hn hN u
    have h2 := lift_proj_slot hn hN u'
    simp only [Prod.mk.injEq] at h
    rw [h.1, h.2, h2] at h1
    exact (Option.some.inj h1).symm
  symm
  calc ∑ u : Fin N, g u
      = ∑ u : Fin N, (match lift N n (proj n hn u) (slot n hN u) with
          | some u' => g u' | none => 0) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [lift_proj_slot hn hN]
    _ = ∑ p ∈ Finset.univ.image (fun u : Fin N => (proj n hn u, slot n hN u)),
          (match lift N n p.1 p.2 with | some u' => g u' | none => 0) := by
        rw [Finset.sum_image (fun u _ u' _ h => hinj h)]
    _ = ∑ p : Fin n × Fin 3, (match lift N n p.1 p.2 with | some u' => g u' | none => 0) := by
        refine Finset.sum_subset (Finset.subset_univ _) fun p _ hp => ?_
        cases hl : lift N n p.1 p.2 with
        | none => rfl
        | some u =>
            exfalso
            apply hp
            rw [Finset.mem_image]
            refine ⟨u, Finset.mem_univ _, ?_⟩
            rw [proj_lift hn _ _ u hl, slot_lift hN _ _ u hl]

theorem lift_zero (h2 : 2 * n ≤ N) (v : Fin n) : lift N n v 0 = some ⟨v.val, by omega⟩ := by
  simp only [lift, Fin.val_zero, zero_mul, add_zero]
  rw [dif_pos (by omega)]

theorem lift_one (h2 : 2 * n ≤ N) (v : Fin n) :
    lift N n v 1 = some ⟨v.val + n, by omega⟩ := by
  simp only [lift, Fin.val_one, one_mul]
  rw [dif_pos (by omega)]

/-- **Splitting the terms**: the old steps, plus at most one padding loop per
vertex. -/
theorem sum_sq_term_le (hn : 0 < n) (hd : 0 < d) (hN : N ≤ 3 * n)
    (rot : Fin N × Fin d → Fin N × Fin d) (hrot : Function.Involutive rot)
    (h2 : 2 * n ≤ N) (f : Fin n → ℝ) :
    ∑ v : Fin n, ∑ i : Fin 3, (term hn hd rot hrot f v i) ^ 2
      ≤ (∑ u : Fin N, ((base hd rot hrot).step (fun w => f (proj n hn w)) u) ^ 2)
        + ∑ v : Fin n, (f v) ^ 2 := by
  classical
  have hsplit : ∀ v i, (term hn hd rot hrot f v i) ^ 2
      = (match lift N n v i with
          | some u => ((base hd rot hrot).step (fun w => f (proj n hn w)) u) ^ 2
          | none => 0)
        + (match lift N n v i with | some _ => 0 | none => (f v) ^ 2) := by
    intro v i
    simp only [term]
    cases lift N n v i <;> simp
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [← Fintype.sum_prod_type', sum_over_lift hn hN]
  refine add_le_add le_rfl (Finset.sum_le_sum fun v _ => ?_)
  rw [Fin.sum_univ_three, lift_zero h2, lift_one h2]
  simp only [zero_add]
  cases lift N n v 2 with
  | some _ => show (0 : ℝ) ≤ f v ^ 2; exact sq_nonneg _
  | none => show f v ^ 2 ≤ f v ^ 2; exact le_rfl

/-- **The lift's squares**: each `f v` is counted at most three times. -/
theorem sum_sq_lift_le (hn : 0 < n) (hN : N ≤ 3 * n) (f : Fin n → ℝ) :
    ∑ u : Fin N, (f (proj n hn u)) ^ 2 ≤ 3 * ∑ v : Fin n, (f v) ^ 2 := by
  classical
  have h := sum_over_lift hn hN (fun u => (f (proj n hn u)) ^ 2)
  rw [← h, Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  have : ∀ i : Fin 3, (match lift N n v i with | some u => (f (proj n hn u)) ^ 2 | none => 0)
      ≤ (f v) ^ 2 := by
    intro i
    cases hl : lift N n v i with
    | none => show (0 : ℝ) ≤ f v ^ 2; exact sq_nonneg _
    | some u => simp only; rw [proj_lift hn v i u hl]
  calc ∑ i : Fin 3, (match lift N n v i with | some u => (f (proj n hn u)) ^ 2 | none => 0)
      ≤ ∑ _i : Fin 3, (f v) ^ 2 := Finset.sum_le_sum fun i _ => this i
    _ = 3 * (f v) ^ 2 := by simp

/-- **The lift's sum** is the sum over the heavy fibres, when `f` has mean zero. -/
theorem sum_lift_eq (hn : 0 < n) (hN : N ≤ 3 * n) (h2 : 2 * n ≤ N) (f : Fin n → ℝ)
    (hf : ∑ v, f v = 0) :
    ∑ u : Fin N, f (proj n hn u)
      = ∑ v : Fin n, (match lift N n v 2 with | some _ => f v | none => 0) := by
  classical
  have h := sum_over_lift hn hN (fun u => f (proj n hn u))
  rw [← h, Fintype.sum_prod_type]
  have hv : ∀ v : Fin n, ∑ i : Fin 3,
      (match lift N n v i with | some u => f (proj n hn u) | none => 0)
      = 2 * f v + (match lift N n v 2 with | some _ => f v | none => 0) := by
    intro v
    rw [Fin.sum_univ_three, lift_zero h2, lift_one h2]
    simp only
    rw [proj_lift hn v 0 _ (lift_zero h2 v), proj_lift hn v 1 _ (lift_one h2 v)]
    cases hl : lift N n v 2 with
    | none => simp; ring
    | some u => simp only; rw [proj_lift hn v 2 u hl]; ring
  rw [Finset.sum_congr rfl fun v _ => hv v, Finset.sum_add_distrib, ← Finset.mul_sum, hf]
  ring

/-- **The mean of the lift is small**: `N c² ≤ ‖f‖² / 2`. -/
theorem sq_sum_lift_le (hn : 0 < n) (hN : N ≤ 3 * n) (h2 : 2 * n ≤ N) (f : Fin n → ℝ)
    (hf : ∑ v, f v = 0) :
    (∑ u : Fin N, f (proj n hn u)) ^ 2 ≤ (n : ℝ) * ∑ v : Fin n, (f v) ^ 2 := by
  classical
  rw [sum_lift_eq hn hN h2 f hf]
  set H : Finset (Fin n) := Finset.univ.filter fun v => (lift N n v 2).isSome with hH
  have hsum : ∑ v : Fin n, (match lift N n v 2 with | some _ => f v | none => 0)
      = ∑ v ∈ H, f v := by
    rw [hH, Finset.sum_filter]
    refine Finset.sum_congr rfl fun v _ => ?_
    cases lift N n v 2 <;> simp
  rw [hsum]
  have hcs := sq_sum_le_card_mul_sum_sq (s := H) (f := f)
  have hcard : (H.card : ℝ) ≤ n := by
    have : H.card ≤ Fintype.card (Fin n) := Finset.card_le_univ H
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have hsub : ∑ v ∈ H, (f v) ^ 2 ≤ ∑ v : Fin n, (f v) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun v _ _ => sq_nonneg _
  have h0 : 0 ≤ ∑ v ∈ H, (f v) ^ 2 := Finset.sum_nonneg fun v _ => sq_nonneg _
  calc (∑ v ∈ H, f v) ^ 2 ≤ H.card * ∑ v ∈ H, (f v) ^ 2 := hcs
    _ ≤ n * ∑ v : Fin n, (f v) ^ 2 := by
        exact mul_le_mul hcard hsub h0 (by positivity)

/-- **The old steps of the lift**, with the mean corrected. -/
theorem sum_sq_step_lift_le (hn : 0 < n) (hd : 0 < d) (rot : Fin N × Fin d → Fin N × Fin d)
    (hrot : Function.Involutive rot) {lam : ℝ} (hspec : (base hd rot hrot).SpectralBound lam)
    (hN0 : 0 < N) (f : Fin n → ℝ) :
    ∑ u : Fin N, ((base hd rot hrot).step (fun w => f (proj n hn w)) u) ^ 2
      ≤ lam ^ 2 * ∑ u : Fin N, (f (proj n hn u)) ^ 2
        + (1 - lam ^ 2) * ((∑ u : Fin N, f (proj n hn u)) ^ 2 / (N : ℝ)) := by
  classical
  set G := base hd rot hrot with hG
  set F : Fin N → ℝ := fun w => f (proj n hn w) with hF
  have hord : (G.order : ℝ) = N := by rw [hG, order_ofRot]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
  have hordpos : 0 < G.order := by rw [hG, order_ofRot]; exact hN0
  -- decompose `F` into its mean and its centred part
  have hdec : F = fun v => G.mean F + G.center F v := G.eq_mean_add_center F
  have hstep : ∀ u, G.step F u = G.mean F + G.step (G.center F) u := by
    intro u
    conv_lhs => rw [hdec]
    rw [G.step_add (fun _ => G.mean F) (G.center F) u, step_const]
  have hcsum : ∑ u, G.center F u = 0 := G.sum_center hordpos F
  have hstepsum : ∑ u, G.step (G.center F) u = 0 := by rw [G.sum_step, hcsum]
  have hspec' := hspec (G.center F) hcsum
  have hsq : ∑ u, (G.step F u) ^ 2
      = ∑ u, (G.step (G.center F) u) ^ 2 + (N : ℝ) * (G.mean F) ^ 2 := by
    rw [Finset.sum_congr rfl fun u _ => by rw [hstep u]]
    have : ∀ u, (G.mean F + G.step (G.center F) u) ^ 2
        = (G.step (G.center F) u) ^ 2 + 2 * G.mean F * G.step (G.center F) u
          + (G.mean F) ^ 2 := fun u => by ring
    have hcardV : Fintype.card (base hd rot hrot).V = N := Fintype.card_fin N
    rw [Finset.sum_congr rfl fun u _ => this u, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, hstepsum, Finset.sum_const, Finset.card_univ,
      hcardV, nsmul_eq_mul]
    ring
  have hFsq := G.sum_sq_center hordpos F
  rw [hord] at hFsq
  have hmean : (N : ℝ) * (G.mean F) ^ 2 = (∑ u, F u) ^ 2 / (N : ℝ) := by
    rw [mean, hord]
    field_simp
    rfl
  show ∑ u, G.step F u ^ 2 ≤ lam ^ 2 * ∑ u, F u ^ 2 + (1 - lam ^ 2) * ((∑ u, F u) ^ 2 / (N : ℝ))
  rw [hsq, hmean]
  have hsub : ∑ u, (G.center F u) ^ 2 = ∑ u, (F u) ^ 2 - (∑ u, F u) ^ 2 / (N : ℝ) := hFsq
  rw [hsub] at hspec'
  have hnn : 0 ≤ (∑ u, F u) ^ 2 / (N : ℝ) := by positivity
  nlinarith [hspec', hnn]

/-- **The spectral bound of the merge.** -/
theorem spectralBound_merged (hn : 0 < n) (hd : 0 < d) (hN : N ≤ 3 * n)
    (rot : Fin N × Fin d → Fin N × Fin d) (hrot : Function.Involutive rot)
    {lam : ℝ} (hlam : lam ^ 2 ≤ 1)
    (hspec : (base hd rot hrot).SpectralBound lam) (h2 : 2 * n ≤ N) :
    (merged hn hd hN rot hrot).SpectralBound (Real.sqrt (1 / 2 + 5 * lam ^ 2 / 6)) := by
  intro f hf
  have hN0 : 0 < N := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
  have hsqrt : Real.sqrt (1 / 2 + 5 * lam ^ 2 / 6) ^ 2 = 1 / 2 + 5 * lam ^ 2 / 6 :=
    Real.sq_sqrt (by positivity)
  rw [hsqrt]
  have hf' : ∑ v : Fin n, f v = 0 := hf
  have hjensen : ∑ v : Fin n, ((merged hn hd hN rot hrot).step f v) ^ 2
      ≤ (∑ v : Fin n, ∑ i : Fin 3, (term hn hd rot hrot f v i) ^ 2) / 3 := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun v _ => sq_step_merged_le hn hd hN rot hrot f v
  have hterms := sum_sq_term_le hn hd hN rot hrot h2 f
  have hold := sum_sq_step_lift_le hn hd rot hrot hspec hN0 f
  have hlift := sum_sq_lift_le hn hN f
  have hmean := sq_sum_lift_le hn hN h2 f hf'
  have hmean' : (∑ u : Fin N, f (proj n hn u)) ^ 2 / (N : ℝ)
      ≤ (1 / 2) * ∑ v : Fin n, (f v) ^ 2 := by
    rw [div_le_iff₀ hN']
    have h2' : (2 : ℝ) * n ≤ N := by exact_mod_cast h2
    have hS : 0 ≤ ∑ v : Fin n, (f v) ^ 2 := Finset.sum_nonneg fun v _ => sq_nonneg _
    nlinarith [hmean, h2', hS]
  have hS : 0 ≤ ∑ v : Fin n, (f v) ^ 2 := Finset.sum_nonneg fun v _ => sq_nonneg _
  have hl0 : 0 ≤ lam ^ 2 := sq_nonneg _
  have hl1 : 0 ≤ 1 - lam ^ 2 := by linarith
  show ∑ v : Fin n, ((merged hn hd hN rot hrot).step f v) ^ 2
    ≤ (1 / 2 + 5 * lam ^ 2 / 6) * ∑ v : Fin n, (f v) ^ 2
  have hA := mul_le_mul_of_nonneg_left hlift hl0
  have hB := mul_le_mul_of_nonneg_left hmean' hl1
  nlinarith [hjensen, hterms, hold, hA, hB]

end Spectral

/-! ### Balanced fibres, for a merge of any width

The merge above folds `N ≤ 3 n` vertices onto `n`. To fold the sparse sizes a
zig-zag tower produces, the width has to be arbitrary, and what makes that work
is that the fibres stay *balanced*: with `(m - 1) n ≤ N ≤ m n` every fibre has
`m - 1` or `m` elements, so at most one of the `m` slots is empty and the
padding costs one loop per vertex however large `m` is.

These are the two facts a general merge rests on; they are stated for a
natural-number slot index, which is the form the general construction needs. -/

/-- The old vertex in slot `i` of the fibre over `v`, if there is one. -/
def liftN (N n : ℕ) (v : Fin n) (i : ℕ) : Option (Fin N) :=
  if h : v.val + i * n < N then some ⟨v.val + i * n, h⟩ else none

theorem liftN_eq_lift (N n : ℕ) (v : Fin n) (i : Fin 3) :
    liftN N n v i.val = lift N n v i := rfl

/-- **Every slot but the last is filled**, when `(m - 1) n ≤ N`. -/
theorem liftN_isSome {N n m : ℕ} (hm : (m - 1) * n ≤ N) (v : Fin n) {i : ℕ}
    (hi : i + 1 < m) : (liftN N n v i).isSome := by
  rw [liftN]
  have hv : v.val < n := v.isLt
  have hle : v.val + i * n < (m - 1) * n := by
    have h1 : i + 1 ≤ m - 1 := by omega
    calc v.val + i * n < n + i * n := by omega
      _ = (i + 1) * n := by ring
      _ ≤ (m - 1) * n := Nat.mul_le_mul_right _ h1
  rw [dif_pos (lt_of_lt_of_le hle hm)]
  rfl

/-- **So at most one slot is empty.** -/
theorem card_liftN_none_le_one {N n m : ℕ} (hm : (m - 1) * n ≤ N) (v : Fin n) :
    ((Finset.range m).filter fun i => liftN N n v i = none).card ≤ 1 := by
  classical
  refine Finset.card_le_one.2 fun i hi j hj => ?_
  rw [Finset.mem_filter, Finset.mem_range] at hi hj
  by_contra hne
  have hlast : ∀ k : ℕ, k < m → liftN N n v k = none → k + 1 = m := by
    intro k hk hnone
    by_contra hcon
    have : k + 1 < m := by omega
    have := liftN_isSome hm v this
    rw [hnone] at this
    exact absurd this (by simp)
  have h1 := hlast i hi.1 hi.2
  have h2 := hlast j hj.1 hj.2
  omega

end RegGraph

end Complexity
