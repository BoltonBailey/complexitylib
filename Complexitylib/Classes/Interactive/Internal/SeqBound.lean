/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.EventProb
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Sequential events with bounded conditional probability

⚠️ Unreviewed by Bolton

Sequential repetition of an interactive protocol faces an adaptive prover: whether the `i`-th run
is accepted depends on the coins of all runs up to `i`, and only the *conditional* probability
given the earlier coins is bounded. The classical bound is nevertheless the binomial tail, and
this file proves it in the finite-counting style of `Complexitylib.Classes.EventProb`.

The sample space is `Fin k → X`, one block per run. A family of Boolean events `A i` is
*prefixed* when `A i` depends only on blocks `≤ i`, and *conditionally bounded* by `q` when,
whatever the other blocks are, at most a `q` fraction of the values of block `i` make `A i` fire.
`card_fireCount_le` bounds the number of sample points at which at least `m` events fire by the
tail `tailProb q k m` of the binomial distribution, defined here by its Pascal recursion and
identified with the usual sum in `tailProb_eq_sum`.

## Main definitions

- `tailProb` — the binomial upper tail, by recursion
- `fireCount` — how many events fire at a sample point
- `Prefixed`, `CondBounded` — the two hypotheses

## Main results

- `card_fireCount_le` — the sequential tail bound
- `tailProb_eq_sum` — the tail as a sum of binomial terms
-/

@[expose] public section

namespace Complexity

/-! ## The binomial tail -/

/-- The probability that at least `m` of `k` independent trials with success probability `q`
succeed, defined by the Pascal recursion on the first trial. -/
def tailProb (q : ℚ) : ℕ → ℕ → ℚ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | k + 1, m + 1 => (1 - q) * tailProb q k (m + 1) + q * tailProb q k m

variable {q : ℚ}

@[simp] theorem tailProb_zero_zero : tailProb q 0 0 = 1 := rfl

@[simp] theorem tailProb_zero_succ (m : ℕ) : tailProb q 0 (m + 1) = 0 := rfl

@[simp] theorem tailProb_succ_zero (k : ℕ) : tailProb q (k + 1) 0 = 1 := rfl

theorem tailProb_succ_succ (k m : ℕ) :
    tailProb q (k + 1) (m + 1) = (1 - q) * tailProb q k (m + 1) + q * tailProb q k m := rfl

theorem tailProb_zero_right : ∀ k, tailProb q k 0 = 1
  | 0 => rfl
  | _ + 1 => rfl

theorem tailProb_nonneg (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : ∀ k m, 0 ≤ tailProb q k m
  | 0, 0 => by simp
  | 0, _ + 1 => by simp
  | _ + 1, 0 => by simp
  | k + 1, m + 1 => by
      rw [tailProb_succ_succ]
      have h1 := tailProb_nonneg hq0 hq1 k (m + 1)
      have h2 := tailProb_nonneg hq0 hq1 k m
      nlinarith

theorem tailProb_le_one (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : ∀ k m, tailProb q k m ≤ 1
  | 0, 0 => by simp
  | 0, _ + 1 => by simp
  | _ + 1, 0 => by simp
  | k + 1, m + 1 => by
      rw [tailProb_succ_succ]
      have h1 := tailProb_le_one hq0 hq1 k (m + 1)
      have h2 := tailProb_le_one hq0 hq1 k m
      nlinarith

/-- The tail is antitone in the threshold. -/
theorem tailProb_succ_le (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∀ k m, tailProb q k (m + 1) ≤ tailProb q k m
  | 0, 0 => by simp
  | 0, _ + 1 => by simp
  | k + 1, 0 => by
      rw [tailProb_succ_succ, tailProb_zero_right, tailProb_succ_zero]
      have h1 := tailProb_le_one hq0 hq1 k 1
      nlinarith
  | k + 1, m + 1 => by
      rw [tailProb_succ_succ, tailProb_succ_succ]
      have h1 := tailProb_succ_le hq0 hq1 k (m + 1)
      have h2 := tailProb_succ_le hq0 hq1 k m
      nlinarith

/-! ## Sequential events -/

variable {X : Type} [Fintype X]

/-- How many of the events fire at a sample point. -/
def fireCount {k : ℕ} (A : Fin k → (Fin k → X) → Bool) (f : Fin k → X) : ℕ :=
  (Finset.univ.filter fun i => A i f = true).card

/-- The `i`-th event depends only on the blocks up to `i`. -/
def Prefixed {k : ℕ} (A : Fin k → (Fin k → X) → Bool) : Prop :=
  ∀ (i : Fin k) (f g : Fin k → X), (∀ j, j ≤ i → f j = g j) → A i f = A i g

/-- Whatever the other blocks hold, at most a `q` fraction of the values of block `i` make the
`i`-th event fire. -/
def CondBounded {k : ℕ} (q : ℚ) (A : Fin k → (Fin k → X) → Bool) : Prop :=
  ∀ (i : Fin k) (f : Fin k → X),
    ((Finset.univ.filter fun y : X => A i (Function.update f i y) = true).card : ℚ)
      ≤ q * Fintype.card X

/-- The events of the blocks after the first, with the first block fixed. -/
def tailEvents {k : ℕ} (A : Fin (k + 1) → (Fin (k + 1) → X) → Bool) (y : X) :
    Fin k → (Fin k → X) → Bool :=
  fun i f => A i.succ (Fin.cons y f)

omit [Fintype X] in
theorem tailEvents_prefixed {k : ℕ} {A : Fin (k + 1) → (Fin (k + 1) → X) → Bool}
    (hA : Prefixed A) (y : X) : Prefixed (tailEvents A y) := by
  intro i f g hfg
  refine hA i.succ _ _ fun j hj => ?_
  cases j using Fin.cases with
  | zero => simp
  | succ j' =>
      simp only [Fin.cons_succ]
      exact hfg j' (Fin.succ_le_succ_iff.mp hj)

theorem tailEvents_condBounded {k : ℕ} {A : Fin (k + 1) → (Fin (k + 1) → X) → Bool}
    (hA : CondBounded q A) (y : X) : CondBounded q (tailEvents A y) := by
  intro i f
  have := hA i.succ (Fin.cons y f)
  simp only [tailEvents, Fin.cons_update]
  exact this

omit [Fintype X] in
/-- The first event only looks at the first block. -/
theorem prefixed_zero {k : ℕ} {A : Fin (k + 1) → (Fin (k + 1) → X) → Bool}
    (hA : Prefixed A) (y : X) (f g : Fin k → X) :
    A 0 (Fin.cons y f) = A 0 (Fin.cons y g) := by
  refine hA 0 _ _ fun j hj => ?_
  have : j = 0 := Fin.le_zero_iff.mp hj
  subst this
  simp

omit [Fintype X] in
theorem fireCount_cons {k : ℕ} (A : Fin (k + 1) → (Fin (k + 1) → X) → Bool) (y : X)
    (f : Fin k → X) :
    fireCount A (Fin.cons y f)
      = (if A 0 (Fin.cons y f) = true then 1 else 0) + fireCount (tailEvents A y) f := by
  rw [fireCount, fireCount, Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  rfl

/-- The sample space of `k + 1` blocks is a first block and the rest. -/
def consEquiv (k : ℕ) : (Fin (k + 1) → X) ≃ X × (Fin k → X) where
  toFun f := (f 0, Fin.tail f)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by
    simp

/-- **The sequential tail bound.** -/
theorem card_fireCount_le (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∀ (k : ℕ) (A : Fin k → (Fin k → X) → Bool), Prefixed A → CondBounded q A →
      ∀ m : ℕ, ((Finset.univ.filter fun f : Fin k → X => m ≤ fireCount A f).card : ℚ)
        ≤ tailProb q k m * (Fintype.card X : ℚ) ^ k
  | 0, A, _, _, m => by
      cases m with
      | zero =>
          simp only [zero_le, Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fun,
            Fintype.card_fin, pow_zero, tailProb_zero_zero, one_mul, Nat.cast_one, le_refl,
            implies_true]
      | succ m =>
          have h : ∀ f : Fin 0 → X, fireCount A f = 0 := by
            intro f
            simp [fireCount]
          simp [h]
  | k + 1, A, hA, hB, m => by
      cases m with
      | zero =>
          simp only [zero_le, Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fun,
            Fintype.card_fin, tailProb_succ_zero, one_mul, Nat.cast_pow, le_refl,
            implies_true]
      | succ m =>
          classical
          -- the first event, as a function of the first block alone
          set a : X → Bool := fun y => decide (∃ f : Fin k → X, A 0 (Fin.cons y f) = true)
            with ha
          have ha_eq : ∀ (y : X) (f : Fin k → X), A 0 (Fin.cons y f) = a y := by
            intro y f
            rw [ha]
            by_cases h : A 0 (Fin.cons y f) = true
            · rw [h]
              symm
              simpa using ⟨f, h⟩
            · simp only [Bool.not_eq_true] at h
              rw [h]
              symm
              simp only [decide_eq_false_iff_not, not_exists]
              intro g hg
              rw [prefixed_zero hA y g f, h] at hg
              exact Bool.false_ne_true hg
          -- the count of sample points, block by block
          have hsplit : ((Finset.univ.filter
              fun f : Fin (k + 1) → X => m + 1 ≤ fireCount A f).card : ℚ)
              = ∑ y : X, ((Finset.univ.filter
                  fun f : Fin k → X => m + 1 ≤ fireCount A (Fin.cons y f)).card : ℚ) := by
            rw [Finset.card_filter]
            push_cast
            rw [Fintype.sum_equiv (consEquiv k)
              (fun f => if m + 1 ≤ fireCount A f then (1 : ℚ) else 0)
              (fun p => if m + 1 ≤ fireCount A (Fin.cons p.1 p.2) then (1 : ℚ) else 0)
              (fun f => by simp [consEquiv])]
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [Finset.card_filter]
            push_cast
            rfl
          -- each block's contribution
          have hblock : ∀ y : X, ((Finset.univ.filter
              fun f : Fin k → X => m + 1 ≤ fireCount A (Fin.cons y f)).card : ℚ)
              ≤ (if a y = true then tailProb q k m else tailProb q k (m + 1))
                * (Fintype.card X : ℚ) ^ k := by
            intro y
            have hpre := tailEvents_prefixed hA y
            have hcond := tailEvents_condBounded hB y
            by_cases hay : a y = true
            · rw [if_pos hay]
              have heq : (Finset.univ.filter
                  fun f : Fin k → X => m + 1 ≤ fireCount A (Fin.cons y f))
                  = Finset.univ.filter
                      fun f : Fin k → X => m ≤ fireCount (tailEvents A y) f := by
                ext f
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, fireCount_cons,
                  ha_eq y f, hay, if_true]
                omega
              rw [heq]
              exact card_fireCount_le hq0 hq1 k _ hpre hcond m
            · rw [if_neg hay]
              have heq : (Finset.univ.filter
                  fun f : Fin k → X => m + 1 ≤ fireCount A (Fin.cons y f))
                  = Finset.univ.filter
                      fun f : Fin k → X => m + 1 ≤ fireCount (tailEvents A y) f := by
                ext f
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, fireCount_cons,
                  ha_eq y f, hay, Bool.false_eq_true, if_false]
                omega
              rw [heq]
              exact card_fireCount_le hq0 hq1 k _ hpre hcond (m + 1)
          -- how many first blocks fire
          have hfirst : ((Finset.univ.filter fun y : X => a y = true).card : ℚ)
              ≤ q * Fintype.card X := by
            rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
            · simp
            · have := hB 0 (fun _ => x₀)
              have heq : (Finset.univ.filter fun y : X => A 0 (Function.update (fun _ => x₀) 0 y)
                  = true) = Finset.univ.filter fun y : X => a y = true := by
                ext y
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                rw [← Fin.cons_self_tail (fun _ : Fin (k + 1) => x₀), Fin.update_cons_zero,
                  ha_eq]
              rw [heq] at this
              exact this
          -- assemble
          rw [hsplit]
          calc ∑ y : X, ((Finset.univ.filter
                  fun f : Fin k → X => m + 1 ≤ fireCount A (Fin.cons y f)).card : ℚ)
              ≤ ∑ y : X, (if a y = true then tailProb q k m else tailProb q k (m + 1))
                  * (Fintype.card X : ℚ) ^ k := Finset.sum_le_sum fun y _ => hblock y
            _ = ((Finset.univ.filter fun y : X => a y = true).card
                  * (tailProb q k m - tailProb q k (m + 1))
                  + Fintype.card X * tailProb q k (m + 1)) * (Fintype.card X : ℚ) ^ k := by
                rw [← Finset.sum_mul]
                congr 1
                rw [Finset.card_filter]
                push_cast
                rw [Finset.sum_mul, show (Fintype.card X : ℚ) * tailProb q k (m + 1)
                    = ∑ _y : X, tailProb q k (m + 1) by
                  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul],
                  ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun y _ => ?_
                split_ifs <;> ring
            _ ≤ (q * Fintype.card X * (tailProb q k m - tailProb q k (m + 1))
                  + Fintype.card X * tailProb q k (m + 1)) * (Fintype.card X : ℚ) ^ k := by
                have hmono := tailProb_succ_le hq0 hq1 k m
                have hpow : (0 : ℚ) ≤ (Fintype.card X : ℚ) ^ k := by positivity
                refine mul_le_mul_of_nonneg_right ?_ hpow
                exact add_le_add (mul_le_mul_of_nonneg_right hfirst (by linarith)) le_rfl
            _ = tailProb q (k + 1) (m + 1) * (Fintype.card X : ℚ) ^ (k + 1) := by
                rw [tailProb_succ_succ, pow_succ]
                ring

/-! ## The tail as a sum -/

/-- The binomial upper tail as the usual sum. -/
theorem tailProb_eq_sum (q : ℚ) : ∀ k m : ℕ,
    tailProb q k m = ∑ j ∈ Finset.range (k + 1),
      if m ≤ j then (k.choose j : ℚ) * q ^ j * (1 - q) ^ (k - j) else 0
  | 0, 0 => by simp
  | 0, m + 1 => by simp
  | k + 1, 0 => by
      rw [tailProb_succ_zero]
      simp only [zero_le, if_true]
      have := (add_pow q (1 - q) (k + 1))
      rw [add_sub_cancel, one_pow] at this
      exact this.trans (Finset.sum_congr rfl fun j _ => by ring)
  | k + 1, m + 1 => by
      rw [tailProb_succ_succ, tailProb_eq_sum q k (m + 1), tailProb_eq_sum q k m,
        Finset.sum_range_succ' (fun j => if m + 1 ≤ j then
          ((k + 1).choose j : ℚ) * q ^ j * (1 - q) ^ (k + 1 - j) else 0) (k + 1),
        Finset.sum_range_succ' (fun j => if m + 1 ≤ j then
          (k.choose j : ℚ) * q ^ j * (1 - q) ^ (k - j) else 0) k]
      rw [if_neg (Nat.not_succ_le_zero m), if_neg (Nat.not_succ_le_zero m), add_zero, add_zero]
      have hpascal : ∀ j : ℕ, ((k + 1).choose (j + 1) : ℚ) = k.choose j + k.choose (j + 1) :=
        fun j => by exact_mod_cast Nat.choose_succ_succ k j
      have hR : ∀ j ∈ Finset.range (k + 1),
          (if m + 1 ≤ j + 1 then ((k + 1).choose (j + 1) : ℚ) * q ^ (j + 1)
              * (1 - q) ^ (k + 1 - (j + 1)) else 0)
            = q * (if m ≤ j then (k.choose j : ℚ) * q ^ j * (1 - q) ^ (k - j) else 0)
              + (if m ≤ j then (k.choose (j + 1) : ℚ) * q ^ (j + 1) * (1 - q) ^ (k - j)
                  else 0) := by
        intro j _
        rw [hpascal, Nat.add_sub_add_right]
        simp only [Nat.add_le_add_iff_right]
        split_ifs <;> ring
      rw [Finset.sum_congr rfl hR, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_range_succ (fun j => if m ≤ j then
          (k.choose (j + 1) : ℚ) * q ^ (j + 1) * (1 - q) ^ (k - j) else 0) k,
        Nat.choose_succ_self]
      simp only [Nat.cast_zero, zero_mul, ite_self, add_zero]
      have hL : ∀ j ∈ Finset.range k,
          (1 - q) * (if m + 1 ≤ j + 1 then (k.choose (j + 1) : ℚ) * q ^ (j + 1)
              * (1 - q) ^ (k - (j + 1)) else 0)
            = if m ≤ j then (k.choose (j + 1) : ℚ) * q ^ (j + 1) * (1 - q) ^ (k - j)
              else 0 := by
        intro j hj
        rw [Finset.mem_range] at hj
        simp only [Nat.add_le_add_iff_right]
        rw [show k - j = k - (j + 1) + 1 by omega, pow_succ]
        split_ifs <;> ring
      rw [Finset.mul_sum, Finset.sum_congr rfl hL]
      ring

end Complexity
