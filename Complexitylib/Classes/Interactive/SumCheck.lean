/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive.Internal.SeqBound
public import Mathlib.Algebra.Polynomial.Roots

/-!
# The sum-check protocol

⚠️ Unreviewed by Bolton

The algebraic core of Shamir's theorem, stated on its own. A function `g` on `Fin n → F` is of
*individual degree* at most `d` when, with every other coordinate fixed, it is a polynomial of
degree at most `d` in the remaining one (`IndivDeg`). The **sum-check protocol** convinces a
verifier of the value of the Boolean-cube sum `boolSum n g`, one variable at a time: in each round
the prover sends a univariate polynomial `s` of degree at most `d`, the verifier checks
`s 0 + s 1` against the current claim, picks a random field element `t`, and continues with the
claim `s t` about `g` with its first variable fixed to `t` (`restrict g t`); at the end the
verifier evaluates `g` itself (`accept`).

The prover is adaptive — a `Strategy` chooses each polynomial from the challenges so far — and
the verifier's coins are the challenges `r : Fin n → F`.

- **Completeness** (`accept_honest`): the honest prover, who sends the true partial sums
  (`honest`), is accepted on every challenge.
- **Soundness** (`card_accept_le`): if the claim is false, any prover is accepted on at most
  `n · d · |F| ^ (n - 1)` challenges — probability `n d / |F|`. The proof is the classical one:
  in the first round the prover's polynomial differs from the true one, they agree on at most `d`
  points, and off those points the residual claim is false, so induction applies.

## Main definitions

- `SumCheck.boolSum`, `SumCheck.IndivDeg`, `SumCheck.restrict`
- `SumCheck.Strategy`, `SumCheck.accept` — the protocol
- `SumCheck.firstPoly`, `SumCheck.honest` — the honest prover

## Main results

- `SumCheck.accept_honest` — completeness
- `SumCheck.card_accept_le`, `SumCheck.card_accept_le_ratio` — soundness
-/

@[expose] public section

namespace Complexity

namespace SumCheck

variable {F : Type} [Field F]

/-! ## The cube sum and individual degree -/

/-- The Boolean point of a bit vector. -/
def boolPt {n : ℕ} (b : Fin n → Bool) : Fin n → F := fun i => if b i then 1 else 0

/-- The sum of `g` over the Boolean cube. -/
def boolSum (n : ℕ) (g : (Fin n → F) → F) : F :=
  ∑ b : Fin n → Bool, g (boolPt b)

/-- `g` is a polynomial of degree at most `d` in each variable separately. -/
def IndivDeg (d n : ℕ) (g : (Fin n → F) → F) : Prop :=
  ∀ (i : Fin n) (x : Fin n → F), ∃ p : Polynomial F, p.natDegree ≤ d ∧
    ∀ t, p.eval t = g (Function.update x i t)

/-- `g` with its first variable fixed to `t`. -/
def restrict {n : ℕ} (g : (Fin (n + 1) → F) → F) (t : F) : (Fin n → F) → F :=
  fun x => g (Fin.cons t x)

theorem indivDeg_restrict {d n : ℕ} {g : (Fin (n + 1) → F) → F} (hg : IndivDeg d (n + 1) g)
    (t : F) : IndivDeg d n (restrict g t) := by
  intro i x
  obtain ⟨p, hp, hpe⟩ := hg i.succ (Fin.cons t x)
  exact ⟨p, hp, fun u => by rw [hpe, restrict, Fin.cons_update]⟩

theorem boolPt_cons {n : ℕ} (b₀ : Bool) (b : Fin n → Bool) :
    (boolPt (Fin.cons b₀ b) : Fin (n + 1) → F)
      = Fin.cons (if b₀ then 1 else 0) (boolPt b) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [boolPt]
  | succ i => simp [boolPt]

/-- The cube sum splits along the first variable. -/
theorem boolSum_succ (n : ℕ) (g : (Fin (n + 1) → F) → F) :
    boolSum (n + 1) g = boolSum n (restrict g 1) + boolSum n (restrict g 0) := by
  rw [boolSum, Fintype.sum_equiv (consEquiv n) (fun b => g (boolPt b))
    (fun p => g (boolPt (Fin.cons p.1 p.2))) (fun b => by simp [consEquiv]),
    Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [boolPt_cons, if_true]
  rfl

theorem boolSum_zero (g : (Fin 0 → F) → F) : boolSum 0 g = g Fin.elim0 := by
  rw [boolSum, Fintype.sum_unique]
  congr 1
  exact Subsingleton.elim _ _

/-! ## The protocol -/

/-- A prover strategy: the next polynomial, as a function of the challenges so far. -/
abbrev Strategy (F : Type) [Semiring F] := List F → Polynomial F

/-- The verifier accepts the claim `C` about `boolSum n g` against the strategy `P` on the
challenges `r`: in each round the prover's polynomial has degree at most `d` and its values at
`0` and `1` add up to the current claim, and at the end `g` itself is consulted. -/
def accept (d : ℕ) :
    (n : ℕ) → ((Fin n → F) → F) → F → Strategy F → (Fin n → F) → Prop
  | 0, g, C, _, _ => g Fin.elim0 = C
  | n + 1, g, C, P, r =>
      (P []).natDegree ≤ d ∧ (P []).eval 0 + (P []).eval 1 = C ∧
        accept d n (restrict g (r 0)) ((P []).eval (r 0)) (fun h => P (r 0 :: h)) (Fin.tail r)

/-! ## The honest prover -/

/-- The true first-round polynomial: the sum of `g` over the cube in all but its first variable,
as a polynomial in that variable. -/
noncomputable def firstPoly {d n : ℕ} {g : (Fin (n + 1) → F) → F}
    (hg : IndivDeg d (n + 1) g) : Polynomial F :=
  ∑ b : Fin n → Bool, Classical.choose (hg 0 (Fin.cons 0 (boolPt b)))

theorem firstPoly_natDegree {d n : ℕ} {g : (Fin (n + 1) → F) → F}
    (hg : IndivDeg d (n + 1) g) : (firstPoly hg).natDegree ≤ d :=
  Polynomial.natDegree_sum_le_of_forall_le _ _ fun b _ =>
    (Classical.choose_spec (hg 0 (Fin.cons 0 (boolPt b)))).1

theorem firstPoly_eval {d n : ℕ} {g : (Fin (n + 1) → F) → F} (hg : IndivDeg d (n + 1) g)
    (t : F) : (firstPoly hg).eval t = boolSum n (restrict g t) := by
  rw [firstPoly, Polynomial.eval_finsetSum, boolSum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [(Classical.choose_spec (hg 0 (Fin.cons 0 (boolPt b)))).2, Fin.update_cons_zero]
  rfl

/-- The honest strategy: in every round, the true partial sum. -/
noncomputable def honest (d : ℕ) :
    (n : ℕ) → (g : (Fin n → F) → F) → IndivDeg d n g → Strategy F
  | 0, _, _, _ => 0
  | _ + 1, _, hg, [] => firstPoly hg
  | n + 1, g, hg, t :: h => honest d n (restrict g t) (indivDeg_restrict hg t) h

/-- **Completeness.** The honest prover is accepted on every challenge. -/
theorem accept_honest (d : ℕ) :
    ∀ (n : ℕ) (g : (Fin n → F) → F) (hg : IndivDeg d n g) (r : Fin n → F),
      accept d n g (boolSum n g) (honest d n g hg) r
  | 0, g, _, _ => by
      show g Fin.elim0 = boolSum 0 g
      rw [boolSum_zero]
  | n + 1, g, hg, r => by
      refine ⟨firstPoly_natDegree hg, ?_, ?_⟩
      · show (firstPoly hg).eval 0 + (firstPoly hg).eval 1 = _
        rw [firstPoly_eval, firstPoly_eval, boolSum_succ, add_comm]
      · show accept d n (restrict g (r 0)) ((firstPoly hg).eval (r 0)) _ (Fin.tail r)
        rw [firstPoly_eval]
        exact accept_honest d n (restrict g (r 0)) (indivDeg_restrict hg (r 0)) (Fin.tail r)

/-! ## Soundness -/

variable [Fintype F] [DecidableEq F]

/-- Two polynomials of degree at most `d` that differ somewhere agree on at most `d` points. -/
theorem card_filter_eval_eq_le {d : ℕ} {s h : Polynomial F} (hs : s.natDegree ≤ d)
    (hh : h.natDegree ≤ d) (hne : ∃ t, s.eval t ≠ h.eval t) :
    (Finset.univ.filter fun t : F => s.eval t = h.eval t).card ≤ d := by
  have hsub : s - h ≠ 0 := by
    obtain ⟨t, ht⟩ := hne
    intro h0
    apply ht
    have := congrArg (Polynomial.eval t) h0
    rw [Polynomial.eval_sub, Polynomial.eval_zero, sub_eq_zero] at this
    exact this
  refine le_trans (Polynomial.card_le_degree_of_subset_roots (p := s - h) ?_) ?_
  · intro t ht
    rw [Finset.mem_val, Finset.mem_filter] at ht
    rw [Polynomial.mem_roots hsub, Polynomial.IsRoot.def, Polynomial.eval_sub, sub_eq_zero]
    exact ht.2
  · exact le_trans (Polynomial.natDegree_sub_le s h) (max_le hs hh)

open Classical in
/-- **Soundness, counted.** If the claim is false, any prover is accepted on at most
`n · d · |F| ^ (n - 1)` of the `|F| ^ n` challenges. -/
theorem card_accept_le (d : ℕ) :
    ∀ (n : ℕ) (g : (Fin n → F) → F), IndivDeg d n g → ∀ (C : F), boolSum n g ≠ C →
      ∀ P : Strategy F,
        (Finset.univ.filter fun r : Fin n → F => accept d n g C P r).card
          ≤ n * d * Fintype.card F ^ (n - 1)
  | 0, g, _, C, hC, P => by
      have hempty : (Finset.univ.filter fun r : Fin 0 → F => accept d 0 g C P r) = ∅ := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        show ¬ g Fin.elim0 = C
        rwa [← boolSum_zero g]
      rw [hempty]
      simp
  | n + 1, g, hg, C, hC, P => by
      set s := P [] with hs
      by_cases h1 : s.natDegree ≤ d ∧ s.eval 0 + s.eval 1 = C
      · set h := firstPoly hg with hh
        have hne : ∃ t, s.eval t ≠ h.eval t := by
          by_contra hall
          simp only [not_exists, not_not] at hall
          apply hC
          rw [boolSum_succ, ← firstPoly_eval hg, ← firstPoly_eval hg, ← hh, ← hall,
            ← hall,
            add_comm]
          exact h1.2
        have hbad := card_filter_eval_eq_le h1.1 (firstPoly_natDegree hg) hne
        -- split the count along the first challenge
        have hsplit : (Finset.univ.filter
            fun r : Fin (n + 1) → F => accept d (n + 1) g C P r).card
            = ∑ t : F, (Finset.univ.filter
                fun r : Fin n → F => accept d (n + 1) g C P (Fin.cons t r)).card := by
          rw [Finset.card_filter, Fintype.sum_equiv (consEquiv n)
            (fun r => if accept d (n + 1) g C P r then 1 else 0)
            (fun p => if accept d (n + 1) g C P (Fin.cons p.1 p.2) then 1 else 0)
            (fun r => by simp [consEquiv]), Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.card_filter]
        have hblock : ∀ t : F, (Finset.univ.filter
            fun r : Fin n → F => accept d (n + 1) g C P (Fin.cons t r)).card
            ≤ if s.eval t = h.eval t then Fintype.card F ^ n
              else n * d * Fintype.card F ^ (n - 1) := by
          intro t
          split_ifs with ht
          · refine le_trans (Finset.card_filter_le _ _) (le_of_eq ?_)
            rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
          · have hsub : (Finset.univ.filter
                fun r : Fin n → F => accept d (n + 1) g C P (Fin.cons t r))
                ⊆ Finset.univ.filter fun r : Fin n → F =>
                  accept d n (restrict g t) (s.eval t) (fun h => P (t :: h)) r := by
              intro r hr
              rw [Finset.mem_filter] at hr ⊢
              refine ⟨Finset.mem_univ _, ?_⟩
              have := hr.2.2.2
              simpa [Fin.cons_zero, Fin.tail_cons] using this
            refine le_trans (Finset.card_le_card hsub) ?_
            refine card_accept_le d n (restrict g t) (indivDeg_restrict hg t) (s.eval t) ?_ _
            rw [← firstPoly_eval hg, ← hh]
            exact fun heq => ht heq.symm
        rw [hsplit]
        calc ∑ t : F, (Finset.univ.filter
                fun r : Fin n → F => accept d (n + 1) g C P (Fin.cons t r)).card
            ≤ ∑ t : F, (if s.eval t = h.eval t then Fintype.card F ^ n
                else n * d * Fintype.card F ^ (n - 1)) := Finset.sum_le_sum fun t _ => hblock t
          _ ≤ ∑ t : F, ((if s.eval t = h.eval t then Fintype.card F ^ n else 0)
                + n * d * Fintype.card F ^ (n - 1)) :=
              Finset.sum_le_sum fun t _ => by split_ifs <;> omega
          _ = (Finset.univ.filter fun t : F => s.eval t = h.eval t).card * Fintype.card F ^ n
                + Fintype.card F * (n * d * Fintype.card F ^ (n - 1)) := by
              rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
                Finset.card_filter, Finset.sum_mul]
              congr 1
              refine Finset.sum_congr rfl fun t _ => ?_
              split_ifs <;> simp
          _ ≤ d * Fintype.card F ^ n + n * d * Fintype.card F ^ n := by
              have hpow : Fintype.card F * (n * d * Fintype.card F ^ (n - 1))
                  ≤ n * d * Fintype.card F ^ n := by
                cases n with
                | zero => simp
                | succ n =>
                    rw [Nat.add_sub_cancel, pow_succ]
                    exact le_of_eq (by ring)
              exact add_le_add (Nat.mul_le_mul_right _ hbad) hpow
          _ = (n + 1) * d * Fintype.card F ^ (n + 1 - 1) := by
              rw [Nat.add_sub_cancel]
              ring
      · have hempty : (Finset.univ.filter fun r : Fin (n + 1) → F => accept d (n + 1) g C P r)
            = ∅ := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          intro hacc
          exact h1 ⟨hacc.1, hacc.2.1⟩
        rw [hempty]
        simp

open Classical in
/-- **Soundness, as a fraction of the challenges**: a false claim is accepted with probability at
most `n d / |F|`. -/
theorem card_accept_le_ratio (d n : ℕ) (g : (Fin n → F) → F) (hg : IndivDeg d n g) (C : F)
    (hC : boolSum n g ≠ C) (P : Strategy F) :
    ((Finset.univ.filter fun r : Fin n → F => accept d n g C P r).card : ℚ)
      / (Fintype.card F : ℚ) ^ n ≤ n * d / Fintype.card F := by
  have hF : (0 : ℚ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have h := card_accept_le d n g hg C hC P
  cases n with
  | zero =>
      simp only [zero_mul, Nat.le_zero] at h
      rw [h]
      simp
  | succ n =>
      rw [div_le_div_iff₀ (by positivity) hF]
      have h' : ((Finset.univ.filter
          fun r : Fin (n + 1) → F => accept d (n + 1) g C P r).card : ℚ)
          ≤ (n + 1) * d * (Fintype.card F : ℚ) ^ n := by
        rw [Nat.add_sub_cancel] at h
        exact_mod_cast h
      calc ((Finset.univ.filter fun r : Fin (n + 1) → F => accept d (n + 1) g C P r).card : ℚ)
            * Fintype.card F
          ≤ (n + 1) * d * (Fintype.card F : ℚ) ^ n * Fintype.card F :=
            mul_le_mul_of_nonneg_right h' hF.le
        _ = ((n + 1 : ℕ) : ℚ) * d * (Fintype.card F : ℚ) ^ (n + 1) := by
            push_cast
            ring

end SumCheck

end Complexity
