/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive.OperatorChain
public import Complexitylib.Classes.Interactive.Internal.ModArith
public import Mathlib.Algebra.Field.ZMod

/-!
# The operator-chain protocol with sampled challenges

⚠️ Unreviewed by Bolton

A concrete verifier does not draw its challenges uniformly from the field: it draws bit strings
and reduces them modulo `p`. The map from strings to field elements is not a bijection, but its
fibres are small, and that is all the soundness argument uses — in each round the prover's
polynomial and the true one agree on at most `d` field elements, hence on at most `d · K`
strings when every field element has at most `K` preimages.

`card_accept_comp_le` is `OpChain.card_accept_le` in that form, and `fiber_le_reduce` bounds
the fibres of reduction modulo `p` on `w`-bit strings by `2 ^ w / p + 1`; together
(`card_accept_reduce_le`) a false claim is accepted on at most a `2 (Σ d) / p` fraction of the
challenge strings once `p ≤ 2 ^ w`.

## Main results

- `card_accept_comp_le` — the sampled soundness bound, for any small-fibre map
- `fiber_le_reduce`, `card_accept_reduce_le` — for reduction modulo `p`
-/

@[expose] public section

namespace Complexity

namespace OpChain

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- Two polynomials of degree at most `d` that differ somewhere agree at the images of at most
`d · K` samples, when every field element has at most `K` preimages. -/
theorem card_filter_eval_comp_le {d K : ℕ} (g : S → F)
    (hg : ∀ y : F, (Finset.univ.filter fun t : S => g t = y).card ≤ K)
    {s h : Polynomial F} (hs : s.natDegree ≤ d) (hh : h.natDegree ≤ d)
    (hne : ∃ t, s.eval t ≠ h.eval t) :
    (Finset.univ.filter fun t : S => s.eval (g t) = h.eval (g t)).card ≤ d * K := by
  have hbad := SumCheck.card_filter_eval_eq_le hs hh hne
  calc (Finset.univ.filter fun t : S => s.eval (g t) = h.eval (g t)).card
      = ((Finset.univ.filter fun y : F => s.eval y = h.eval y).biUnion
          fun y => Finset.univ.filter fun t : S => g t = y).card := by
        congr 1
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
        constructor
        · intro ht
          exact ⟨g t, ht, rfl⟩
        · rintro ⟨y, hy, rfl⟩
          exact hy
    _ ≤ ∑ y ∈ Finset.univ.filter (fun y : F => s.eval y = h.eval y),
          (Finset.univ.filter fun t : S => g t = y).card := Finset.card_biUnion_le
    _ ≤ ∑ _y ∈ Finset.univ.filter (fun y : F => s.eval y = h.eval y), K :=
        Finset.sum_le_sum fun y _ => hg y
    _ = (Finset.univ.filter fun y : F => s.eval y = h.eval y).card * K := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ d * K := Nat.mul_le_mul_right _ hbad

open Classical in
/-- **Soundness with sampled challenges.** With every field element having at most `K`
preimages under `g`, a false claim is accepted on at most `(Σ ds) · K · |S| ^ (n - 1)` of the
challenge strings. -/
theorem card_accept_comp_le {K : ℕ} (g : S → F)
    (hg : ∀ y : F, (Finset.univ.filter fun t : S => g t = y).card ≤ K) :
    ∀ (ops : List Op) (ds : List ℕ) (f : (ℕ → F) → F),
      ChainDeg ops ds f → ∀ (a : ℕ → F) (C : F), applyChain ops f a ≠ C →
        ∀ P : SumCheck.Strategy F,
          (Finset.univ.filter fun r : Fin ops.length → S =>
              accept ops ds f a C P (fun k => g (r k))).card
            ≤ (ds.take ops.length).sum * K * Fintype.card S ^ (ops.length - 1)
  | [], _, f, _, a, C, hC, P => by
      simp only [List.length_nil, List.take_zero, List.sum_nil, zero_mul, Nat.le_zero,
        Finset.card_eq_zero]
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact hC
  | o :: os, ds, f, hdeg, a, C, hC, P => by
      set s := P [] with hs
      set d := ds.headD 0 with hd
      set gg := applyChain os f with hgg
      set n := os.length with hn
      by_cases h1 : s.natDegree ≤ d ∧ o.check a s = C
      · set h := roundPoly hdeg.1 a with hh
        have hne : ∃ t, s.eval t ≠ h.eval t := by
          by_contra hall
          simp only [not_exists, not_not] at hall
          apply hC
          rw [applyChain_cons, ← Op.check_eq o gg a
            (fun t => by rw [hall t, hh, roundPoly_eval hdeg.1 a])]
          exact h1.2
        have hbad := card_filter_eval_comp_le g hg h1.1 (roundPoly_natDegree hdeg.1 a) hne
        have hsplit : (Finset.univ.filter
            fun r : Fin (o :: os).length → S =>
              accept (o :: os) ds f a C P (fun k => g (r k))).card
            = ∑ t : S, (Finset.univ.filter
                fun r : Fin n → S =>
                  accept (o :: os) ds f a C P
                    (fun k => g ((Fin.cons t r : Fin (n + 1) → S) k))).card := by
          show (Finset.univ.filter
            fun r : Fin (n + 1) → S => accept (o :: os) ds f a C P (fun k => g (r k))).card = _
          rw [Finset.card_filter, Fintype.sum_equiv (consEquiv n)
            (fun r => if accept (o :: os) ds f a C P (fun k => g (r k)) then 1 else 0)
            (fun p => if accept (o :: os) ds f a C P
                (fun k => g ((Fin.cons p.1 p.2 : Fin (n + 1) → S) k)) then 1 else 0)
            (fun r => by simp [consEquiv]), Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.card_filter]
        have hblock : ∀ t : S, (Finset.univ.filter
            fun r : Fin n → S => accept (o :: os) ds f a C P
              (fun k => g ((Fin.cons t r : Fin (n + 1) → S) k))).card
            ≤ if s.eval (g t) = h.eval (g t) then Fintype.card S ^ n
              else (ds.tail.take n).sum * K * Fintype.card S ^ (n - 1) := by
          intro t
          split_ifs with ht
          · refine le_trans (Finset.card_filter_le _ _) (le_of_eq ?_)
            rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
          · have hsub : (Finset.univ.filter
                fun r : Fin n → S => accept (o :: os) ds f a C P
                  (fun k => g ((Fin.cons t r : Fin (n + 1) → S) k)))
                ⊆ Finset.univ.filter fun r : Fin n → S =>
                  accept os ds.tail f (Function.update a o.var (g t)) (s.eval (g t))
                    (fun h => P (g t :: h)) (fun k => g (r k)) := by
              intro r hr
              rw [Finset.mem_filter] at hr ⊢
              refine ⟨Finset.mem_univ _, ?_⟩
              have := hr.2.2.2
              simpa [Fin.cons_zero, Fin.tail_cons] using this
            refine le_trans (Finset.card_le_card hsub) ?_
            refine card_accept_comp_le g hg os ds.tail f hdeg.2 _ (s.eval (g t)) ?_ _
            rw [← roundPoly_eval hdeg.1 a, ← hh]
            exact fun heq => ht heq.symm
        rw [hsplit]
        have hpow : Fintype.card S * ((ds.tail.take n).sum * K * Fintype.card S ^ (n - 1))
            ≤ (ds.tail.take n).sum * K * Fintype.card S ^ n := by
          cases n with
          | zero => simp
          | succ n =>
              rw [Nat.add_sub_cancel, pow_succ]
              exact le_of_eq (by ring)
        have htake : (ds.take (o :: os).length).sum = d + (ds.tail.take n).sum := by
          cases ds with
          | nil => simp [hd, hn]
          | cons d' ds' => simp [hd, hn, List.take_succ_cons]
        calc ∑ t : S, (Finset.univ.filter
                fun r : Fin n → S =>
                  accept (o :: os) ds f a C P
                    (fun k => g ((Fin.cons t r : Fin (n + 1) → S) k))).card
            ≤ ∑ t : S, (if s.eval (g t) = h.eval (g t) then Fintype.card S ^ n
                else (ds.tail.take n).sum * K * Fintype.card S ^ (n - 1)) :=
              Finset.sum_le_sum fun t _ => hblock t
          _ ≤ ∑ t : S, ((if s.eval (g t) = h.eval (g t) then Fintype.card S ^ n else 0)
                + (ds.tail.take n).sum * K * Fintype.card S ^ (n - 1)) :=
              Finset.sum_le_sum fun t _ => by split_ifs <;> omega
          _ = (Finset.univ.filter fun t : S => s.eval (g t) = h.eval (g t)).card
                  * Fintype.card S ^ n
                + Fintype.card S * ((ds.tail.take n).sum * K * Fintype.card S ^ (n - 1)) := by
              rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
                Finset.card_filter, Finset.sum_mul]
              congr 1
              refine Finset.sum_congr rfl fun t _ => ?_
              split_ifs <;> simp
          _ ≤ d * K * Fintype.card S ^ n + (ds.tail.take n).sum * K * Fintype.card S ^ n :=
              add_le_add (Nat.mul_le_mul_right _ hbad) hpow
          _ = (ds.take (o :: os).length).sum * K * Fintype.card S ^ ((o :: os).length - 1) := by
              rw [htake, List.length_cons, Nat.add_sub_cancel, ← hn]
              ring
      · have hempty : (Finset.univ.filter
            fun r : Fin (o :: os).length → S =>
              accept (o :: os) ds f a C P (fun k => g (r k))) = ∅ := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          intro hacc
          exact h1 ⟨hacc.1, hacc.2.1⟩
        rw [hempty]
        simp

/-! ## Reduction modulo `p` -/

/-- A `w`-bit string as a residue modulo `p`. -/
def reduceBits (w : ℕ) (p : ℕ) (t : Fin w → Bool) : ZMod p :=
  (binValLE (BitString.toList t) : ZMod p)

/-- **Reduction has small fibres**: at most `2 ^ w / p + 1` strings per residue. -/
theorem fiber_le_reduce (w p : ℕ) [NeZero p] (y : ZMod p) :
    (Finset.univ.filter fun t : Fin w → Bool => reduceBits w p t = y).card ≤ 2 ^ w / p + 1 := by
  classical
  have hpos : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  set A := Finset.univ.filter fun t : Fin w → Bool => reduceBits w p t = y with hA
  set B := (Finset.range (2 ^ w)).filter fun v => v % p = y.val with hB
  -- strings inject into residues below `2 ^ w`
  have h1 : A.card ≤ B.card := by
    refine Finset.card_le_card_of_injOn (fun t => binValLE (BitString.toList t)) ?_ ?_
    · intro t ht
      rw [hA, Finset.mem_coe, Finset.mem_filter] at ht
      rw [hB, Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      refine ⟨by simpa using binValLE_lt (BitString.toList t), ?_⟩
      have := congrArg ZMod.val ht.2
      rw [reduceBits, ZMod.val_natCast] at this
      exact this
    · intro t₁ _ t₂ _ h
      have e := congrArg (bitsOfLenLE w) h
      simp only at e
      have e₁ := bitsOfLenLE_binValLE (BitString.toList t₁)
      have e₂ := bitsOfLenLE_binValLE (BitString.toList t₂)
      rw [BitString.length_toList] at e₁ e₂
      exact BitString.toList_inj.mp (e₁.symm.trans (e.trans e₂))
  -- residues inject into quotients below `2 ^ w / p + 1`
  have h2 : B.card ≤ (Finset.range (2 ^ w / p + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun v => v / p) ?_ ?_
    · intro v hv
      rw [hB, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hv
      rw [Finset.mem_coe, Finset.mem_range]
      show v / p < 2 ^ w / p + 1
      have := Nat.div_le_div_right (c := p) hv.1.le
      omega
    · intro v₁ hv₁ v₂ hv₂ h
      rw [hB, Finset.mem_coe, Finset.mem_filter] at hv₁ hv₂
      simp only at h
      have e₁ := Nat.div_add_mod v₁ p
      have e₂ := Nat.div_add_mod v₂ p
      rw [hv₁.2] at e₁
      rw [hv₂.2] at e₂
      rw [← e₁, ← e₂, h]
  rw [Finset.card_range] at h2
  exact le_trans h1 h2

open Classical in
/-- **Soundness with challenges reduced modulo `p`.** With `p ≤ 2 ^ w`, a false claim is
accepted on at most a `2 (Σ ds) / p` fraction of the `w`-bit challenge strings. -/
theorem card_accept_reduce_le (w : ℕ) {p : ℕ} [hp : Fact p.Prime] (hpw : p ≤ 2 ^ w)
    (ops : List Op) (ds : List ℕ) (f : (ℕ → ZMod p) → ZMod p) (hdeg : ChainDeg ops ds f)
    (a : ℕ → ZMod p) (C : ZMod p) (hC : applyChain ops f a ≠ C)
    (P : SumCheck.Strategy (ZMod p)) :
    ((Finset.univ.filter fun r : Fin ops.length → (Fin w → Bool) =>
        accept ops ds f a C P (fun k => reduceBits w p (r k))).card : ℚ)
      / ((2 : ℚ) ^ w) ^ ops.length ≤ 2 * (ds.take ops.length).sum / p := by
  have hppos : (0 : ℚ) < p := by exact_mod_cast hp.out.pos
  have h := card_accept_comp_le (K := 2 ^ w / p + 1) (reduceBits w p) (fiber_le_reduce w p)
    ops ds f hdeg a C hC P
  rw [card_finArrowBool] at h
  have hK : ((2 ^ w / p + 1 : ℕ) : ℚ) ≤ 2 * 2 ^ w / p := by
    have h1 : ((2 ^ w / p : ℕ) : ℚ) ≤ (2 ^ w : ℚ) / p := by
      rw [le_div_iff₀ hppos]
      exact_mod_cast Nat.div_mul_le_self _ _
    have h2 : (1 : ℚ) ≤ (2 ^ w : ℚ) / p := by
      rw [le_div_iff₀ hppos, one_mul]
      exact_mod_cast hpw
    push_cast
    rw [mul_div_assoc, two_mul]
    linarith
  have hS : (0 : ℚ) ≤ (2 : ℚ) ^ w := by positivity
  cases hops : ops with
  | nil =>
      subst hops
      have hS0 : (ds.take ([] : List Op).length).sum = 0 := by simp
      rw [hS0, zero_mul, zero_mul, Nat.le_zero] at h
      rw [h]
      simp
  | cons o os =>
      subst hops
      rw [div_le_div_iff₀ (by positivity) hppos]
      have h' : ((Finset.univ.filter fun r : Fin (o :: os).length → (Fin w → Bool) =>
          accept (o :: os) ds f a C P (fun k => reduceBits w p (r k))).card : ℚ)
          ≤ (ds.take (o :: os).length).sum * ((2 ^ w / p + 1 : ℕ) : ℚ)
            * ((2 : ℚ) ^ w) ^ os.length := by
        exact_mod_cast h
      calc ((Finset.univ.filter fun r : Fin (o :: os).length → (Fin w → Bool) =>
            accept (o :: os) ds f a C P (fun k => reduceBits w p (r k))).card : ℚ) * p
          ≤ (ds.take (o :: os).length).sum * ((2 ^ w / p + 1 : ℕ) : ℚ)
              * ((2 : ℚ) ^ w) ^ os.length * p := mul_le_mul_of_nonneg_right h' hppos.le
        _ ≤ (ds.take (o :: os).length).sum * (2 * 2 ^ w / p) * ((2 : ℚ) ^ w) ^ os.length
              * p := by
            gcongr
        _ = 2 * (ds.take (o :: os).length).sum * ((2 : ℚ) ^ w) ^ (o :: os).length := by
            rw [List.length_cons, pow_succ]
            field_simp

end OpChain

end Complexity
