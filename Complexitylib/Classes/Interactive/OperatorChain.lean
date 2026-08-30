/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive.SumCheck
public import Complexitylib.SAT.QBF.Arith

/-!
# The operator-chain protocol

⚠️ Unreviewed by Bolton

Shamir's protocol for a quantified Boolean formula, in Shen's form, is a sequence of rounds each
of which strips one *operator* from the arithmetized formula: a sum `Σ_{x_i ∈ {0,1}}` for an
existential quantifier, a product `Π_{x_i ∈ {0,1}}` for a universal one, and a linearization
`L_i` (`QBF.linearize`) to keep degrees small. This file states and proves that protocol for an
arbitrary chain of such operators applied to an arbitrary function `f` on assignments
`ℕ → F`, generalizing `Complexitylib.Classes.Interactive.SumCheck`.

The claim is the value of `applyChain ops f` at a point `a`. In the round for the operator `o`
on variable `x_i`, the prover sends a univariate polynomial `s` standing for the rest of the chain
as a function of `x_i` at `a`; the verifier checks `o.check a s = C` — `s 0 + s 1`, `s 0 * s 1`
or the linear interpolation — picks a random `t`, moves the point to `a[x_i := t]` and the claim
to `s t`. When no operator is left it evaluates `f` itself.

- **Completeness** (`accept_honest`): the honest prover is always accepted.
- **Soundness** (`card_accept_le`): if the claim is false, any prover is accepted on at most
  `(Σ d_k) · |F| ^ (n - 1)` of the `|F| ^ n` challenge vectors, where `d_k` bounds the degree of
  the `k`-th intermediate function in its variable (`ChainDeg`).

## Main definitions

- `OpChain.Op`, `OpChain.Op.apply`, `OpChain.applyChain` — the operators (sum, product, the
  Boolean-preserving "or", linearization) and their chains
- `OpChain.Op.check` — the verifier's consistency check for one operator
- `OpChain.accept`, `OpChain.honest`, `OpChain.ChainDeg`

## Main results

- `OpChain.accept_honest` — completeness
- `OpChain.card_accept_le`, `OpChain.card_accept_le_ratio` — soundness
-/

@[expose] public section

namespace Complexity

namespace OpChain

variable {F : Type} [Field F]

/-! ## Operators -/

/-- The three round operators of Shen's protocol, each on a named variable. -/
inductive Op where
  /-- `Σ_{x_i ∈ {0,1}}`. -/
  | sum (i : ℕ)
  /-- `Π_{x_i ∈ {0,1}}`. -/
  | prod (i : ℕ)
  /-- The De Morgan dual of the product, `1 - Π_{x_i ∈ {0,1}} (1 - ·)`: a Boolean-preserving
  existential quantifier. -/
  | or (i : ℕ)
  /-- Linearization in `x_i`. -/
  | lin (i : ℕ)

/-- The variable an operator acts on. -/
def Op.var : Op → ℕ
  | .sum i => i
  | .prod i => i
  | .or i => i
  | .lin i => i

/-- Apply an operator to a function on assignments. -/
def Op.apply : Op → ((ℕ → F) → F) → (ℕ → F) → F
  | .sum i, g, a => g (Function.update a i 0) + g (Function.update a i 1)
  | .prod i, g, a => g (Function.update a i 0) * g (Function.update a i 1)
  | .or i, g, a => 1 - (1 - g (Function.update a i 0)) * (1 - g (Function.update a i 1))
  | .lin i, g, a => QBF.linearize i g a

/-- Apply a chain of operators, the head outermost. -/
def applyChain : List Op → ((ℕ → F) → F) → (ℕ → F) → F
  | [], f => f
  | o :: os, f => o.apply (applyChain os f)

@[simp] theorem applyChain_nil (f : (ℕ → F) → F) : applyChain [] f = f := rfl

@[simp] theorem applyChain_cons (o : Op) (os : List Op) (f : (ℕ → F) → F) :
    applyChain (o :: os) f = o.apply (applyChain os f) := rfl

/-- The verifier's check of the prover's polynomial against the claim, for one operator. -/
def Op.check : Op → (ℕ → F) → Polynomial F → F
  | .sum _, _, s => s.eval 0 + s.eval 1
  | .prod _, _, s => s.eval 0 * s.eval 1
  | .or _, _, s => 1 - (1 - s.eval 0) * (1 - s.eval 1)
  | .lin i, a, s => (1 - a i) * s.eval 0 + a i * s.eval 1

/-- A polynomial that really is the rest of the chain in the operator's variable passes the
check with the true value. -/
theorem Op.check_eq (o : Op) (g : (ℕ → F) → F) (a : ℕ → F) {s : Polynomial F}
    (hs : ∀ t, s.eval t = g (Function.update a o.var t)) : o.check a s = o.apply g a := by
  cases o with
  | sum i => simp [check, apply, hs, var]
  | prod i => simp [check, apply, hs, var]
  | or i => simp [check, apply, hs, var]
  | lin i => simp [check, apply, hs, var, QBF.linearize]

/-! ## The protocol -/

/-- The verifier accepts the claim `C` about `applyChain ops f` at `a` against the strategy `P`
on the challenges `r`, with degree bounds `ds`. -/
def accept : (ops : List Op) → List ℕ → ((ℕ → F) → F) → (ℕ → F) → F →
    SumCheck.Strategy F → (Fin ops.length → F) → Prop
  | [], _, f, a, C, _, _ => f a = C
  | o :: os, ds, f, a, C, P, r =>
      (P []).natDegree ≤ ds.headD 0 ∧ o.check a (P []) = C ∧
        accept os ds.tail f (Function.update a o.var (r 0)) ((P []).eval (r 0))
          (fun h => P (r 0 :: h)) (Fin.tail r)

/-- The degree bounds `ds` are valid for the chain: the function each round is about is a
polynomial of the stated degree in the round's variable. -/
def ChainDeg : List Op → List ℕ → ((ℕ → F) → F) → Prop
  | [], _, _ => True
  | o :: os, ds, f => QBF.IsPolyIn (ds.headD 0) o.var (applyChain os f) ∧ ChainDeg os ds.tail f

/-! ## The honest prover -/

/-- The honest polynomial for one round: the rest of the chain as a function of the round's
variable at the current point. -/
noncomputable def roundPoly {d i : ℕ} {g : (ℕ → F) → F} (hg : QBF.IsPolyIn d i g)
    (a : ℕ → F) : Polynomial F :=
  Classical.choose (hg a)

theorem roundPoly_natDegree {d i : ℕ} {g : (ℕ → F) → F} (hg : QBF.IsPolyIn d i g)
    (a : ℕ → F) : (roundPoly hg a).natDegree ≤ d :=
  (Classical.choose_spec (hg a)).1

theorem roundPoly_eval {d i : ℕ} {g : (ℕ → F) → F} (hg : QBF.IsPolyIn d i g) (a : ℕ → F)
    (t : F) : (roundPoly hg a).eval t = g (Function.update a i t) :=
  (Classical.choose_spec (hg a)).2 t

/-- The honest strategy: in every round the true polynomial, at the point the challenges so far
have moved to. -/
noncomputable def honest : (ops : List Op) → (ds : List ℕ) → (f : (ℕ → F) → F) →
    ChainDeg ops ds f → (ℕ → F) → SumCheck.Strategy F
  | [], _, _, _, _, _ => 0
  | _ :: _, _, _, h, a, [] => roundPoly h.1 a
  | o :: os, ds, f, h, a, t :: hist => honest os ds.tail f h.2 (Function.update a o.var t) hist

/-- **Completeness.** The honest prover is accepted on every challenge vector. -/
theorem accept_honest : ∀ (ops : List Op) (ds : List ℕ) (f : (ℕ → F) → F)
    (h : ChainDeg ops ds f) (a : ℕ → F) (r : Fin ops.length → F),
    accept ops ds f a (applyChain ops f a) (honest ops ds f h a) r
  | [], _, _, _, _, _ => rfl
  | o :: os, ds, f, h, a, r => by
      refine ⟨roundPoly_natDegree h.1 a, ?_, ?_⟩
      · show o.check a (roundPoly h.1 a) = _
        rw [Op.check_eq o _ a (roundPoly_eval h.1 a), applyChain_cons]
      · show accept os ds.tail f (Function.update a o.var (r 0)) ((roundPoly h.1 a).eval (r 0))
          _ (Fin.tail r)
        rw [roundPoly_eval h.1 a]
        exact accept_honest os ds.tail f h.2 (Function.update a o.var (r 0)) (Fin.tail r)

/-! ## Soundness -/

variable [Fintype F] [DecidableEq F]

open Classical in
/-- **Soundness, counted.** If the claim is false, any prover is accepted on at most
`(Σ ds) · |F| ^ (n - 1)` challenge vectors. -/
theorem card_accept_le : ∀ (ops : List Op) (ds : List ℕ) (f : (ℕ → F) → F),
    ChainDeg ops ds f → ∀ (a : ℕ → F) (C : F), applyChain ops f a ≠ C →
      ∀ P : SumCheck.Strategy F,
        (Finset.univ.filter fun r : Fin ops.length → F => accept ops ds f a C P r).card
          ≤ (ds.take ops.length).sum * Fintype.card F ^ (ops.length - 1)
  | [], _, f, _, a, C, hC, P => by
      have hempty : (Finset.univ.filter fun r : Fin 0 → F => accept [] [] f a C P r) = ∅ := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        exact hC
      simp only [List.length_nil, List.take_zero, List.sum_nil, zero_mul, Nat.le_zero,
        Finset.card_eq_zero]
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact hC
  | o :: os, ds, f, hdeg, a, C, hC, P => by
      set s := P [] with hs
      set d := ds.headD 0 with hd
      set g := applyChain os f with hg
      set n := os.length with hn
      by_cases h1 : s.natDegree ≤ d ∧ o.check a s = C
      · set h := roundPoly hdeg.1 a with hh
        have hne : ∃ t, s.eval t ≠ h.eval t := by
          by_contra hall
          simp only [not_exists, not_not] at hall
          apply hC
          rw [applyChain_cons, ← Op.check_eq o g a
            (fun t => by rw [hall t, hh, roundPoly_eval hdeg.1 a])]
          exact h1.2
        have hbad := SumCheck.card_filter_eval_eq_le h1.1 (roundPoly_natDegree hdeg.1 a) hne
        have hsplit : (Finset.univ.filter
            fun r : Fin (o :: os).length → F => accept (o :: os) ds f a C P r).card
            = ∑ t : F, (Finset.univ.filter
                fun r : Fin n → F => accept (o :: os) ds f a C P (Fin.cons t r)).card := by
          show (Finset.univ.filter
            fun r : Fin (n + 1) → F => accept (o :: os) ds f a C P r).card = _
          rw [Finset.card_filter, Fintype.sum_equiv (consEquiv n)
            (fun r => if accept (o :: os) ds f a C P r then 1 else 0)
            (fun p => if accept (o :: os) ds f a C P (Fin.cons p.1 p.2) then 1 else 0)
            (fun r => by simp [consEquiv]), Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.card_filter]
        have hblock : ∀ t : F, (Finset.univ.filter
            fun r : Fin n → F => accept (o :: os) ds f a C P (Fin.cons t r)).card
            ≤ if s.eval t = h.eval t then Fintype.card F ^ n
              else (ds.tail.take n).sum * Fintype.card F ^ (n - 1) := by
          intro t
          split_ifs with ht
          · refine le_trans (Finset.card_filter_le _ _) (le_of_eq ?_)
            rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
          · have hsub : (Finset.univ.filter
                fun r : Fin n → F => accept (o :: os) ds f a C P (Fin.cons t r))
                ⊆ Finset.univ.filter fun r : Fin n → F =>
                  accept os ds.tail f (Function.update a o.var t) (s.eval t)
                    (fun h => P (t :: h)) r := by
              intro r hr
              rw [Finset.mem_filter] at hr ⊢
              refine ⟨Finset.mem_univ _, ?_⟩
              have := hr.2.2.2
              simpa [Fin.cons_zero, Fin.tail_cons] using this
            refine le_trans (Finset.card_le_card hsub) ?_
            refine card_accept_le os ds.tail f hdeg.2 _ (s.eval t) ?_ _
            rw [← roundPoly_eval hdeg.1 a, ← hh]
            exact fun heq => ht heq.symm
        rw [hsplit]
        have hpow : Fintype.card F * ((ds.tail.take n).sum * Fintype.card F ^ (n - 1))
            ≤ (ds.tail.take n).sum * Fintype.card F ^ n := by
          cases n with
          | zero => simp
          | succ n =>
              rw [Nat.add_sub_cancel, pow_succ]
              exact le_of_eq (by ring)
        have htake : (ds.take (o :: os).length).sum = d + (ds.tail.take n).sum := by
          cases ds with
          | nil => simp [hd, hn]
          | cons d' ds' => simp [hd, hn, List.take_succ_cons]
        calc ∑ t : F, (Finset.univ.filter
                fun r : Fin n → F => accept (o :: os) ds f a C P (Fin.cons t r)).card
            ≤ ∑ t : F, (if s.eval t = h.eval t then Fintype.card F ^ n
                else (ds.tail.take n).sum * Fintype.card F ^ (n - 1)) :=
              Finset.sum_le_sum fun t _ => hblock t
          _ ≤ ∑ t : F, ((if s.eval t = h.eval t then Fintype.card F ^ n else 0)
                + (ds.tail.take n).sum * Fintype.card F ^ (n - 1)) :=
              Finset.sum_le_sum fun t _ => by split_ifs <;> omega
          _ = (Finset.univ.filter fun t : F => s.eval t = h.eval t).card * Fintype.card F ^ n
                + Fintype.card F * ((ds.tail.take n).sum * Fintype.card F ^ (n - 1)) := by
              rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
                Finset.card_filter, Finset.sum_mul]
              congr 1
              refine Finset.sum_congr rfl fun t _ => ?_
              split_ifs <;> simp
          _ ≤ d * Fintype.card F ^ n + (ds.tail.take n).sum * Fintype.card F ^ n :=
              add_le_add (Nat.mul_le_mul_right _ hbad) hpow
          _ = (ds.take (o :: os).length).sum * Fintype.card F ^ ((o :: os).length - 1) := by
              rw [htake, List.length_cons, Nat.add_sub_cancel, ← hn]
              ring
      · have hempty : (Finset.univ.filter
            fun r : Fin (o :: os).length → F => accept (o :: os) ds f a C P r) = ∅ := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          intro hacc
          exact h1 ⟨hacc.1, hacc.2.1⟩
        rw [hempty]
        simp

open Classical in
/-- **Soundness, as a fraction of the challenge vectors**: a false claim is accepted with
probability at most `(Σ ds) / |F|`. -/
theorem card_accept_le_ratio (ops : List Op) (ds : List ℕ) (f : (ℕ → F) → F)
    (hdeg : ChainDeg ops ds f) (a : ℕ → F) (C : F) (hC : applyChain ops f a ≠ C)
    (P : SumCheck.Strategy F) :
    ((Finset.univ.filter fun r : Fin ops.length → F => accept ops ds f a C P r).card : ℚ)
      / (Fintype.card F : ℚ) ^ ops.length ≤ (ds.take ops.length).sum / Fintype.card F := by
  have hF : (0 : ℚ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have h := card_accept_le ops ds f hdeg a C hC P
  have key : ((Finset.univ.filter
        fun r : Fin ops.length → F => accept ops ds f a C P r).card : ℚ) * Fintype.card F
      ≤ (ds.take ops.length).sum * (Fintype.card F : ℚ) ^ ops.length := by
    cases ops with
    | nil =>
        have hS : (ds.take ([] : List Op).length).sum = 0 := by simp
        rw [hS, zero_mul] at h
        rw [Nat.le_zero.mp h]
        simp
    | cons o os =>
        have h' : ((Finset.univ.filter
            fun r : Fin (o :: os).length → F => accept (o :: os) ds f a C P r).card : ℚ)
            ≤ (ds.take (o :: os).length).sum * (Fintype.card F : ℚ) ^ os.length := by
          exact_mod_cast h
        calc ((Finset.univ.filter
              fun r : Fin (o :: os).length → F => accept (o :: os) ds f a C P r).card : ℚ)
              * Fintype.card F
            ≤ (ds.take (o :: os).length).sum * (Fintype.card F : ℚ) ^ os.length
                * Fintype.card F := mul_le_mul_of_nonneg_right h' hF.le
          _ = ((ds.take (o :: os).length).sum : ℚ)
                * (Fintype.card F : ℚ) ^ (o :: os).length := by
              rw [List.length_cons, pow_succ]
              ring
  rw [div_le_div_iff₀ (by positivity) hF]
  exact key

end OpChain

end Complexity
