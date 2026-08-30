/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive.Internal.ModArith
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
# Polynomial evaluation in the polynomial-time algebra

⚠️ Unreviewed by Bolton

The verifier of Shamir's protocol receives a univariate polynomial from the prover, as a string
of `w`-bit coefficient blocks, highest degree first, and evaluates it at `0`, `1` and a random
field element. `hornerEval` does this by Horner's rule with the modular arithmetic of
`Complexitylib.Classes.Interactive.Internal.ModArith`, one block per step of a packed scan.

`hornerEval_encZMod` identifies the result with `Polynomial.eval` over `ZMod p` when the blocks
are the coefficients of a polynomial of degree below their number — so the length of the
prover's message is exactly the degree check the verifier needs.

## Main definitions

- `hornerVal` — Horner's rule on a list of coefficients, highest degree first
- `hornerStep`, `hornerStepP`, `hornerEval` — the scan and its packed form
- `coeffBlocks` — a polynomial's coefficients as blocks

## Main results

- `hornerVal_eq_eval` — Horner's rule is evaluation
- `binValLE_hornerEval` — what the scan computes
- `hornerEval_encZMod` — on residues it is `Polynomial.eval`
- `hornerEvalFn_mem_FP` — it is polynomial-time
-/

@[expose] public section

namespace Complexity

open Cobham

/-! ## Horner's rule -/

/-- Horner's rule on coefficients listed highest degree first. -/
def hornerVal {R : Type} [Semiring R] (x : R) (cs : List R) : R :=
  cs.foldl (fun acc c => acc * x + c) 0

theorem foldl_horner {R : Type} [CommSemiring R] (x : R) (f : ℕ → R) :
    ∀ (n : ℕ) (init : R),
      ((List.range n).reverse.map f).foldl (fun acc c => acc * x + c) init
        = init * x ^ n + ∑ i ∈ Finset.range n, f i * x ^ i
  | 0, init => by simp
  | n + 1, init => by
      rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.map_cons, List.foldl_cons, foldl_horner x f n, Finset.sum_range_succ, pow_succ]
      ring

/-- **Horner's rule is evaluation.** -/
theorem hornerVal_eq_eval {R : Type} [CommSemiring R] (p : Polynomial R) (n : ℕ)
    (hn : p.natDegree < n) (x : R) :
    hornerVal x ((List.range n).reverse.map p.coeff) = p.eval x := by
  rw [hornerVal, foldl_horner, zero_mul, zero_add, Polynomial.eval_eq_sum_range' hn]

/-! ## The scan -/

/-- One step: multiply the accumulator by the point and add the next coefficient block. -/
noncomputable def hornerStep (q x : List Bool) : List Bool × List Bool → List Bool × List Bool
  | (acc, []) => (acc, [])
  | (acc, b :: t) =>
      (addMod q (mulMod q acc x) ((b :: t).take q.length), (b :: t).drop q.length)

theorem hornerStep_nil (q x acc : List Bool) : hornerStep q x (acc, []) = (acc, []) := rfl

theorem hornerStep_block (q x acc c rest : List Bool) (hc : c.length = q.length)
    (hne : c ≠ []) :
    hornerStep q x (acc, c ++ rest) = (addMod q (mulMod q acc x) c, rest) := by
  obtain ⟨b, t, rfl⟩ : ∃ b t, c = b :: t := by
    cases c with
    | nil => exact absurd rfl hne
    | cons b t => exact ⟨b, t, rfl⟩
  rw [List.cons_append, hornerStep, ← List.cons_append, List.take_left' hc, List.drop_left' hc]

theorem hornerStep_iterate_nil (q x acc : List Bool) (n : ℕ) :
    (hornerStep q x)^[n] (acc, []) = (acc, []) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, hornerStep_nil, ih]

theorem hornerStep_iterate_length (q x acc rest : List Bool) (n : ℕ) :
    ((hornerStep q x)^[n] (acc, rest)).1.length ≤ max acc.length q.length ∧
      ((hornerStep q x)^[n] (acc, rest)).2.length ≤ rest.length := by
  induction n generalizing acc rest with
  | zero => exact ⟨le_max_left _ _, le_rfl⟩
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      cases rest with
      | nil => simpa [hornerStep_nil] using ih acc []
      | cons b t =>
          rw [hornerStep]
          have := ih (addMod q (mulMod q acc x) ((b :: t).take q.length)) ((b :: t).drop q.length)
          refine ⟨le_trans this.1 (max_le ?_ (le_max_right _ _)), le_trans this.2 (by simp)⟩
          exact le_trans (addMod_length_le _ _ _) (le_trans (mulMod_length_le _ _ _)
            (le_max_right _ _))

/-- **The scan computes Horner's rule** on coefficient blocks of the modulus's width. -/
theorem hornerStep_iterate_run (q x : List Bool) (hx : x.length = q.length)
    (hxq : binValLE x < binValLE q) (hq : 0 < q.length) :
    ∀ (cs : List (List Bool)) (acc : List Bool), (∀ c ∈ cs, c.length = q.length) →
      (∀ c ∈ cs, binValLE c < binValLE q) → acc.length = q.length →
      binValLE acc < binValLE q →
      ∃ acc' : List Bool, (hornerStep q x)^[cs.length] (acc, cs.flatten) = (acc', []) ∧
        acc'.length = q.length ∧
        binValLE acc' = (cs.map binValLE).foldl (fun a c => (a * binValLE x + c) % binValLE q)
          (binValLE acc)
  | [], acc, _, _, hlen, _ => ⟨acc, by simp, hlen, by simp⟩
  | c :: cs, acc, hcl, hcv, hlen, hacc => by
      have hc := hcl c List.mem_cons_self
      have hcne : c ≠ [] := by
        intro h
        rw [h] at hc
        simp at hc
        omega
      rw [List.length_cons, Function.iterate_succ_apply, List.flatten_cons,
        hornerStep_block q x acc c cs.flatten hc hcne]
      obtain ⟨hmv, hml⟩ := binValLE_mulMod q acc x hlen hacc
      have hpos : 0 < binValLE q := by omega
      have hmlt : binValLE (mulMod q acc x) < binValLE q := by rw [hmv]; exact Nat.mod_lt _ hpos
      have hav := binValLE_addMod q _ c hml hc hmlt (hcv c List.mem_cons_self)
      obtain ⟨acc', h1, h2, h3⟩ := hornerStep_iterate_run q x hx hxq hq cs _
        (fun d hd => hcl d (List.mem_cons_of_mem _ hd))
        (fun d hd => hcv d (List.mem_cons_of_mem _ hd))
        (addMod_length q _ c hml hc) (by rw [hav]; exact Nat.mod_lt _ hpos)
      refine ⟨acc', h1, h2, ?_⟩
      rw [h3, List.map_cons, List.foldl_cons, hav, hmv, Nat.add_mod, Nat.mod_mod,
        ← Nat.add_mod]

/-- The packed state: the accumulator, the remaining blocks, the point and the modulus. -/
def hornerPack (acc rest x q : List Bool) : List Bool := pair acc (pair rest (pair x q))

/-- One step of the packed scan. -/
noncomputable def hornerStepP (z : List Bool) : List Bool :=
  selectHead (lenLeFlag (pairFst (pairSnd z)) [false])
    (hornerPack
      (addMod (pairSnd (pairSnd (pairSnd z)))
        (mulMod (pairSnd (pairSnd (pairSnd z))) (pairFst z) (pairFst (pairSnd (pairSnd z))))
        ((pairFst (pairSnd z)).take (pairSnd (pairSnd (pairSnd z))).length))
      ((pairFst (pairSnd z)).drop (pairSnd (pairSnd (pairSnd z))).length)
      (pairFst (pairSnd (pairSnd z))) (pairSnd (pairSnd (pairSnd z))))
    z

theorem hornerStepP_pack (acc rest x q : List Bool) :
    hornerStepP (hornerPack acc rest x q)
      = hornerPack (hornerStep q x (acc, rest)).1 (hornerStep q x (acc, rest)).2 x q := by
  rw [hornerStepP, hornerPack]
  simp only [pairFst_pair, pairSnd_pair]
  cases rest with
  | nil =>
      have hflag : lenLeFlag ([] : List Bool) [false] = [false] := rfl
      rw [selectHead, hflag]
      simp [hornerStep_nil, hornerPack]
  | cons b t =>
      have hflag : lenLeFlag (b :: t) [false] = [true] :=
        (lenLeFlag_eq_true_iff (b :: t) [false]).mpr (by simp)
      rw [selectHead, hflag]
      simp only [List.head?_cons, reduceIte]
      rw [hornerStep]

theorem hornerStepP_iterate (x q : List Bool) (s : List Bool × List Bool) (n : ℕ) :
    hornerStepP^[n] (hornerPack s.1 s.2 x q)
      = hornerPack ((hornerStep q x)^[n] s).1 ((hornerStep q x)^[n] s).2 x q := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, hornerStepP_pack, ih (hornerStep q x s),
        Function.iterate_succ_apply]

/-- Evaluate the coefficient string `cs` at `x` modulo `q`, running the scan once per bit of
`cs` (the extra steps on an exhausted string do nothing). -/
noncomputable def hornerEval (q x cs : List Bool) : List Bool :=
  pairFst (hornerStepP^[cs.length] (hornerPack (List.replicate q.length false) cs x q))

/-- **What the scan computes.** -/
theorem binValLE_hornerEval (q x : List Bool) (hx : x.length = q.length)
    (hxq : binValLE x < binValLE q) (hq : 0 < q.length) (cs : List (List Bool))
    (hcl : ∀ c ∈ cs, c.length = q.length) (hcv : ∀ c ∈ cs, binValLE c < binValLE q) :
    binValLE (hornerEval q x cs.flatten)
        = (cs.map binValLE).foldl (fun a c => (a * binValLE x + c) % binValLE q) 0 ∧
      (hornerEval q x cs.flatten).length = q.length := by
  have hpos : 0 < binValLE q := by omega
  obtain ⟨acc', h1, h2, h3⟩ := hornerStep_iterate_run q x hx hxq hq cs
    (List.replicate q.length false) hcl hcv (by simp) (by rw [binValLE_replicate_false]; exact hpos)
  have hlen : cs.length ≤ cs.flatten.length := by
    rw [List.length_flatten]
    have : ∀ c ∈ cs, 1 ≤ c.length := fun c hc => by rw [hcl c hc]; exact hq
    clear h1 h2 h3 hcl hcv
    induction cs with
    | nil => simp
    | cons c cs ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have h1 := this c List.mem_cons_self
        have h2 := ih fun d hd => this d (List.mem_cons_of_mem _ hd)
        omega
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hlen
  rw [hornerEval, hm, add_comm, Function.iterate_add_apply,
    hornerStepP_iterate x q (List.replicate q.length false, cs.flatten), h1,
    hornerStepP_iterate x q (acc', []), hornerStep_iterate_nil, hornerPack, pairFst_pair]
  rw [binValLE_replicate_false] at h3
  exact ⟨h3, h2⟩

theorem hornerStepP_mem_FP : hornerStepP ∈ FP := by
  have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hfst : ∀ {a : List Bool → List Bool}, a ∈ FP → (fun z => pairFst (a z)) ∈ FP := by
    intro a ha
    have := mem_FP_comp ha Cobham.fstBlock_mem_FP
    simpa [Function.comp] using this
  have hsnd : ∀ {a : List Bool → List Bool}, a ∈ FP → (fun z => pairSnd (a z)) ∈ FP := by
    intro a ha
    have := mem_FP_comp ha Cobham.sndBlock_mem_FP
    simpa [Function.comp] using this
  have hacc := hfst hid
  have hw := hsnd hid
  have hrest := hfst hw
  have hww := hsnd hw
  have hx := hfst hww
  have hq := hsnd hww
  have hone : (fun _ : List Bool => ([false] : List Bool)) ∈ FP := constFn_mem_FP [false]
  exact Cobham.selectHeadFn_mem_FP (lenLeFlagFn_mem_FP hrest hone)
    (Cobham.pairFn_mem_FP
      (addModFn_mem_FP hq (mulModFn_mem_FP hq hacc hx) (Cobham.takeLenFn_mem_FP hq hrest))
      (Cobham.pairFn_mem_FP (dropLenFn_mem_FP hq hrest) (Cobham.pairFn_mem_FP hx hq))) hid

theorem hornerEvalFn_mem_FP {a b c : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP)
    (hc : c ∈ FP) : (fun z => hornerEval (a z) (b z) (c z)) ∈ FP := by
  have hinit : (fun z => hornerPack (List.replicate (a z).length false) (c z) (b z) (a z))
      ∈ FP :=
    Cobham.pairFn_mem_FP (zeroBlockFn_mem_FP ha)
      (Cobham.pairFn_mem_FP hc (Cobham.pairFn_mem_FP hb ha))
  have hwidth : (fun z => hornerPack (a z) (c z) (b z) (a z)) ∈ FP :=
    Cobham.pairFn_mem_FP ha (Cobham.pairFn_mem_FP hc (Cobham.pairFn_mem_FP hb ha))
  have hbound : ∀ z, ∀ n ≤ (c z).length,
      (hornerStepP^[n] (hornerPack (List.replicate (a z).length false) (c z) (b z) (a z))).length
        ≤ (hornerPack (a z) (c z) (b z) (a z)).length := by
    intro z n _
    rw [hornerStepP_iterate (b z) (a z) (List.replicate (a z).length false, c z)]
    obtain ⟨h1, h2⟩ := hornerStep_iterate_length (a z) (b z) (List.replicate (a z).length false)
      (c z) n
    simp only [List.length_replicate, max_self] at h1
    rw [hornerPack, hornerPack, pair_length, pair_length, pair_length, pair_length, pair_length,
      pair_length]
    omega
  have h := Cobham.iterate_mem_FP hornerStepP_mem_FP hinit hc hwidth hbound
  have h1 := mem_FP_comp h Cobham.fstBlock_mem_FP
  simpa [Function.comp, hornerEval] using h1

/-! ## Residues -/

/-- The coefficients of a polynomial over `ZMod p` below degree `n`, as `w`-bit blocks, highest
degree first. -/
def coeffBlocks (w : ℕ) {p : ℕ} (f : Polynomial (ZMod p)) (n : ℕ) : List (List Bool) :=
  (List.range n).reverse.map fun i => encZMod w (f.coeff i)

theorem coeffBlocks_length (w : ℕ) {p : ℕ} (f : Polynomial (ZMod p)) (n : ℕ) :
    (coeffBlocks w f n).length = n := by
  simp [coeffBlocks]

theorem coeffBlocks_flatten_length (w : ℕ) {p : ℕ} (f : Polynomial (ZMod p)) (n : ℕ) :
    (coeffBlocks w f n).flatten.length = n * w := by
  rw [List.length_flatten, coeffBlocks, List.map_map, List.map_reverse]
  have : ((List.range n).map (List.length ∘ fun i => encZMod w (f.coeff i)))
      = (List.range n).map fun _ => w := by
    refine List.map_congr_left fun i _ => ?_
    simp
  rw [this, List.sum_reverse, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]

/-- Horner's rule in `ZMod p`, block by block, is Horner's rule on the residues. -/
theorem foldl_mod_encZMod (w : ℕ) {p : ℕ} [NeZero p] (hp : p < 2 ^ w) (x : ZMod p) :
    ∀ (cs : List (ZMod p)) (acc : ZMod p),
      ((cs.map fun c => (encZMod w c : List Bool)).map binValLE).foldl
          (fun a c => (a * x.val + c) % p) acc.val
        = (cs.foldl (fun a c => a * x + c) acc).val
  | [], acc => rfl
  | c :: cs, acc => by
      rw [List.map_cons, List.map_cons, List.foldl_cons, List.foldl_cons, binValLE_encZMod w hp,
        ← foldl_mod_encZMod w hp x cs (acc * x + c)]
      congr 1
      rw [ZMod.val_add, ZMod.val_mul, Nat.mod_add_mod]

/-- **On residues the scan is `Polynomial.eval`.** -/
theorem hornerEval_encZMod (w : ℕ) {p : ℕ} [NeZero p] (hp : p < 2 ^ w) (hw : 0 < w)
    (f : Polynomial (ZMod p)) (n : ℕ) (hn : f.natDegree < n) (x : ZMod p) :
    hornerEval (bitsOfLenLE w p) (encZMod w x) (coeffBlocks w f n).flatten
      = encZMod w (f.eval x) := by
  have hpv : binValLE (bitsOfLenLE w p) = p := binValLE_bitsOfLenLE w p hp
  obtain ⟨hval, hlen⟩ := binValLE_hornerEval (bitsOfLenLE w p) (encZMod w x) (by simp)
    (by rw [binValLE_encZMod w hp, hpv]; exact ZMod.val_lt x) (by simpa using hw)
    (coeffBlocks w f n) (fun c hc => by
      rw [coeffBlocks, List.mem_map] at hc
      obtain ⟨i, _, rfl⟩ := hc
      simp)
    (fun c hc => by
      rw [coeffBlocks, List.mem_map] at hc
      obtain ⟨i, _, rfl⟩ := hc
      rw [binValLE_encZMod w hp, hpv]
      exact ZMod.val_lt _)
  refine eq_of_binValLE_eq ?_ ?_
  · rw [hlen, bitsOfLenLE_length, encZMod_length]
  · have hmap : (fun i => encZMod w (f.coeff i)) = (fun c : ZMod p => encZMod w c) ∘ f.coeff :=
      rfl
    rw [hval, binValLE_encZMod w hp, binValLE_encZMod w hp, hpv, coeffBlocks, hmap,
      ← List.map_map, show (0 : ℕ) = (0 : ZMod p).val from ZMod.val_zero.symm,
      foldl_mod_encZMod w hp x, ← hornerVal_eq_eval f n hn x, hornerVal]

end Complexity
