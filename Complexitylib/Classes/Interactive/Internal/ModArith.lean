/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.BinArith
public import Complexitylib.Classes.Containments.Internal.WitnessEnum
public import Complexitylib.Classes.PCP.Internal.UnaryList
public import Complexitylib.Classes.PCP.Internal.CoinEnum
public import Mathlib.Data.ZMod.Basic

/-!
# Modular arithmetic in the polynomial-time algebra

⚠️ Unreviewed by Bolton

A polynomial-time verifier for Shamir's protocol has to add and multiply field elements. This
file provides fixed-width modular addition and multiplication on little-endian bitstrings, built
from the adder and comparator of `Complexitylib.Classes.Containments.Internal.BinArith`:

- `subBits x p` is `x - p` in two's complement, the adder run with carry-in on `x` and the
  complement of `p`;
- `addMod p u v` adds and subtracts `p` back when the sum carries out or reaches `p`;
- `mulMod p u v` is double-and-add over the bits of `v`, most significant first.

Each comes with a value lemma (`binValLE_addMod`, `binValLE_mulMod`) and membership in `FP`,
and `encZMod` packages the values of `ZMod p` as strings, with `addMod_encZMod` and
`mulMod_encZMod` saying the string operations are the field operations.

## Main definitions

- `notBits`, `subBits`, `addMod`, `mulMod` — the operations
- `encZMod` — a residue as a bitstring

## Main results

- `binValLE_subBits`, `binValLE_addMod`, `binValLE_mulMod` — what they compute
- `addModFn_mem_FP`, `mulModFn_mem_FP` — they are polynomial-time
- `addMod_encZMod`, `mulMod_encZMod` — on residues they are the field operations
-/

@[expose] public section

namespace Complexity

open Cobham

/-! ## Complement -/

/-- The bitwise complement. -/
noncomputable def notBits (x : List Bool) : List Bool := xorSuffix x (marks x)

theorem notBits_eq (x : List Bool) : notBits x = x.map not := by
  rw [notBits, marks_eq, xorSuffix_eq_zipWith_of_length _ _ (by simp)]
  induction x with
  | nil => rfl
  | cons b t ih =>
      rw [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, List.map_cons, ih]
      cases b <;> rfl

@[simp] theorem notBits_length (x : List Bool) : (notBits x).length = x.length := by
  rw [notBits_eq, List.length_map]

theorem binValLE_notBits (x : List Bool) :
    binValLE (notBits x) + binValLE x + 1 = 2 ^ x.length := by
  rw [notBits_eq]
  induction x with
  | nil => rfl
  | cons b t ih =>
      rw [List.map_cons, binValLE_cons, binValLE_cons, List.length_cons, pow_succ]
      cases b <;> simp only [Bool.not_false, Bool.not_true, Bool.toNat_true, Bool.toNat_false] <;>
        omega

theorem notBitsFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => notBits (a z)) ∈ FP :=
  binFn_mem_FP (g := xorSuffix) (Cobham.xorSuffix_mem (Cobham.proj 0) (Cobham.proj 1)) ha
    (marks_mem_FP ha)

/-! ## Subtraction -/

/-- The adder run with carry-in. -/
def addRun1 (u v : List Bool) : List Bool := addStepP^[u.length] (addPack [true] [] u v)

theorem addRun1_eq (u v : List Bool) (h : v.length = u.length) :
    addRun1 u v = addPack [(addBitsLE true u v).1] (addBitsLE true u v).2 [] [] := by
  rw [addRun1, addStepP_iterate_args, addStep_iterate_run true [] u v h]
  simp

theorem addRun1Fn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => addRun1 (a z) (b z)) ∈ FP := by
  have hinit : (fun z => addPack [true] [] (a z) (b z)) ∈ FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP [true])
      (Cobham.pairFn_mem_FP (constFn_mem_FP []) (Cobham.pairFn_mem_FP ha hb))
  have hwidth : (fun z => addPack [true] (a z) (a z) (b z)) ∈ FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP [true])
      (Cobham.pairFn_mem_FP ha (Cobham.pairFn_mem_FP ha hb))
  have hbound : ∀ z, ∀ n ≤ (a z).length,
      (addStepP^[n] (addPack [true] [] (a z) (b z))).length
        ≤ (addPack [true] (a z) (a z) (b z)).length := by
    intro z n _
    rw [addStepP_iterate_args]
    obtain ⟨h1, h2, h3⟩ := addStep_iterate_length true [] (a z) (b z) n
    have hone1 : ([true] : List Bool).length = 1 := rfl
    rw [addPack_length, addPack_length]
    simp only [List.length_nil] at h2
    omega
  exact Cobham.iterate_mem_FP addStepP_mem_FP hinit ha hwidth hbound

/-- `x - p` in two's complement: `x + ¬p + 1`, the carry out dropped. -/
noncomputable def subBits (x p : List Bool) : List Bool := pairFst (pairSnd (addRun1 x (notBits p)))

theorem subBits_eq (x p : List Bool) (h : p.length = x.length) :
    subBits x p = (addBitsLE true x (notBits p)).2 := by
  rw [subBits, addRun1_eq x (notBits p) (by rw [notBits_length, h]), addPack]
  simp

theorem subBits_length (x p : List Bool) (h : p.length = x.length) :
    (subBits x p).length = x.length := by
  rw [subBits_eq x p h, addBitsLE_length]

/-- **What subtraction computes**: `x - p`, wrapping around at `2 ^ |x|`. -/
theorem binValLE_subBits (x p : List Bool) (h : p.length = x.length) :
    binValLE (subBits x p)
      = if binValLE p ≤ binValLE x then binValLE x - binValLE p
        else binValLE x + 2 ^ x.length - binValLE p := by
  rw [subBits_eq x p h]
  have hk := addBitsLE_binValLE true x (notBits p) (by rw [notBits_length, h])
  have hn := binValLE_notBits p
  rw [h] at hn
  have hs := binValLE_lt (addBitsLE true x (notBits p)).2
  rw [addBitsLE_length] at hs
  have hp := binValLE_lt p
  rw [h] at hp
  simp only [Bool.toNat_true] at hk
  split_ifs with hle
  · cases hc : (addBitsLE true x (notBits p)).1
    · rw [hc, Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at hk
      omega
    · rw [hc, Bool.toNat_true, Nat.one_mul] at hk
      omega
  · cases hc : (addBitsLE true x (notBits p)).1
    · rw [hc, Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at hk
      omega
    · rw [hc, Bool.toNat_true, Nat.one_mul] at hk
      omega

theorem subBitsFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => subBits (a z) (b z)) ∈ FP := by
  have h1 := mem_FP_comp (addRun1Fn_mem_FP ha (notBitsFn_mem_FP hb)) Cobham.sndBlock_mem_FP
  have h2 := mem_FP_comp h1 Cobham.fstBlock_mem_FP
  simpa [Function.comp, subBits] using h2

/-! ## Modular addition -/

/-- Add, and subtract `p` back if the sum carried out or reached `p`. -/
noncomputable def addMod (p u v : List Bool) : List Bool :=
  selectHead (orBit (addCarry u v) (notBit (ltFlag (addBits u v) p)))
    (subBits (addBits u v) p) (addBits u v)

theorem addMod_length_le (p u v : List Bool) : (addMod p u v).length ≤ u.length := by
  rw [addMod]
  refine le_trans (selectHead_length_le _ _ _) (max_le ?_ ?_)
  · rw [subBits, addRun1]
    have := addStep_iterate_length true [] (addBits u v) (notBits p) (addBits u v).length
    rw [addStepP_iterate_args]
    have hab : (addBits u v).length ≤ u.length := by
      rw [addBits, addRun]
      have h2 := addStep_iterate_length false [] u v u.length
      rw [addStepP_iterate_args, addPack]
      simp only [pairSnd_pair, pairFst_pair]
      simp only [List.length_nil, Nat.zero_add] at h2
      omega
    rw [addPack]
    simp only [pairSnd_pair, pairFst_pair]
    simp only [List.length_nil, Nat.zero_add] at this
    omega
  · rw [addBits, addRun]
    have h2 := addStep_iterate_length false [] u v u.length
    rw [addStepP_iterate_args, addPack]
    simp only [pairSnd_pair, pairFst_pair]
    simp only [List.length_nil, Nat.zero_add] at h2
    omega

/-- The two flags the selector reads, as Booleans. -/
theorem addMod_eq (p u v : List Bool) (hu : u.length = p.length) (hv : v.length = p.length) :
    addMod p u v
      = if (addBitsLE false u v).1 = true ∨ ltBitsLE false (addBitsLE false u v).2 p = false
        then subBits (addBitsLE false u v).2 p else (addBitsLE false u v).2 := by
  have h : v.length = u.length := hv.trans hu.symm
  have hab : (addBits u v).length = u.length := addBits_length u v h
  rw [addMod, addCarry_eq u v h, ltFlag_eq (addBits u v) p (by rw [hab, hu]), addBits_eq u v h]
  cases (addBitsLE false u v).1 <;> cases ltBitsLE false (addBitsLE false u v).2 p <;>
    simp [orBit, notBit, caseBit₀]

theorem addMod_length (p u v : List Bool) (hu : u.length = p.length) (hv : v.length = p.length) :
    (addMod p u v).length = p.length := by
  have h : v.length = u.length := hv.trans hu.symm
  rw [addMod_eq p u v hu hv]
  split_ifs
  · rw [subBits_length _ _ (by rw [addBitsLE_length, hu]), addBitsLE_length, hu]
  · rw [addBitsLE_length, hu]

/-- Remainders below twice the modulus. -/
theorem mod_of_lt_two_mul {n p : ℕ} (hn : n < 2 * p) :
    n % p = if p ≤ n then n - p else n := by
  split_ifs with hle
  · rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

/-- **What modular addition computes.** -/
theorem binValLE_addMod (p u v : List Bool) (hu : u.length = p.length)
    (hv : v.length = p.length) (hup : binValLE u < binValLE p) (hvp : binValLE v < binValLE p) :
    binValLE (addMod p u v) = (binValLE u + binValLE v) % binValLE p := by
  have h : v.length = u.length := hv.trans hu.symm
  have hk := addBitsLE_binValLE false u v h
  simp only [Bool.toNat_false, Nat.add_zero] at hk
  set s := (addBitsLE false u v).2 with hs
  set c := (addBitsLE false u v).1 with hc
  have hslen : s.length = u.length := by rw [hs, addBitsLE_length]
  have hsl := binValLE_lt s
  rw [hslen] at hsl
  have hpl := binValLE_lt p
  rw [← hu] at hpl
  have hsub := binValLE_subBits s p (by rw [hslen, hu])
  rw [hslen] at hsub
  have hlt : ltBitsLE false s p = true ↔ binValLE s < binValLE p := by
    have := ltFlag_eq_true_iff s p (by rw [hslen, hu])
    rw [ltFlag_eq s p (by rw [hslen, hu])] at this
    simpa using this
  have hpos : 0 < binValLE p := by omega
  have hmod := mod_of_lt_two_mul (n := binValLE u + binValLE v) (p := binValLE p) (by omega)
  rw [addMod_eq p u v hu hv, ← hs, ← hc, hmod]
  cases hcv : c
  · rw [hcv, Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at hk
    cases hl : ltBitsLE false s p
    · simp only [Bool.false_eq_true, false_or, if_true]
      have hnlt : ¬ binValLE s < binValLE p := by
        intro hh
        have := hlt.mpr hh
        rw [hl] at this
        exact Bool.false_ne_true this
      rw [hsub, if_pos (by omega), if_pos (by omega), hk]
    · simp only [Bool.false_eq_true, Bool.true_eq_false, or_self, if_false]
      have := hlt.mp hl
      rw [if_neg (by omega), hk]
  · rw [hcv, Bool.toNat_true, Nat.one_mul] at hk
    simp only [true_or, if_true]
    rw [hsub, if_neg (by omega), if_pos (by omega)]
    omega

theorem addModFn_mem_FP {a b c : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP)
    (hc : c ∈ FP) : (fun z => addMod (a z) (b z) (c z)) ∈ FP :=
  Cobham.selectHeadFn_mem_FP
    (orBitFn_mem_FP (addCarryFn_mem_FP hb hc)
      (notBitFn_mem_FP (ltFlagFn_mem_FP (addBitsFn_mem_FP hb hc) ha)))
    (subBitsFn_mem_FP (addBitsFn_mem_FP hb hc) ha) (addBitsFn_mem_FP hb hc)

/-! ## Modular multiplication -/

/-- One step of double-and-add: double the accumulator and add `u` if the next (most
significant remaining) bit of the multiplier is set. -/
noncomputable def mulStep (p u : List Bool) : List Bool × List Bool → List Bool × List Bool
  | (acc, []) => (acc, [])
  | (acc, b :: rest) =>
      (addMod p (addMod p acc acc) (if b then u else List.replicate u.length false), rest)

theorem mulStep_iterate_length (p u : List Bool) (acc rest : List Bool) (n : ℕ) :
    ((mulStep p u)^[n] (acc, rest)).1.length ≤ acc.length ∧
      ((mulStep p u)^[n] (acc, rest)).2.length ≤ rest.length := by
  induction n generalizing acc rest with
  | zero => exact ⟨le_rfl, le_rfl⟩
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      cases rest with
      | nil => simpa [mulStep] using ih acc []
      | cons b t =>
          rw [mulStep]
          have := ih (addMod p (addMod p acc acc)
            (if b then u else List.replicate u.length false)) t
          refine ⟨le_trans this.1 (le_trans (addMod_length_le _ _ _) (addMod_length_le _ _ _)),
            le_trans this.2 (by simp)⟩

/-- **Double-and-add computes the product modulo `p`.** -/
theorem mulStep_iterate_run (p u : List Bool) (hu : u.length = p.length)
    (hup : binValLE u < binValLE p) :
    ∀ (rest pre acc : List Bool), acc.length = p.length →
      binValLE acc = (binValLE u * binValLE pre.reverse) % binValLE p →
      ∃ acc' : List Bool, (mulStep p u)^[rest.length] (acc, rest) = (acc', []) ∧
        acc'.length = p.length ∧
        binValLE acc' = (binValLE u * binValLE (pre ++ rest).reverse) % binValLE p
  | [], pre, acc, hlen, hval => ⟨acc, by simp, hlen, by simpa using hval⟩
  | b :: rest, pre, acc, hlen, hval => by
      have hpos : 0 < binValLE p := by omega
      set bu := if b then u else List.replicate u.length false with hbu
      have hbulen : bu.length = p.length := by
        rw [hbu]; split_ifs <;> simp [hu]
      have hbuval : binValLE bu = b.toNat * binValLE u := by
        rw [hbu]; cases b <;> simp [binValLE_replicate_false]
      have hbup : binValLE bu < binValLE p := by rw [hbuval]; cases b <;> simp <;> omega
      have hacc : binValLE acc < binValLE p := by rw [hval]; exact Nat.mod_lt _ hpos
      have h2 : binValLE (addMod p acc acc) = (2 * binValLE acc) % binValLE p := by
        rw [binValLE_addMod p acc acc hlen hlen hacc hacc]; ring_nf
      have h2len : (addMod p acc acc).length = p.length := addMod_length p acc acc hlen hlen
      have h2lt : binValLE (addMod p acc acc) < binValLE p := by rw [h2]; exact Nat.mod_lt _ hpos
      have hstep : binValLE (addMod p (addMod p acc acc) bu)
          = (binValLE u * binValLE (pre ++ [b]).reverse) % binValLE p := by
        rw [binValLE_addMod p _ _ h2len hbulen h2lt hbup, h2, hbuval, hval,
          List.reverse_append, List.reverse_singleton, List.singleton_append, binValLE_cons]
        have hm1 : 2 * (binValLE u * binValLE pre.reverse % binValLE p) % binValLE p
            ≡ 2 * (binValLE u * binValLE pre.reverse) [MOD binValLE p] :=
          (Nat.mod_modEq _ _).trans (Nat.ModEq.mul_left 2 (Nat.mod_modEq _ _))
        have hm2 := hm1.add_right (b.toNat * binValLE u)
        rw [Nat.ModEq] at hm2
        rw [hm2]
        congr 1
        ring
      rw [List.length_cons, Function.iterate_succ_apply, mulStep]
      obtain ⟨acc', h1, h2', h3⟩ := mulStep_iterate_run p u hu hup rest (pre ++ [b]) _
        (addMod_length p _ _ h2len hbulen) hstep
      exact ⟨acc', h1, h2', by rwa [List.append_assoc, List.singleton_append] at h3⟩

/-- The packed state: the accumulator, the remaining multiplier bits, the multiplicand and the
modulus. -/
def mulPack (acc rest u p : List Bool) : List Bool := pair acc (pair rest (pair u p))

/-- One step of the packed scan. -/
noncomputable def mulStepP (z : List Bool) : List Bool :=
  selectHead (lenLeFlag (pairFst (pairSnd z)) [false])
    (mulPack
      (addMod (pairSnd (pairSnd (pairSnd z)))
        (addMod (pairSnd (pairSnd (pairSnd z))) (pairFst z) (pairFst z))
        (selectHead (bit1 (pairFst (pairSnd z))) (pairFst (pairSnd (pairSnd z)))
          (List.replicate (pairFst (pairSnd (pairSnd z))).length false)))
      ((pairFst (pairSnd z)).drop 1) (pairFst (pairSnd (pairSnd z)))
      (pairSnd (pairSnd (pairSnd z))))
    z

theorem mulStepP_pack (acc rest u p : List Bool) :
    mulStepP (mulPack acc rest u p)
      = mulPack (mulStep p u (acc, rest)).1 (mulStep p u (acc, rest)).2 u p := by
  rw [mulStepP, mulPack]
  simp only [pairFst_pair, pairSnd_pair]
  cases rest with
  | nil =>
      have hflag : lenLeFlag ([] : List Bool) [false] = [false] := rfl
      rw [selectHead, hflag]
      simp [mulStep, mulPack]
  | cons b t =>
      have hflag : lenLeFlag (b :: t) [false] = [true] :=
        (lenLeFlag_eq_true_iff (b :: t) [false]).mpr (by simp)
      rw [selectHead, hflag]
      simp only [List.head?_cons, reduceIte]
      rw [mulStep, mulPack, bit1_cons]
      cases b <;> simp [mulPack]

theorem mulStepP_iterate (u p : List Bool) (s : List Bool × List Bool) (n : ℕ) :
    mulStepP^[n] (mulPack s.1 s.2 u p)
      = mulPack ((mulStep p u)^[n] s).1 ((mulStep p u)^[n] s).2 u p := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, mulStepP_pack, ih (mulStep p u s),
        Function.iterate_succ_apply]

/-- The product modulo `p`, by the packed scan over the multiplier's bits, most significant
first. -/
noncomputable def mulMod (p u v : List Bool) : List Bool :=
  pairFst (mulStepP^[v.length] (mulPack (List.replicate p.length false) v.reverse u p))

/-- **What modular multiplication computes.** -/
theorem binValLE_mulMod (p u v : List Bool) (hu : u.length = p.length)
    (hup : binValLE u < binValLE p) :
    binValLE (mulMod p u v) = (binValLE u * binValLE v) % binValLE p ∧
      (mulMod p u v).length = p.length := by
  obtain ⟨acc', h1, h2, h3⟩ := mulStep_iterate_run p u hu hup v.reverse []
    (List.replicate p.length false) (by simp) (by simp [binValLE_replicate_false, binValLE])
  rw [mulMod, ← List.length_reverse,
    mulStepP_iterate u p (List.replicate p.length false, v.reverse), h1, mulPack, pairFst_pair]
  simp only [List.nil_append, List.reverse_reverse] at h3
  exact ⟨h3, h2⟩

theorem mulMod_length_le (p u v : List Bool) : (mulMod p u v).length ≤ p.length := by
  rw [mulMod, mulStepP_iterate u p (List.replicate p.length false, v.reverse), mulPack,
    pairFst_pair]
  have := (mulStep_iterate_length p u (List.replicate p.length false) v.reverse v.length).1
  simpa using this

theorem mulStepP_mem_FP : mulStepP ∈ FP := by
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
  have hu := hfst hww
  have hp := hsnd hww
  have hone : (fun _ : List Bool => ([false] : List Bool)) ∈ FP := constFn_mem_FP [false]
  have hbit : (fun z => bit1 (pairFst (pairSnd z))) ∈ FP := by
    have := Cobham.takeLenFn_mem_FP hone (Cobham.appendFn_mem_FP hrest hone)
    simpa [bit1] using this
  have hdrop : (fun z => (pairFst (pairSnd z)).drop 1) ∈ FP := by
    have := dropLenFn_mem_FP hone hrest
    simpa using this
  have hzero : (fun z => List.replicate (pairFst (pairSnd (pairSnd z))).length false) ∈ FP :=
    zeroBlockFn_mem_FP hu
  exact Cobham.selectHeadFn_mem_FP (lenLeFlagFn_mem_FP hrest hone)
    (Cobham.pairFn_mem_FP
      (addModFn_mem_FP hp (addModFn_mem_FP hp hacc hacc)
        (Cobham.selectHeadFn_mem_FP hbit hu hzero))
      (Cobham.pairFn_mem_FP hdrop (Cobham.pairFn_mem_FP hu hp))) hid

theorem mulModFn_mem_FP {a b c : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP)
    (hc : c ∈ FP) : (fun z => mulMod (a z) (b z) (c z)) ∈ FP := by
  have hrev : (fun z => (c z).reverse) ∈ FP := by
    have := mem_FP_comp hc reverse_mem_FP
    simpa [Function.comp] using this
  have hinit : (fun z => mulPack (List.replicate (a z).length false) (c z).reverse (b z) (a z))
      ∈ FP :=
    Cobham.pairFn_mem_FP (zeroBlockFn_mem_FP ha)
      (Cobham.pairFn_mem_FP hrev (Cobham.pairFn_mem_FP hb ha))
  have hwidth : (fun z => mulPack (a z) (c z) (b z) (a z)) ∈ FP :=
    Cobham.pairFn_mem_FP ha (Cobham.pairFn_mem_FP hc (Cobham.pairFn_mem_FP hb ha))
  have hbound : ∀ z, ∀ n ≤ (c z).length,
      (mulStepP^[n] (mulPack (List.replicate (a z).length false) (c z).reverse (b z) (a z))).length
        ≤ (mulPack (a z) (c z) (b z) (a z)).length := by
    intro z n _
    rw [mulStepP_iterate (b z) (a z) (List.replicate (a z).length false, (c z).reverse)]
    obtain ⟨h1, h2⟩ := mulStep_iterate_length (a z) (b z) (List.replicate (a z).length false)
      (c z).reverse n
    simp only [List.length_replicate, List.length_reverse] at h1 h2
    rw [mulPack, mulPack, pair_length, pair_length, pair_length, pair_length, pair_length,
      pair_length]
    omega
  have h := Cobham.iterate_mem_FP mulStepP_mem_FP hinit hc hwidth hbound
  have h1 := mem_FP_comp h Cobham.fstBlock_mem_FP
  simpa [Function.comp, mulMod] using h1

/-! ## Residues as strings -/

/-- A residue modulo `p`, as a `w`-bit string. -/
def encZMod (w : ℕ) {p : ℕ} (a : ZMod p) : List Bool := bitsOfLenLE w a.val

@[simp] theorem encZMod_length (w : ℕ) {p : ℕ} (a : ZMod p) : (encZMod w a).length = w :=
  bitsOfLenLE_length _ _

theorem binValLE_encZMod (w : ℕ) {p : ℕ} [NeZero p] (hp : p < 2 ^ w) (a : ZMod p) :
    binValLE (encZMod w a) = a.val :=
  binValLE_bitsOfLenLE w a.val (lt_trans (ZMod.val_lt a) hp)

/-- Two strings of the same length with the same value are equal. -/
theorem eq_of_binValLE_eq {x y : List Bool} (hl : x.length = y.length)
    (hv : binValLE x = binValLE y) : x = y := by
  rw [← bitsOfLenLE_binValLE x, ← bitsOfLenLE_binValLE y, hl, hv]

/-- **Modular addition on residues is addition in `ZMod p`.** -/
theorem addMod_encZMod (w : ℕ) {p : ℕ} [NeZero p] (hp : p < 2 ^ w) (a b : ZMod p) :
    addMod (bitsOfLenLE w p) (encZMod w a) (encZMod w b) = encZMod w (a + b) := by
  have hpv : binValLE (bitsOfLenLE w p) = p := binValLE_bitsOfLenLE w p hp
  refine eq_of_binValLE_eq ?_ ?_
  · rw [addMod_length _ _ _ (by simp) (by simp), bitsOfLenLE_length, encZMod_length]
  · rw [binValLE_addMod _ _ _ (by simp) (by simp)
      (by rw [binValLE_encZMod w hp, hpv]; exact ZMod.val_lt a)
      (by rw [binValLE_encZMod w hp, hpv]; exact ZMod.val_lt b),
      binValLE_encZMod w hp, binValLE_encZMod w hp, binValLE_encZMod w hp, hpv, ZMod.val_add]

/-- **Modular multiplication on residues is multiplication in `ZMod p`.** -/
theorem mulMod_encZMod (w : ℕ) {p : ℕ} [NeZero p] (hp : p < 2 ^ w) (a b : ZMod p) :
    mulMod (bitsOfLenLE w p) (encZMod w a) (encZMod w b) = encZMod w (a * b) := by
  have hpv : binValLE (bitsOfLenLE w p) = p := binValLE_bitsOfLenLE w p hp
  obtain ⟨hval, hlen⟩ := binValLE_mulMod (bitsOfLenLE w p) (encZMod w a) (encZMod w b)
    (by simp) (by rw [binValLE_encZMod w hp, hpv]; exact ZMod.val_lt a)
  refine eq_of_binValLE_eq ?_ ?_
  · rw [hlen, bitsOfLenLE_length, encZMod_length]
  · rw [hval, binValLE_encZMod w hp, binValLE_encZMod w hp, binValLE_encZMod w hp, hpv,
      ZMod.val_mul]

end Complexity
