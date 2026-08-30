/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive.Internal.ShenParams
public import Complexitylib.Classes.PCP.Internal.StripTrailing

/-!
# Well-formedness of an instance

⚠️ Unreviewed by Bolton

The concrete verifier works on instances `(qs, φ)` whose quantifier prefix binds the variables
`0, 1, …, n - 1` in that order and whose matrix mentions only those variables. `wfFlag` checks
both conditions in polynomial time, comparing variables in binary: the prefix's `i`-th variable
against the digits of `i`, and each literal's variable against the digits of `n`.

## Main definitions

- `WellFormed` — the two conditions
- `wfFlag` — the check

## Main results

- `wfFlag_eq_true_iff` — the check is the conditions
- `wfFlag_mem_FP`
-/

@[expose] public section

namespace Complexity

open Cobham Shen

/-- An instance is well formed when its prefix binds `0, …, n - 1` in order and its matrix only
mentions those variables. -/
def WellFormed (I : Instance) : Prop :=
  (∀ i (hi : i < I.1.length), (I.1[i]'hi).2 = i) ∧ ∀ c ∈ I.2, ∀ l ∈ c, l.2 < I.1.length

/-! ## Binary comparison helpers -/

theorem binValLE_append_replicate_false (x : List Bool) (k : ℕ) :
    binValLE (x ++ List.replicate k false) = binValLE x := by
  induction x with
  | nil => simp [binValLE_replicate_false, binValLE]
  | cons b t ih => rw [List.cons_append, binValLE_cons, binValLE_cons, ih]

theorem binValLE_padTo (r x : List Bool) (h : x.length ≤ r.length) :
    binValLE (padTo r x) = binValLE x := by
  rw [padTo_eq_append r x h, binValLE_append_replicate_false]

/-- The digits of the length of a unary string, on `pair anything (unary i)`. -/
noncomputable def digitsOfU (z : List Bool) : List Bool :=
  stripFn (pair [] (coinStr (pairSnd z ++ [true]).length (pairSnd z).length))

theorem digitsOfU_mem_FP : digitsOfU ∈ FP := by
  have hc : (fun z : List Bool => coinStr (pairSnd z ++ [true]).length (pairSnd z).length) ∈ FP :=
    coinStr_mem_FP (t := fun z => (pairSnd z ++ [true]).length) (c := fun z => (pairSnd z).length)
      (by
        have := marks_mem_FP (Cobham.appendFn_mem_FP Cobham.sndBlock_mem_FP (constFn_mem_FP [true]))
        exact mem_FP_of_eq this fun z => by rw [marks_eq])
      (by
        have := marks_mem_FP Cobham.sndBlock_mem_FP
        exact mem_FP_of_eq this fun z => by rw [marks_eq])
  have h := mem_FP_comp (Cobham.pairFn_mem_FP (constFn_mem_FP []) hc) stripFn_mem_FP
  simpa only [Function.comp_def] using h

theorem digitsOfU_pair (s : List Bool) (i : ℕ) :
    digitsOfU (pair s (List.replicate i true)) = Nat.bits i := by
  simp only [digitsOfU, pairSnd_pair, List.length_append, List.length_replicate]
  rw [stripFn_eq, pairSnd_pair, coinStr_eq (by
      simp only [List.length_singleton]
      exact lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))),
    stripTrailing_eq_bits, binValLE_bitsOfLenLE _ _ (by
      simp only [List.length_singleton]
      exact lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-- The variable of the `i`-th quantifier of an encoded prefix, in binary, on
`pair qsE (unary i)`: `qVarP`. -/
theorem qVarP_eq_bits (qs : Prefix) {i : ℕ} (hi : i < qs.length) :
    qVarP (pair (DataEncode.bitstringEncode qs) (List.replicate i true)) = Nat.bits (qs[i]'hi).2 :=
  qVarP_pair qs hi

/-! ## The prefix check -/

/-- A mark when the `i`-th quantifier's variable is not `i`, on `pair qsE (unary i)`. -/
noncomputable def prefixMark (z : List Bool) : List Bool :=
  selectHead (eqFlag (qVarP z) (digitsOfU z)) [] [true]

theorem prefixMark_mem_FP : prefixMark ∈ FP :=
  Cobham.selectHeadFn_mem_FP (eqFlagFn_mem_FP qVarP_mem_FP digitsOfU_mem_FP) (constFn_mem_FP _)
    (constFn_mem_FP _)

theorem prefixMark_length (qs : Prefix) {i : ℕ} (hi : i < qs.length) :
    (prefixMark (pair (DataEncode.bitstringEncode qs) (List.replicate i true))).length
      = if (qs[i]'hi).2 = i then 0 else 1 := by
  rw [prefixMark, qVarP_eq_bits qs hi, digitsOfU_pair]
  by_cases h : (qs[i]'hi).2 = i
  · rw [if_pos h, h, (eqFlag_eq_true_iff _ _).mpr rfl, selectHead_cons_true]
    rfl
  · rw [if_neg h]
    rcases eqFlag_flag (Nat.bits (qs[i]'hi).2) (Nat.bits i) with hf | hf
    · exfalso
      apply h
      have := (eqFlag_eq_true_iff _ _).mp hf
      have := congrArg binValLE this
      rwa [binValLE_bits, binValLE_bits] at this
    · rw [hf, selectHead_cons_false]
      rfl

/-- The number of prefix violations, in unary. -/
noncomputable def prefixBad (x : List Bool) : List Bool :=
  countOver prefixMark (pair (mU x) (qsE x))

theorem prefixBad_mem_FP : prefixBad ∈ FP := by
  unfold prefixBad
  have h := mem_FP_comp (Cobham.pairFn_mem_FP mU_mem_FP qsE_mem_FP)
    (countOver_mem_FP prefixMark_mem_FP)
  simpa only [Function.comp_def] using h

theorem prefixBad_eq_nil_iff (I : Instance) :
    prefixBad (DataEncode.bitstringEncode I) = []
      ↔ ∀ i (hi : i < I.1.length), (I.1[i]'hi).2 = i := by
  rw [prefixBad, mU_eq, qsE_eq, ← List.length_eq_zero_iff, length_countOver,
    Finset.sum_eq_zero_iff]
  constructor
  · intro h i hi
    have := h i (Finset.mem_range.mpr hi)
    rw [prefixMark_length I.1 hi] at this
    split_ifs at this with hh
    exact hh
  · intro h i hi
    rw [Finset.mem_range] at hi
    rw [prefixMark_length I.1 hi, if_pos (h i hi)]

/-! ## The matrix check -/

/-- A mark when the literal's variable is not below the number of quantifiers, on
`pair (pair (pair mBits φE) (unary i)) (unary j)`. -/
noncomputable def litMark (z : List Bool) : List Bool :=
  let mb := pairFst (pairFst (pairFst z))
  let e := pairSnd (pairFst (pairFst z))
  let vb := decOne (sndEnc (posAt (posAt e (pairSnd (pairFst z)).length) (pairSnd z).length))
  selectHead (ltFlag (padTo (vb ++ mb) vb) (padTo (vb ++ mb) mb)) [] [true]

theorem litMark_mem_FP : litMark ∈ FP := by
  have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hX := comp_fst hid
  have hXX := comp_fst hX
  have hmb := comp_fst hXX
  have he := comp_snd hXX
  have hi := comp_snd hX
  have hj := comp_snd hid
  have hclause : (fun z => posAt (pairSnd (pairFst (pairFst z)))
      (pairSnd (pairFst z)).length) ∈ FP :=
    posAt_mem_FP hi he
  have hlit : (fun z => posAt (posAt (pairSnd (pairFst (pairFst z))) (pairSnd (pairFst z)).length)
      (pairSnd z).length) ∈ FP := posAt_mem_FP hj hclause
  have hvb : (fun z => decOne (sndEnc (posAt (posAt (pairSnd (pairFst (pairFst z)))
      (pairSnd (pairFst z)).length) (pairSnd z).length))) ∈ FP := by
    have h := mem_FP_comp (sndEnc_mem_FP hlit) decOne_mem_FP
    simpa only [Function.comp_def] using h
  have hW := Cobham.appendFn_mem_FP hvb hmb
  exact Cobham.selectHeadFn_mem_FP (ltFlagFn_mem_FP (padToFn_mem_FP hW hvb) (padToFn_mem_FP hW hmb))
    (constFn_mem_FP _) (constFn_mem_FP _)

theorem litMark_length (m : ℕ) (φ : List (List CLit)) {i : ℕ} (hi : i < φ.length) {j : ℕ}
    (hj : j < (φ[i]'hi).length) :
    (litMark (pair (pair (pair (Nat.bits m) (DataEncode.bitstringEncode φ))
        (List.replicate i true)) (List.replicate j true))).length
      = if ((φ[i]'hi)[j]'hj).2 < m then 0 else 1 := by
  simp only [litMark, pairFst_pair, pairSnd_pair, List.length_replicate]
  rw [posAt_eq_of_lt hi, posAt_eq_of_lt hj]
  rcases hl : (φ[i]'hi)[j]'hj with ⟨b, n⟩
  rw [sndEnc_eq]
  have hn : decOne (DataEncode.bitstringEncode n) = Nat.bits n := decOne_encode (Nat.bits n)
  rw [hn]
  simp only
  have hlt := ltFlag_eq_true_iff (padTo (Nat.bits n ++ Nat.bits m) (Nat.bits n))
    (padTo (Nat.bits n ++ Nat.bits m) (Nat.bits m)) (by simp)
  rw [binValLE_padTo _ _ (by simp), binValLE_padTo _ _ (by simp), binValLE_bits, binValLE_bits]
    at hlt
  by_cases h : n < m
  · rw [if_pos h, hlt.mpr h, selectHead_cons_true]
    rfl
  · rw [if_neg h]
    rcases ltFlag_flag (padTo (Nat.bits n ++ Nat.bits m) (Nat.bits n))
      (padTo (Nat.bits n ++ Nat.bits m) (Nat.bits m)) (by simp) with hf | hf
    · exact absurd (hlt.mp hf) h
    · rw [hf, selectHead_cons_false]
      rfl

/-- The violations in clause `i`, on `pair (pair mBits φE) (unary i)`. -/
noncomputable def clauseBad (z : List Bool) : List Bool :=
  countOver litMark (pair (posCount (posAt (pairSnd (pairFst z)) (pairSnd z).length)) z)

theorem clauseBad_mem_FP : clauseBad ∈ FP := by
  have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have he := comp_snd (comp_fst hid)
  have hi := comp_snd hid
  unfold clauseBad
  have h := mem_FP_comp (Cobham.pairFn_mem_FP (posCount_mem_FP (posAt_mem_FP hi he)) hid)
    (countOver_mem_FP litMark_mem_FP)
  simpa only [Function.comp_def] using h

theorem clauseBad_length (m : ℕ) (φ : List (List CLit)) {i : ℕ} (hi : i < φ.length) :
    (clauseBad (pair (pair (Nat.bits m) (DataEncode.bitstringEncode φ))
        (List.replicate i true))).length
      = ∑ j ∈ Finset.range (φ[i]'hi).length,
          if ((φ[i]'hi)[j]?.getD (true, 0)).2 < m then 0 else 1 := by
  simp only [clauseBad, pairFst_pair, pairSnd_pair, List.length_replicate]
  rw [posAt_eq_of_lt hi, posCount_eq, length_countOver]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [litMark_length m φ hi hj, List.getElem?_eq_getElem hj]
  rfl

/-- The number of matrix violations, in unary. -/
noncomputable def matrixBad (x : List Bool) : List Bool :=
  countOver clauseBad (pair (posCount (φE x)) (pair (digitsOfU (pair [] (mU x))) (φE x)))

theorem matrixBad_mem_FP : matrixBad ∈ FP := by
  unfold matrixBad
  have hd : (fun x => digitsOfU (pair [] (mU x))) ∈ FP := by
    have h := mem_FP_comp (Cobham.pairFn_mem_FP (constFn_mem_FP []) mU_mem_FP) digitsOfU_mem_FP
    simpa only [Function.comp_def] using h
  have h := mem_FP_comp (Cobham.pairFn_mem_FP (posCount_mem_FP φE_mem_FP)
    (Cobham.pairFn_mem_FP hd φE_mem_FP)) (countOver_mem_FP clauseBad_mem_FP)
  simpa only [Function.comp_def] using h

theorem matrixBad_eq_nil_iff (I : Instance) :
    matrixBad (DataEncode.bitstringEncode I) = []
      ↔ ∀ c ∈ I.2, ∀ l ∈ c, l.2 < I.1.length := by
  rw [matrixBad, φE_eq, mU_eq, digitsOfU_pair, posCount_eq, ← List.length_eq_zero_iff,
    length_countOver, Finset.sum_eq_zero_iff]
  have hterm : ∀ i ∈ Finset.range I.2.length,
      ((clauseBad (pair (pair (Nat.bits I.1.length) (DataEncode.bitstringEncode I.2))
        (List.replicate i true))).length = 0
        ↔ ∀ l ∈ (I.2[i]?.getD []), l.2 < I.1.length) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [clauseBad_length I.1.length I.2 hi, Finset.sum_eq_zero_iff, List.getElem?_eq_getElem hi]
    simp only [Option.getD_some]
    constructor
    · intro h l hl
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
      have := h j (Finset.mem_range.mpr hj)
      rw [List.getElem?_eq_getElem hj] at this
      simp only [Option.getD_some] at this
      split_ifs at this with hh
      exact hh
    · intro h j hj
      rw [Finset.mem_range] at hj
      rw [List.getElem?_eq_getElem hj]
      simp only [Option.getD_some]
      rw [if_pos (h _ (List.getElem_mem hj))]
  constructor
  · intro h c hc l hl
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    have := (hterm i (Finset.mem_range.mpr hi)).mp (h i (Finset.mem_range.mpr hi))
    rw [List.getElem?_eq_getElem hi] at this
    exact this l hl
  · intro h i hi
    rw [hterm i hi]
    intro l hl
    rw [Finset.mem_range] at hi
    rw [List.getElem?_eq_getElem hi] at hl
    exact h _ (List.getElem_mem hi) l hl

/-! ## The check -/

/-- **The well-formedness check.** -/
noncomputable def wfFlag (x : List Bool) : List Bool :=
  andBit (emptyFlag (prefixBad x)) (emptyFlag (matrixBad x))

theorem wfFlag_mem_FP : wfFlag ∈ FP :=
  andBitFn_mem_FP (emptyFlagFn_mem_FP prefixBad_mem_FP) (emptyFlagFn_mem_FP matrixBad_mem_FP)

theorem wfFlag_flag (x : List Bool) : wfFlag x = [true] ∨ wfFlag x = [false] :=
  andBit_flag _ _

/-- **The check is well-formedness.** -/
theorem wfFlag_eq_true_iff (I : Instance) :
    wfFlag (DataEncode.bitstringEncode I) = [true] ↔ WellFormed I := by
  rw [wfFlag, andBit_eq_true_iff (emptyFlag_flag _) (emptyFlag_flag _), emptyFlag_eq_true_iff,
    emptyFlag_eq_true_iff, prefixBad_eq_nil_iff, matrixBad_eq_nil_iff, WellFormed]

end Complexity
