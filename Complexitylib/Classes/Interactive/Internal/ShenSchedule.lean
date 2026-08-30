/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive.TQBFProtocol
public import Complexitylib.Classes.Interactive.Internal.CNFArith
public import Complexitylib.Classes.PCP.Internal.Materialize
public import Mathlib.Data.List.GetD

/-!
# The schedule of Shen's chain, as data

⚠️ Unreviewed by Bolton

A concrete verifier for Shen's protocol has to know, in each round, which operator it is
stripping: a product or an "or" on the quantified variable, or a linearization of a variable
bound so far. This file represents the chain `Shen.shenChain` as a list of *codes* — a kind
(`[]` for product, `[true]` for "or", `[true, true]` for linearization) and the variable's binary
digits — and shows

- `decodeOp_shenCodes`: decoding the codes gives back the chain;
- `chainDeg_uniform`: a single uniform degree bound, `max 2 (number of literals)`, is valid in
  every round, so the verifier need not carry a per-round degree list;
- `shenCodesEnc_eq`, `shenCodesEnc_mem_FP`: the encoding of the code list is computed from the
  encoding of the prefix in polynomial time.

## Main definitions

- `OpCode`, `decodeOp`, `shenCodes` — the codes
- `litCount` — the number of literals of a CNF
- `shenCodesEnc` — the schedule from the encoded prefix

## Main results

- `decodeOp_shenCodes`, `chainDeg_uniform`, `shenCodesEnc_eq`, `shenCodesEnc_mem_FP`
-/

@[expose] public section

namespace Complexity

open OpChain Shen Cobham

/-! ## Codes -/

/-- An operator code: its kind and its variable's binary digits. -/
abbrev OpCode := List Bool × List Bool

/-- Decode a code. -/
def decodeOp (c : OpCode) : Op :=
  match c.1 with
  | [] => .prod (binValLE c.2)
  | [_] => .or (binValLE c.2)
  | _ => .lin (binValLE c.2)

/-- The code of a quantifier on variable `i`. -/
def quantCode (q : Bool) (i : ℕ) : OpCode := (if q then [] else [true], Nat.bits i)

/-- The code of a linearization of variable `i`. -/
def linCode (i : ℕ) : OpCode := ([true, true], Nat.bits i)

/-- The codes of one level of the chain. -/
def levelCodes (vs : List ℕ) (q : Bool) (i : ℕ) : List OpCode :=
  quantCode q i :: (vs ++ [i]).map linCode

/-- The codes of Shen's chain. -/
def shenCodes : Prefix → List ℕ → List OpCode
  | [], _ => []
  | (q, i) :: qs, vs => levelCodes vs q i ++ shenCodes qs (vs ++ [i])

theorem decodeOp_quantCode (q : Bool) (i : ℕ) : decodeOp (quantCode q i) = quantOp q i := by
  cases q <;> simp [decodeOp, quantCode, quantOp, binValLE_bits]

theorem decodeOp_linCode (i : ℕ) : decodeOp (linCode i) = Op.lin i := by
  simp [decodeOp, linCode, binValLE_bits]

/-- **Decoding the codes gives the chain.** -/
theorem decodeOp_shenCodes : ∀ (qs : Prefix) (vs : List ℕ),
    (shenCodes qs vs).map decodeOp = shenChain qs vs
  | [], _ => rfl
  | (q, i) :: qs, vs => by
      rw [shenCodes, shenChain, List.map_append, decodeOp_shenCodes qs, levelCodes, List.map_cons,
        decodeOp_quantCode, List.map_map, linOps, List.cons_append]
      congr 2
      exact List.map_congr_left fun j _ => decodeOp_linCode j

theorem shenCodes_length : ∀ (qs : Prefix) (vs : List ℕ),
    (shenCodes qs vs).length = (shenChain qs vs).length := by
  intro qs vs
  rw [← decodeOp_shenCodes, List.length_map]

/-! ## A uniform degree bound -/

theorem tail_drop' {α : Type} (l : List α) (k : ℕ) : l.tail.drop k = l.drop (k + 1) := by
  cases l <;> simp

/-- Raising every degree bound keeps the chain valid. -/
theorem chainDeg_mono {F : Type} [Field F] :
    ∀ (ops : List Op) (ds ds' : List ℕ) (f : (ℕ → F) → F), ChainDeg ops ds f →
      (∀ k, k < ops.length → (ds.drop k).headD 0 ≤ (ds'.drop k).headD 0) →
      ChainDeg ops ds' f
  | [], _, _, _, _, _ => trivial
  | o :: os, ds, ds', f, h, hle => by
      refine ⟨h.1.mono (by simpa using hle 0 (by simp)), ?_⟩
      refine chainDeg_mono os ds.tail ds'.tail f h.2 fun k hk => ?_
      have := hle (k + 1) (by simpa using hk)
      rwa [tail_drop', tail_drop']

/-- The number of literals of a CNF. -/
def litCount (φ : List (List CLit)) : ℕ := (φ.map List.length).sum

theorem varDeg_litQBF (j : ℕ) (l : CLit) : QBF.varDeg j (litQBF l) ≤ 1 := by
  rcases l with ⟨b, n⟩
  cases b <;> simp [litQBF, QBF.varDeg] <;> split_ifs <;> omega

theorem varDeg_clauseQBF (j : ℕ) (c : List CLit) : QBF.varDeg j (clauseQBF c) ≤ c.length := by
  induction c with
  | nil => simp [clauseQBF, QBF.varDeg]
  | cons l c ih =>
      rw [clauseQBF, List.foldr_cons, QBF.varDeg, ← clauseQBF, List.length_cons]
      have := varDeg_litQBF j l
      omega

theorem varDeg_cnfQBF (j : ℕ) (φ : List (List CLit)) :
    QBF.varDeg j (cnfQBF φ) ≤ litCount φ := by
  induction φ with
  | nil => simp [cnfQBF, QBF.varDeg, litCount]
  | cons c φ ih =>
      rw [cnfQBF, List.foldr_cons, QBF.varDeg, ← cnfQBF, litCount, List.map_cons, List.sum_cons]
      have := varDeg_clauseQBF j c
      rw [litCount] at ih
      omega

/-- Every entry of `shenDegs` for a CNF matrix is at most `max 2 (litCount φ)`. -/
theorem shenDegs_le (φ : List (List CLit)) : ∀ (qs : Prefix) (vs : List ℕ),
    ∀ d ∈ shenDegs (cnfQBF φ) qs vs, d ≤ max 2 (litCount φ)
  | [], _, d, hd => by simp [shenDegs] at hd
  | (q, i) :: qs, vs, d, hd => by
      rw [shenDegs, List.mem_cons, List.mem_append, List.mem_map] at hd
      rcases hd with rfl | ⟨j, _, rfl⟩ | hd
      · exact le_max_left _ _
      · rw [linDeg]
        exact max_le_max_left _ (varDeg_cnfQBF j φ)
      · exact shenDegs_le φ qs (vs ++ [i]) d hd

theorem shenDegs_length (ψ : QBF) : ∀ (qs : Prefix) (vs : List ℕ),
    (shenDegs ψ qs vs).length = (shenChain qs vs).length
  | [], _ => rfl
  | (q, i) :: qs, vs => by
      rw [shenDegs, shenChain, List.length_cons, List.length_cons, List.length_append,
        List.length_append, List.length_map, linOps, List.length_map, shenDegs_length ψ qs]

/-- **A uniform degree bound is valid** for Shen's chain over a CNF matrix. -/
theorem chainDeg_uniform {F : Type} [Field F] (φ : List (List CLit)) (qs : Prefix)
    (hnd : (qs.map Prod.snd).Nodup) :
    ChainDeg (shenChain qs []) (List.replicate (shenChain qs []).length (max 2 (litCount φ)))
      (QBF.arith (cnfQBF φ) : (ℕ → F) → F) := by
  refine chainDeg_mono _ _ _ _ (chainDeg_shenChain (cnfQBF φ) qs [] (by simpa using hnd))
    fun k hk => ?_
  obtain ⟨m, hm⟩ : ∃ m, (shenChain qs []).length - k = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  rw [List.drop_replicate, hm, List.replicate_succ, List.headD_cons]
  have hlen := shenDegs_length (cnfQBF φ) qs []
  rcases hd : (shenDegs (cnfQBF φ) qs []).drop k with _ | ⟨d, rest⟩
  · exact absurd hd (by
      intro h
      have := congrArg List.length h
      rw [List.length_drop, hlen] at this
      simp at this
      omega)
  · rw [List.headD_cons]
    exact shenDegs_le φ qs [] d (by
      have : d ∈ (shenDegs (cnfQBF φ) qs []).drop k := by rw [hd]; exact List.mem_cons_self
      exact List.mem_of_mem_drop this)

/-! ## The schedule from the encoded prefix -/

/-- The levels of the chain, indexed: level `i` linearizes the variables of the first `i + 1`
quantifiers. -/
theorem shenCodes_eq_flatMap : ∀ (qs : Prefix) (vs : List ℕ),
    shenCodes qs vs = (List.range qs.length).flatMap fun i =>
      levelCodes (vs ++ (qs.take i).map Prod.snd) (qs.getD i (true, 0)).1 (qs.getD i (true, 0)).2
  | [], _ => by simp [shenCodes]
  | (q, i) :: qs, vs => by
      rw [shenCodes, shenCodes_eq_flatMap qs (vs ++ [i]), List.length_cons, List.range_succ_eq_map,
        List.flatMap_cons, List.flatMap_map]
      simp only [List.take_zero, List.map_nil, List.append_nil, List.getD_cons_zero]
      congr 1
      refine List.flatMap_congr fun j _ => ?_
      rw [List.take_succ_cons, List.map_cons, List.getD_cons_succ, List.append_assoc,
        List.singleton_append]

/-- The `i`-th quantifier's kind code, on `pair e (unary i)`. -/
noncomputable def qKindP (z : List Bool) : List Bool :=
  selectHead (eqFlag (fstEnc (posAt (pairFst z) (pairSnd z).length)) [false, false, true, true])
    [] [true]

theorem qKindP_mem_FP : qKindP ∈ FP :=
  Cobham.selectHeadFn_mem_FP (eqFlagFn_mem_FP
    (fstEnc_mem_FP (posAt_mem_FP Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP))
    (constFn_mem_FP _)) (constFn_mem_FP _) (constFn_mem_FP _)

theorem qKindP_pair (qs : Prefix) {i : ℕ} (hi : i < qs.length) :
    qKindP (pair (DataEncode.bitstringEncode qs) (List.replicate i true))
      = (quantCode (qs[i]'hi).1 (qs[i]'hi).2).1 := by
  simp only [qKindP, pairFst_pair, pairSnd_pair, List.length_replicate]
  rw [posAt_eq_of_lt hi, fstEnc_eq]
  rcases hl : qs[i]'hi with ⟨q, n⟩
  cases q
  · rw [bitstringEncode_false]
    rcases eqFlag_flag [false, true] [false, false, true, true] with h | h
    · exact absurd ((eqFlag_eq_true_iff _ _).mp h) (by decide)
    · rw [h, selectHead_cons_false]
      rfl
  · rw [bitstringEncode_true, (eqFlag_eq_true_iff _ _).mpr rfl, selectHead_cons_true]
    rfl

/-- The `i`-th quantifier's variable, in binary, on `pair e (unary i)`. -/
noncomputable def qVarP : List Bool → List Bool :=
  decOne ∘ fun z => sndEnc (posAt (pairFst z) (pairSnd z).length)

theorem qVarP_mem_FP : qVarP ∈ FP :=
  mem_FP_comp (sndEnc_mem_FP (posAt_mem_FP Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP))
    decOne_mem_FP

theorem qKindP_comp {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun s => qKindP (a s)) ∈ FP := by
  have h := mem_FP_comp ha qKindP_mem_FP
  simpa only [Function.comp_def] using h

theorem qVarP_comp {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun s => qVarP (a s)) ∈ FP := by
  have h := mem_FP_comp ha qVarP_mem_FP
  simpa only [Function.comp_def] using h

theorem qVarP_pair (qs : Prefix) {i : ℕ} (hi : i < qs.length) :
    qVarP (pair (DataEncode.bitstringEncode qs) (List.replicate i true))
      = Nat.bits (qs[i]'hi).2 := by
  simp only [qVarP, Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate]
  rw [posAt_eq_of_lt hi]
  rcases hl : qs[i]'hi with ⟨q, n⟩
  rw [sndEnc_eq]
  exact decOne_encode (Nat.bits n)

/-- The `j`-th code of level `i`, on `pair (pair e (unary i)) (unary j)`: the quantifier's code
for `j = 0`, the linearization of the `(j - 1)`-th variable otherwise. -/
noncomputable def levelEntry (s : List Bool) : List Bool :=
  selectHead (emptyFlag (pairSnd s))
    (encPair (qKindP (pairFst s)) (qVarP (pairFst s)))
    (encPair [true, true] (qVarP (pair (pairFst (pairFst s)) (dropOne (pairSnd s)))))

theorem levelEntry_mem_FP : levelEntry ∈ FP := by
  have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hX : (fun s : List Bool => pairFst s) ∈ FP := Cobham.fstBlock_mem_FP
  have hj : (fun s : List Bool => pairSnd s) ∈ FP := Cobham.sndBlock_mem_FP
  have he : (fun s : List Bool => pairFst (pairFst s)) ∈ FP := comp_fst hX
  have hkind : (fun s => qKindP (pairFst s)) ∈ FP := qKindP_comp hX
  have hvar : (fun s => qVarP (pairFst s)) ∈ FP := qVarP_comp hX
  have hvar' : (fun s => qVarP (pair (pairFst (pairFst s)) (dropOne (pairSnd s)))) ∈ FP :=
    qVarP_comp (Cobham.pairFn_mem_FP he (dropOneFn_mem_FP hj))
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hj) (encPair_mem_FP hkind hvar)
    (encPair_mem_FP (constFn_mem_FP _) hvar')

theorem levelEntry_zero (qs : Prefix) {i : ℕ} (hi : i < qs.length) :
    levelEntry (pair (pair (DataEncode.bitstringEncode qs) (List.replicate i true))
        (List.replicate 0 true))
      = DataEncode.bitstringEncode (quantCode (qs[i]'hi).1 (qs[i]'hi).2) := by
  simp only [levelEntry, pairSnd_pair, pairFst_pair]
  rw [List.replicate_zero, emptyFlag_nil, selectHead_cons_true, qKindP_pair qs hi,
    qVarP_pair qs hi, encPair_eq]
  rfl

theorem levelEntry_succ (qs : Prefix) {i : ℕ} (hi : i < qs.length) (j : ℕ) (hj : j ≤ i) :
    levelEntry (pair (pair (DataEncode.bitstringEncode qs) (List.replicate i true))
        (List.replicate (j + 1) true))
      = DataEncode.bitstringEncode (linCode (qs[j]'(by omega)).2) := by
  simp only [levelEntry, pairSnd_pair, pairFst_pair]
  rw [List.replicate_succ, emptyFlag_cons, selectHead_cons_false, dropOne, List.drop_succ_cons,
    List.drop_zero, qVarP_pair qs (by omega), encPair_eq]
  rfl

theorem take_map_snd_getElem (qs : Prefix) {i : ℕ} (hi : i < qs.length) (j : ℕ) (hj : j ≤ i) :
    ((qs.take i).map Prod.snd ++ [(qs[i]'hi).2])[j]'(by simp; omega) = (qs[j]'(by omega)).2 := by
  rw [List.getElem_append]
  split
  · rw [List.getElem_map, List.getElem_take]
  · have : j = i := by
      simp only [List.length_map, List.length_take] at *
      omega
    subst this
    simp

/-- The encoding of level `i`'s codes, on `pair e (unary i)`. -/
noncomputable def levelEncP (z : List Bool) : List Bool :=
  listEncFn levelEntry (pair (pairSnd z ++ [true, true]) (pair (pairFst z) (pairSnd z)))

theorem levelEncP_mem_FP : levelEncP ∈ FP := by
  have hX : (fun s : List Bool => pairFst s) ∈ FP := Cobham.fstBlock_mem_FP
  have hj : (fun s : List Bool => pairSnd s) ∈ FP := Cobham.sndBlock_mem_FP
  have harg : (fun z => pair (pairSnd z ++ [true, true]) (pair (pairFst z) (pairSnd z))) ∈ FP :=
    Cobham.pairFn_mem_FP (Cobham.appendFn_mem_FP hj (constFn_mem_FP _))
      (Cobham.pairFn_mem_FP hX hj)
  exact mem_FP_comp (g := listEncFn levelEntry) harg (materialize_mem_FP levelEntry_mem_FP)

theorem levelEncP_pair (qs : Prefix) {i : ℕ} (hi : i < qs.length) :
    levelEncP (pair (DataEncode.bitstringEncode qs) (List.replicate i true))
      = DataEncode.bitstringEncode
          (levelCodes ((qs.take i).map Prod.snd) (qs[i]'hi).1 (qs[i]'hi).2) := by
  simp only [levelEncP, pairFst_pair, pairSnd_pair]
  have hlen : (levelCodes ((qs.take i).map Prod.snd) (qs[i]'hi).1 (qs[i]'hi).2).length
      = i + 2 := by
    simp [levelCodes]
    omega
  rw [show List.replicate i true ++ [true, true] = List.replicate (i + 2) true by
    rw [List.replicate_add]; rfl, ← hlen]
  refine materialize_eq _ _ fun j hj => ?_
  cases j with
  | zero =>
      simp only [levelCodes, List.getElem_cons_zero]
      exact levelEntry_zero qs hi
  | succ j =>
      simp only [levelCodes, List.getElem_cons_succ, List.getElem_map]
      rw [take_map_snd_getElem qs hi j (by rw [hlen] at hj; omega)]
      exact levelEntry_succ qs hi j (by rw [hlen] at hj; omega)

/-- The inner part of level `i`'s encoding, on `pair e (unary i)`. -/
noncomputable def levelInner (z : List Bool) : List Bool := posInner (levelEncP z)

theorem levelInner_mem_FP : levelInner ∈ FP := posInner_mem_FP levelEncP_mem_FP

/-- **The schedule, from the encoded prefix.** -/
noncomputable def shenCodesEnc (e : List Bool) : List Bool :=
  listEncFn levelInner (pair (posCount e) e)

theorem shenCodesEnc_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun w => shenCodesEnc (a w)) ∈ FP := by
  have h : (fun w => listEncFn levelInner (pair (posCount (a w)) (a w))) ∈ FP :=
    mem_FP_comp (g := listEncFn levelInner) (Cobham.pairFn_mem_FP (posCount_mem_FP ha) ha)
      (materialize_mem_FP levelInner_mem_FP)
  exact h

theorem posInner_bitstringEncode_append {α : Type} [DataEncode α] (l₁ l₂ : List α) :
    posInner (DataEncode.bitstringEncode (l₁ ++ l₂))
      = posInner (DataEncode.bitstringEncode l₁)
        ++ posInner (DataEncode.bitstringEncode l₂) := by
  rw [posInner_bitstringEncode, posInner_bitstringEncode, posInner_bitstringEncode, List.map_append,
    List.map_append, List.flatten_append]

theorem bitstringEncode_eq_posInner {α : Type} [DataEncode α] (l : List α) :
    DataEncode.bitstringEncode l = false :: posInner (DataEncode.bitstringEncode l) ++ [true] := by
  rw [posInner_bitstringEncode, DataEncode.bitstringEncode_def,
    show DataEncode.encode l = Data.l (l.map DataEncode.encode) from rfl, Data.toBits_l]
  rfl

theorem entryCat_levelInner (qs : Prefix) : ∀ n, n ≤ qs.length →
    entryCat levelInner (DataEncode.bitstringEncode qs) n
      = posInner (DataEncode.bitstringEncode ((List.range n).flatMap fun i =>
          levelCodes ((qs.take i).map Prod.snd) (qs.getD i (true, 0)).1 (qs.getD i (true, 0)).2))
  | 0, _ => by simp [entryCat, posInner_bitstringEncode]
  | n + 1, hn => by
      rw [entryCat_succ, entryCat_levelInner qs n (by omega), List.range_succ, List.flatMap_append,
        List.flatMap_singleton, posInner_bitstringEncode_append, levelInner,
        levelEncP_pair qs (by omega : n < qs.length), List.getD_eq_getElem qs _ (by omega)]

/-- **The schedule computed from the encoded prefix is the encoding of the codes.** -/
theorem shenCodesEnc_eq (qs : Prefix) :
    shenCodesEnc (DataEncode.bitstringEncode qs)
      = DataEncode.bitstringEncode (shenCodes qs []) := by
  rw [shenCodesEnc, posCount_eq, listEncFn_eq, pairFst_pair, pairSnd_pair, List.length_replicate,
    entryCat_levelInner qs qs.length le_rfl, shenCodes_eq_flatMap qs [],
    ← bitstringEncode_eq_posInner]
  simp only [List.nil_append]

end Complexity
