/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive.Internal.FoldLoop
public import Complexitylib.Classes.Interactive.Internal.ModArith
public import Complexitylib.Classes.Interactive.Containments
public import Complexitylib.Classes.PCP.Internal.UnaryList
public import Complexitylib.Classes.PCP.Internal.BinToUnary
public import Complexitylib.Classes.PCP.Internal.VerifierLang
public import Complexitylib.SAT.QBF.Arith

/-!
# Evaluating an arithmetized CNF in polynomial time

⚠️ Unreviewed by Bolton

The last step of Shamir's verifier evaluates the arithmetized matrix of the formula at the random
point the protocol has moved to. With the matrix a CNF, this is a product over clauses of
`1 - Π (1 - literal)`, and `cnfEval` computes it in the polynomial-time algebra: the point is a
string of `w`-bit blocks, one per variable, the CNF is its `DataEncode` serialization, and the
two products are `foldLoop`s over the entries read by `posAt`.

`cnfEval_encZMod` identifies the result with `QBF.arith` of the CNF viewed as a formula
(`cnfQBF`), at the assignment the blocks encode.

## Main definitions

- `cnfQBF` — a CNF as a `QBF`
- `litVal`, `clauseEval`, `cnfEval` — the evaluator

## Main results

- `arith_cnfQBF` — the arithmetization of a CNF is the product formula
- `cnfEval_encZMod` — the evaluator computes it
- `cnfEvalFn_mem_FP` — in polynomial time
-/

@[expose] public section

namespace Complexity

open Cobham

/-! ## A CNF as a formula -/

/-- A literal, `true` for positive. -/
abbrev CLit := Bool × ℕ

/-- A literal as a formula. -/
def litQBF (l : CLit) : QBF := if l.1 then .var l.2 else .neg (.var l.2)

/-- A clause as a formula: the disjunction of its literals, ending in `⊥`. -/
def clauseQBF (c : List CLit) : QBF := c.foldr (fun l acc => .disj (litQBF l) acc) .fls

/-- A CNF as a formula: the conjunction of its clauses, ending in `⊤`. -/
def cnfQBF (φ : List (List CLit)) : QBF := φ.foldr (fun c acc => .conj (clauseQBF c) acc) .tru

section Formula

variable {R : Type} [CommRing R]

theorem arith_litQBF (l : CLit) (a : ℕ → R) :
    QBF.arith (litQBF l) a = if l.1 then a l.2 else 1 - a l.2 := by
  rcases l with ⟨b, n⟩
  cases b <;> simp [litQBF, QBF.arith]

/-- The arithmetization of a clause is `1 - Π (1 - literal)`. -/
theorem arith_clauseQBF (c : List CLit) (a : ℕ → R) :
    QBF.arith (clauseQBF c) a = 1 - (c.map fun l => 1 - QBF.arith (litQBF l) a).prod := by
  induction c with
  | nil => simp [clauseQBF, QBF.arith]
  | cons l c ih =>
      rw [clauseQBF, List.foldr_cons, QBF.arith, ← clauseQBF, ih, List.map_cons, List.prod_cons]
      ring

/-- **The arithmetization of a CNF is the product of its clauses.** -/
theorem arith_cnfQBF (φ : List (List CLit)) (a : ℕ → R) :
    QBF.arith (cnfQBF φ) a = (φ.map fun c => QBF.arith (clauseQBF c) a).prod := by
  induction φ with
  | nil => simp [cnfQBF, QBF.arith]
  | cons c φ ih =>
      rw [cnfQBF, List.foldr_cons, QBF.arith, ← cnfQBF, ih, List.map_cons, List.prod_cons]

end Formula

/-! ## Field constants -/

/-- The residue `1`, at the width of the modulus. -/
def oneStr (q : List Bool) : List Bool := [true] ++ List.replicate (dropOne q).length false

theorem oneStr_length (q : List Bool) (hq : 0 < q.length) : (oneStr q).length = q.length := by
  rw [oneStr, List.length_append, List.length_replicate, dropOne, List.length_drop]
  simp only [List.length_singleton]
  omega

theorem binValLE_oneStr (q : List Bool) : binValLE (oneStr q) = 1 := by
  rw [oneStr, List.singleton_append, binValLE_cons, binValLE_replicate_false]
  rfl

theorem oneStrFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => oneStr (a z)) ∈ FP :=
  Cobham.appendFn_mem_FP (constFn_mem_FP [true]) (zeroBlockFn_mem_FP (dropOneFn_mem_FP ha))

/-- `-v` modulo `q`: `0` for `0`, `q - v` otherwise. -/
noncomputable def negMod (q v : List Bool) : List Bool :=
  selectHead (eqFlag v (List.replicate q.length false)) (List.replicate q.length false)
    (subBits q v)

theorem binValLE_negMod (q v : List Bool) (hv : v.length = q.length)
    (hvq : binValLE v < binValLE q) :
    binValLE (negMod q v) = (binValLE q - binValLE v) % binValLE q ∧
      (negMod q v).length = q.length := by
  rw [negMod]
  rcases eqFlag_flag v (List.replicate q.length false) with h | h
  · rw [h, selectHead_cons_true]
    have hz := (eqFlag_eq_true_iff _ _).mp h
    rw [hz, binValLE_replicate_false]
    simp
  · rw [h, selectHead_cons_false]
    have hne : v ≠ List.replicate q.length false := by
      intro heq
      rw [(eqFlag_eq_true_iff _ _).mpr heq] at h
      exact absurd h (by decide)
    have hpos : 0 < binValLE v := by
      by_contra h0
      apply hne
      have hv0 : binValLE v = 0 := by omega
      rw [← bitsOfLenLE_binValLE v, hv0, hv]
      clear h hne hv0 h0 hvq hv
      induction q.length with
      | zero => rfl
      | succ n ih => simp [bitsOfLenLE, List.replicate_succ, ih]
    rw [binValLE_subBits q v hv, if_pos (by omega), subBits_length q v hv]
    refine ⟨?_, rfl⟩
    rw [Nat.mod_eq_of_lt (by omega)]

theorem negModFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => negMod (a z) (b z)) ∈ FP :=
  Cobham.selectHeadFn_mem_FP (eqFlagFn_mem_FP hb (zeroBlockFn_mem_FP ha)) (zeroBlockFn_mem_FP ha)
    (subBitsFn_mem_FP ha hb)

/-- `1 - v` modulo `q`. -/
noncomputable def oneMinusMod (q v : List Bool) : List Bool := addMod q (oneStr q) (negMod q v)

theorem oneMinusModFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => oneMinusMod (a z) (b z)) ∈ FP :=
  addModFn_mem_FP ha (oneStrFn_mem_FP ha) (negModFn_mem_FP ha hb)

/-- **On residues, `oneMinusMod` is `1 - ·`.** -/
theorem oneMinusMod_encZMod (w : ℕ) {p : ℕ} [NeZero p] (hp : p < 2 ^ w) (hp1 : 1 < p)
    (v : ZMod p) : oneMinusMod (bitsOfLenLE w p) (encZMod w v) = encZMod w (1 - v) := by
  have hpv : binValLE (bitsOfLenLE w p) = p := binValLE_bitsOfLenLE w p hp
  have hw : 0 < w := by
    by_contra h0
    have : w = 0 := by omega
    subst this
    simp at hp
    omega
  have hql : (bitsOfLenLE w p).length = w := bitsOfLenLE_length _ _
  obtain ⟨hnv, hnl⟩ := binValLE_negMod (bitsOfLenLE w p) (encZMod w v) (by simp)
    (by rw [binValLE_encZMod w hp, hpv]; exact ZMod.val_lt v)
  rw [hpv, binValLE_encZMod w hp] at hnv
  have hone : binValLE (oneStr (bitsOfLenLE w p)) = 1 := binValLE_oneStr _
  have honel : (oneStr (bitsOfLenLE w p)).length = (bitsOfLenLE w p).length :=
    oneStr_length _ (by omega)
  refine eq_of_binValLE_eq ?_ ?_
  · rw [oneMinusMod, addMod_length _ _ _ honel hnl, hql, encZMod_length]
  · rw [oneMinusMod, binValLE_addMod _ _ _ honel hnl (by rw [hone, hpv]; exact hp1)
      (by rw [hnv, hpv]; exact Nat.mod_lt _ (by omega)), hone, hnv, hpv, binValLE_encZMod w hp]
    haveI : Fact (1 < p) := ⟨hp1⟩
    rw [sub_eq_add_neg, ZMod.val_add, ZMod.val_one, ZMod.neg_val]
    by_cases hv0 : v = 0
    · subst hv0
      simp
    · rw [if_neg hv0]
      have hvpos : 0 < v.val := by
        by_contra h0
        exact hv0 ((ZMod.val_eq_zero v).mp (by omega))
      have hvlt := ZMod.val_lt v
      rw [Nat.mod_eq_of_lt (a := p - v.val) (by omega)]

/-! ## Reading a literal -/

/-- The loop body's input is `pair acc (pair X (unary j))` with `X = pair q (pair pt e)`: the
modulus, the point and the encoded clause (or CNF). -/
def argAcc (s : List Bool) : List Bool := pairFst s
/-- The modulus. -/
def argQ (s : List Bool) : List Bool := pairFst (pairFst (pairSnd s))
/-- The point. -/
def argPt (s : List Bool) : List Bool := pairFst (pairSnd (pairFst (pairSnd s)))
/-- The encoded clause or CNF. -/
def argE (s : List Bool) : List Bool := pairSnd (pairSnd (pairFst (pairSnd s)))
/-- The index, in unary. -/
def argJ (s : List Bool) : List Bool := pairSnd (pairSnd s)

@[simp] theorem argAcc_pair (acc q pt e j : List Bool) :
    argAcc (pair acc (pair (pair q (pair pt e)) j)) = acc := by simp [argAcc]
@[simp] theorem argQ_pair (acc q pt e j : List Bool) :
    argQ (pair acc (pair (pair q (pair pt e)) j)) = q := by simp [argQ]
@[simp] theorem argPt_pair (acc q pt e j : List Bool) :
    argPt (pair acc (pair (pair q (pair pt e)) j)) = pt := by simp [argPt]
@[simp] theorem argE_pair (acc q pt e j : List Bool) :
    argE (pair acc (pair (pair q (pair pt e)) j)) = e := by simp [argE]
@[simp] theorem argJ_pair (acc q pt e j : List Bool) :
    argJ (pair acc (pair (pair q (pair pt e)) j)) = j := by simp [argJ]

theorem comp_fst {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => pairFst (a z)) ∈ FP := by
  have := mem_FP_comp ha Cobham.fstBlock_mem_FP
  simpa [Function.comp] using this

theorem comp_snd {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => pairSnd (a z)) ∈ FP := by
  have := mem_FP_comp ha Cobham.sndBlock_mem_FP
  simpa [Function.comp] using this

theorem id_mem_FP' : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)

theorem argAcc_mem_FP : argAcc ∈ FP := comp_fst id_mem_FP'
theorem argQ_mem_FP : argQ ∈ FP := comp_fst (comp_fst (comp_snd id_mem_FP'))
theorem argPt_mem_FP : argPt ∈ FP := comp_fst (comp_snd (comp_fst (comp_snd id_mem_FP')))
theorem argE_mem_FP : argE ∈ FP := comp_snd (comp_snd (comp_fst (comp_snd id_mem_FP')))
theorem argJ_mem_FP : argJ ∈ FP := comp_snd (comp_snd id_mem_FP')

/-- The `j`-th entry of the encoded list, as its own serialization. -/
noncomputable def entryAt (s : List Bool) : List Bool := posAt (argE s) (argJ s).length

theorem entryAt_mem_FP : entryAt ∈ FP := posAt_mem_FP argJ_mem_FP argE_mem_FP

/-- The serialization of `true`. -/
theorem bitstringEncode_true : DataEncode.bitstringEncode true = [false, false, true, true] := by
  rw [DataEncode.bitstringEncode_def]
  show (Data.l [Data.l []]).toBits = _
  rw [Data.toBits_l]
  simp [Data.toBits_l]

/-- The serialization of `false`. -/
theorem bitstringEncode_false : DataEncode.bitstringEncode false = [false, true] := by
  rw [DataEncode.bitstringEncode_def]
  show (Data.l []).toBits = _
  rw [Data.toBits_l]
  rfl

/-- The sign of the literal, as a flag. -/
noncomputable def litSign (s : List Bool) : List Bool :=
  eqFlag (fstEnc (entryAt s)) [false, false, true, true]

theorem litSign_mem_FP : litSign ∈ FP :=
  eqFlagFn_mem_FP (fstEnc_mem_FP entryAt_mem_FP) (constFn_mem_FP _)

/-- The variable of the literal, as its binary digits. -/
noncomputable def litVarBits : List Bool → List Bool := decOne ∘ fun s => sndEnc (entryAt s)

theorem litVarBits_apply (s : List Bool) : litVarBits s = decOne (sndEnc (entryAt s)) := by
  simp only [litVarBits, Function.comp_apply]

theorem litVarBits_mem_FP : litVarBits ∈ FP :=
  mem_FP_comp (sndEnc_mem_FP entryAt_mem_FP) decOne_mem_FP

/-- The clamp of the unary conversion: twice the input length. -/
noncomputable def clampPoly : Polynomial ℕ := 2 * Polynomial.X

theorem clampPoly_eval (n : ℕ) : clampPoly.eval n = 2 * n := by
  simp [clampPoly]

/-- The variable of the literal, in unary. -/
noncomputable def litVarUnary (s : List Bool) : List Bool :=
  unaryVal clampPoly (pair s (litVarBits s))

theorem litVarUnary_mem_FP : litVarUnary ∈ FP := by
  have := mem_FP_comp (Cobham.pairFn_mem_FP id_mem_FP' litVarBits_mem_FP)
    (unaryVal_mem_FP clampPoly)
  exact this

/-- The value of the literal's variable: its block of the point. -/
noncomputable def litBlock (s : List Bool) : List Bool :=
  wBlock (argPt s) (mulLen (litVarUnary s) (argQ s)).length (argQ s).length

theorem litBlock_mem_FP : litBlock ∈ FP :=
  wBlock_mem_FP argPt_mem_FP (mulLen_mem_FP litVarUnary_mem_FP argQ_mem_FP) argQ_mem_FP

/-- The value of the literal. -/
noncomputable def litValStr (s : List Bool) : List Bool :=
  selectHead (litSign s) (litBlock s) (oneMinusMod (argQ s) (litBlock s))

theorem litValStr_mem_FP : litValStr ∈ FP :=
  Cobham.selectHeadFn_mem_FP litSign_mem_FP litBlock_mem_FP
    (oneMinusModFn_mem_FP argQ_mem_FP litBlock_mem_FP)

/-! ## The loops -/

/-- The clause loop's body: multiply the accumulator by `1 - literal`. -/
noncomputable def clauseBody (s : List Bool) : List Bool :=
  mulMod (argQ s) (argAcc s) (oneMinusMod (argQ s) (litValStr s))

theorem clauseBody_mem_FP : clauseBody ∈ FP :=
  mulModFn_mem_FP argQ_mem_FP argAcc_mem_FP (oneMinusModFn_mem_FP argQ_mem_FP litValStr_mem_FP)

/-- The value of an encoded clause at the point: `1 - Π (1 - literal)`. -/
noncomputable def clauseEval (q pt e : List Bool) : List Bool :=
  oneMinusMod q (foldLoop clauseBody (oneStr q) (pair q (pair pt e)) (posCount e))

theorem clauseEvalFn_mem_FP {a b c : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP)
    (hc : c ∈ FP) : (fun z => clauseEval (a z) (b z) (c z)) ∈ FP := by
  refine oneMinusModFn_mem_FP ha ?_
  refine foldLoopFn_mem_FP clauseBody_mem_FP (oneStrFn_mem_FP ha)
    (Cobham.pairFn_mem_FP ha (Cobham.pairFn_mem_FP hb hc)) (posCount_mem_FP hc)
    (bnd := fun z => true :: a z) ?_ ?_ ?_
  · have := mem_FP_comp ha (Cobham.cons_mem_FP true)
    simpa [Function.comp] using this
  · intro z
    rw [oneStr, List.length_append, List.length_replicate, dropOne, List.length_drop]
    simp only [List.length_cons, List.length_nil]
    omega
  · intro z acc i
    rw [clauseBody, argQ_pair, argAcc_pair, List.length_cons]
    exact le_trans (mulMod_length_le _ _ _) (Nat.le_succ _)

/-- The CNF loop's body: multiply the accumulator by the next clause's value. -/
noncomputable def cnfBody (s : List Bool) : List Bool :=
  mulMod (argQ s) (argAcc s) (clauseEval (argQ s) (argPt s) (entryAt s))

theorem cnfBody_mem_FP : cnfBody ∈ FP :=
  mulModFn_mem_FP argQ_mem_FP argAcc_mem_FP
    (clauseEvalFn_mem_FP argQ_mem_FP argPt_mem_FP entryAt_mem_FP)

/-- **The value of an encoded CNF at the point.** -/
noncomputable def cnfEval (q pt e : List Bool) : List Bool :=
  foldLoop cnfBody (oneStr q) (pair q (pair pt e)) (posCount e)

theorem cnfEvalFn_mem_FP {a b c : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP)
    (hc : c ∈ FP) : (fun z => cnfEval (a z) (b z) (c z)) ∈ FP := by
  refine foldLoopFn_mem_FP cnfBody_mem_FP (oneStrFn_mem_FP ha)
    (Cobham.pairFn_mem_FP ha (Cobham.pairFn_mem_FP hb hc)) (posCount_mem_FP hc)
    (bnd := fun z => true :: a z) ?_ ?_ ?_
  · have := mem_FP_comp ha (Cobham.cons_mem_FP true)
    simpa [Function.comp] using this
  · intro z
    rw [oneStr, List.length_append, List.length_replicate, dropOne, List.length_drop]
    simp only [List.length_cons, List.length_nil]
    omega
  · intro z acc i
    rw [cnfBody, argQ_pair, argAcc_pair, List.length_cons]
    exact le_trans (mulMod_length_le _ _ _) (Nat.le_succ _)

/-! ## Correctness -/

theorem two_pow_size_le (n : ℕ) : 2 ^ n.size ≤ 2 * n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hs : 0 < n.size := Nat.size_pos.mpr hn
    have hle : 2 ^ (n.size - 1) ≤ n := by
      by_contra hlt
      have := Nat.size_le.mpr (not_le.mp hlt)
      omega
    calc 2 ^ n.size = 2 * 2 ^ (n.size - 1) := by
          rw [← pow_succ']
          congr 1
          omega
      _ ≤ 2 * n + 1 := by omega

/-- A block of the point. -/
theorem wBlock_flatten (w : ℕ) :
    ∀ (bs : List (List Bool)) (n : ℕ) (_ : ∀ b ∈ bs, b.length = w) (hn : n < bs.length),
      wBlock bs.flatten (n * w) w = bs[n]'hn
  | [], n, _, hn => by simp at hn
  | b :: bs, 0, hb, _ => by
      rw [List.flatten_cons, wBlock, Nat.zero_mul, List.drop_zero,
        List.take_left' (hb b List.mem_cons_self)]
      rfl
  | b :: bs, n + 1, hb, hn => by
      rw [List.flatten_cons, wBlock, Nat.succ_mul, Nat.add_comm, ← List.drop_drop,
        ← hb b List.mem_cons_self, List.drop_left, ← wBlock,
        hb b List.mem_cons_self]
      rw [wBlock_flatten w bs n (fun d hd => hb d (List.mem_cons_of_mem _ hd)) (by simpa using hn)]
      rfl

variable {p : ℕ} [NeZero p]

/-- The encoded point: one block per variable below `m`. -/
def pointStr (w m : ℕ) (a : ℕ → ZMod p) : List Bool :=
  ((List.range m).map fun i => encZMod w (a i)).flatten

omit [NeZero p] in
theorem pointStr_length (w m : ℕ) (a : ℕ → ZMod p) : (pointStr w m a).length = m * w := by
  rw [pointStr, List.length_flatten, List.map_map]
  have : ((List.range m).map (List.length ∘ fun i => encZMod w (a i)))
      = (List.range m).map fun _ => w := List.map_congr_left fun i _ => by simp
  rw [this, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]

omit [NeZero p] in
theorem wBlock_pointStr (w m : ℕ) (a : ℕ → ZMod p) {n : ℕ} (hn : n < m) :
    wBlock (pointStr w m a) (n * w) w = encZMod w (a n) := by
  rw [pointStr, wBlock_flatten w _ n (fun b hb => by
      rw [List.mem_map] at hb
      obtain ⟨i, _, rfl⟩ := hb
      simp) (by simpa using hn)]
  simp

/-- `oneStr` is the residue `1`. -/
theorem oneStr_encZMod (w : ℕ) (hp : p < 2 ^ w) (hp1 : 1 < p) :
    oneStr (bitsOfLenLE w p) = encZMod w (1 : ZMod p) := by
  haveI : Fact (1 < p) := ⟨hp1⟩
  have hw : 0 < w := by
    by_contra h0
    have : w = 0 := by omega
    subst this
    simp at hp
    omega
  refine eq_of_binValLE_eq ?_ ?_
  · rw [oneStr_length _ (by simpa using hw), bitsOfLenLE_length, encZMod_length]
  · rw [binValLE_oneStr, binValLE_encZMod w hp, ZMod.val_one]

/-- **A loop multiplying residues computes their product.** -/
theorem foldIdx_mulMod (w : ℕ) (hp : p < 2 ^ w) {F : List Bool → List Bool} {x : List Bool}
    (v : ℕ → ZMod p) (N : ℕ)
    (hF : ∀ (acc : List Bool) (i : ℕ), i < N →
      F (pair acc (pair x (List.replicate i true)))
        = mulMod (bitsOfLenLE w p) acc (encZMod w (v i))) :
    ∀ (n i : ℕ) (r : ZMod p), i + n ≤ N →
      foldIdx F x (encZMod w r) i n
        = encZMod w (r * ((List.range n).map fun k => v (i + k)).prod)
  | 0, _, r, _ => by simp
  | n + 1, i, r, hN => by
      rw [foldIdx_succ, hF _ i (by omega), mulMod_encZMod w hp,
        foldIdx_mulMod w hp v N hF n (i + 1) (r * v i) (by omega), List.range_succ_eq_map,
        List.map_cons, List.prod_cons, List.map_map]
      congr 1
      rw [Nat.add_zero, mul_assoc]
      congr 2
      congr 1
      refine List.map_congr_left fun k _ => ?_
      show v (i + 1 + k) = v (i + (k + 1))
      congr 1
      omega

/-- **A literal is read correctly.** -/
theorem litValStr_eq (w m : ℕ) (hp : p < 2 ^ w) (hp1 : 1 < p) (a : ℕ → ZMod p)
    (acc : List Bool) (c : List CLit) (j : ℕ) (hj : j < c.length) (hvar : (c[j]'hj).2 < m) :
    litValStr (pair acc (pair (pair (bitsOfLenLE w p) (pair (pointStr w m a)
        (DataEncode.bitstringEncode c))) (List.replicate j true)))
      = encZMod w (QBF.arith (litQBF (c[j]'hj)) a) := by
  set s := pair acc (pair (pair (bitsOfLenLE w p) (pair (pointStr w m a)
    (DataEncode.bitstringEncode c))) (List.replicate j true)) with hs
  have hw : 0 < w := by
    by_contra h0
    have : w = 0 := by omega
    subst this
    simp at hp
    omega
  rcases hl : c[j]'hj with ⟨b, n⟩
  rw [hl] at hvar
  simp only at hvar
  have hentry : entryAt s = DataEncode.bitstringEncode (b, n) := by
    rw [entryAt, hs, argE_pair, argJ_pair, List.length_replicate, posAt_eq_of_lt hj, hl]
  have hsign : litSign s = if b then [true] else [false] := by
    rw [litSign, hentry, fstEnc_eq]
    cases b
    · rw [bitstringEncode_false]
      rcases eqFlag_flag [false, true] [false, false, true, true] with h | h
      · exact absurd ((eqFlag_eq_true_iff _ _).mp h) (by decide)
      · exact h
    · rw [bitstringEncode_true, if_pos rfl]
      exact (eqFlag_eq_true_iff _ _).mpr rfl
  have hbits : litVarBits s = Nat.bits n := by
    rw [litVarBits_apply, hentry, sndEnc_eq]
    exact decOne_encode (Nat.bits n)
  have hslen : (pointStr w m a).length ≤ s.length := by
    rw [hs, pair_length, pair_length, pair_length, pair_length]
    omega
  have hunary : litVarUnary s = List.replicate n true := by
    rw [litVarUnary, hbits, unaryVal_eq, pairSnd_pair, binValLE_bits]
    rw [pairSnd_pair, pair_length, clampPoly_eval, Nat.size_eq_bits_len]
    have h1 := two_pow_size_le n
    have h2 := pointStr_length w m a
    have h3 : m ≤ m * w := Nat.le_mul_of_pos_right m hw
    omega
  have hblock : litBlock s = encZMod w (a n) := by
    rw [litBlock, hs, argPt_pair, argQ_pair, hunary, length_mulLen, List.length_replicate,
      bitsOfLenLE_length, wBlock_pointStr w m a hvar]
  rw [litValStr, hsign, hs, argQ_pair, ← hs, hblock, arith_litQBF]
  cases b
  · rw [if_neg (by simp), selectHead_cons_false, oneMinusMod_encZMod w hp hp1]
    simp
  · rw [if_pos rfl, selectHead_cons_true]
    simp

/-- **A clause is evaluated correctly.** -/
theorem clauseEval_eq (w m : ℕ) (hp : p < 2 ^ w) (hp1 : 1 < p) (a : ℕ → ZMod p)
    (c : List CLit) (hc : ∀ l ∈ c, l.2 < m) :
    clauseEval (bitsOfLenLE w p) (pointStr w m a) (DataEncode.bitstringEncode c)
      = encZMod w (QBF.arith (clauseQBF c) a) := by
  classical
  set v : ℕ → ZMod p := fun j => if h : j < c.length then 1 - QBF.arith (litQBF (c[j]'h)) a
    else 0 with hv
  have hbody : ∀ (acc : List Bool) (i : ℕ), i < c.length →
      clauseBody (pair acc (pair (pair (bitsOfLenLE w p) (pair (pointStr w m a)
          (DataEncode.bitstringEncode c))) (List.replicate i true)))
        = mulMod (bitsOfLenLE w p) acc (encZMod w (v i)) := by
    intro acc i hi
    rw [clauseBody, argQ_pair, argAcc_pair,
      litValStr_eq w m hp hp1 a acc c i hi (hc _ (List.getElem_mem hi)),
      oneMinusMod_encZMod w hp hp1, hv]
    simp only [dif_pos hi]
  rw [clauseEval, posCount_eq, foldLoop_eq, List.length_replicate, oneStr_encZMod w hp hp1,
    foldIdx_mulMod w hp v c.length hbody c.length 0 1 (by omega), one_mul,
    oneMinusMod_encZMod w hp hp1, arith_clauseQBF]
  congr 2
  congr 1
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  rw [List.getElem_map, List.getElem_range, List.getElem_map, hv]
  have hi : i < c.length := by simpa using h2
  simp [hi]

/-- **A CNF is evaluated correctly.** -/
theorem cnfEval_encZMod (w m : ℕ) (hp : p < 2 ^ w) (hp1 : 1 < p) (a : ℕ → ZMod p)
    (φ : List (List CLit)) (hφ : ∀ c ∈ φ, ∀ l ∈ c, l.2 < m) :
    cnfEval (bitsOfLenLE w p) (pointStr w m a) (DataEncode.bitstringEncode φ)
      = encZMod w (QBF.arith (cnfQBF φ) a) := by
  classical
  set v : ℕ → ZMod p := fun i => if h : i < φ.length then QBF.arith (clauseQBF (φ[i]'h)) a
    else 0 with hv
  have hbody : ∀ (acc : List Bool) (i : ℕ), i < φ.length →
      cnfBody (pair acc (pair (pair (bitsOfLenLE w p) (pair (pointStr w m a)
          (DataEncode.bitstringEncode φ))) (List.replicate i true)))
        = mulMod (bitsOfLenLE w p) acc (encZMod w (v i)) := by
    intro acc i hi
    rw [cnfBody, argQ_pair, argAcc_pair, argPt_pair, entryAt, argE_pair, argJ_pair,
      List.length_replicate, posAt_eq_of_lt hi,
      clauseEval_eq w m hp hp1 a _ (hφ _ (List.getElem_mem hi)), hv]
    simp only [dif_pos hi]
  rw [cnfEval, posCount_eq, foldLoop_eq, List.length_replicate, oneStr_encZMod w hp hp1,
    foldIdx_mulMod w hp v φ.length hbody φ.length 0 1 (by omega), one_mul, arith_cnfQBF]
  congr 1
  congr 1
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  rw [List.getElem_map, List.getElem_range, List.getElem_map, hv]
  have hi : i < φ.length := by simpa using h2
  simp [hi]

end Complexity
