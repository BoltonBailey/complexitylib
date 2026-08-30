/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive.Internal.ShenProtocol
public import Complexitylib.Classes.Interactive.Internal.ShenAbstract

/-!
# One round of the concrete verifier is one round of the abstract run

⚠️ Unreviewed by Bolton

For a well-formed instance, `ShenCtx` bundles the derived prime `p`, the width `w` and the
schedule, and `encSt` is the string the verifier's state takes when it represents an abstract
state: a flag, the remaining schedule, a point and a claim. `roundStep_encSt` is the value of the
round on such a state: the schedule advances, the point and the claim move as `OpChain.runStep`
prescribes with the prover's polynomial read off its message, and the flag stays up exactly when
it was up, the message is well formed and the check passes.

## Main definitions

- `ShenCtx`, `ShenCtx.encSt`, `MsgWF`

## Main results

- `ShenCtx.roundStep_encSt` — the round on a represented state
-/

@[expose] public section

namespace Complexity

open Cobham OpChain Shen

/-- A well-formed instance with the parameters the verifier derives from it. -/
structure ShenCtx where
  /-- The instance. -/
  I : Instance
  /-- It is well formed. -/
  hwf : WellFormed I
  /-- The prime. -/
  p : ℕ
  /-- It is prime. -/
  hp : p.Prime
  /-- It is above `N`. -/
  hN : (NU (DataEncode.bitstringEncode I)).length < p
  /-- It is at most `2 N`. -/
  hp2 : p ≤ 2 * (NU (DataEncode.bitstringEncode I)).length
  /-- It fits in `N + 1` bits. -/
  hpw : p < 2 ^ ((NU (DataEncode.bitstringEncode I)).length + 1)
  /-- The modulus string is its binary form. -/
  hq : qStr (DataEncode.bitstringEncode I)
    = bitsOfLenLE ((NU (DataEncode.bitstringEncode I)).length + 1) p

/-- Every well-formed instance has a context. -/
theorem exists_shenCtx (I : Instance) (hwf : WellFormed I) : ∃ Γ : ShenCtx, Γ.I = I := by
  obtain ⟨p, hp, h1, h2, h3, h4⟩ := qStr_spec I
  exact ⟨⟨I, hwf, p, hp, h1, h2, h3, h4⟩, rfl⟩

namespace ShenCtx

variable (Γ : ShenCtx)

/-- The input string. -/
noncomputable def x : List Bool := DataEncode.bitstringEncode Γ.I
/-- The width. -/
noncomputable def w : ℕ := (NU Γ.x).length + 1
/-- The number of variables. -/
def m : ℕ := Γ.I.1.length
/-- The uniform degree bound. -/
def D : ℕ := litCount Γ.I.2 + 2
/-- The chain. -/
def ops : List Op := shenChain Γ.I.1 []
/-- Its codes. -/
def codes : List OpCode := shenCodes Γ.I.1 []
/-- The number of rounds. -/
def n : ℕ := Γ.ops.length

instance factPrime : Fact Γ.p.Prime := ⟨Γ.hp⟩

theorem hp1 : 1 < Γ.p := Γ.hp.one_lt
theorem hpw' : Γ.p < 2 ^ Γ.w := Γ.hpw
theorem hq' : qStr Γ.x = bitsOfLenLE Γ.w Γ.p := Γ.hq
theorem hw0 : 0 < Γ.w := by rw [w]; omega
theorem qStr_length : (qStr Γ.x).length = Γ.w := by rw [hq', bitsOfLenLE_length]
theorem DU_len : (DU Γ.x).length = Γ.D := DU_length Γ.I
theorem codes_length : Γ.codes.length = Γ.n := shenCodes_length _ _
theorem codesE_eq' : codesE Γ.x = DataEncode.bitstringEncode Γ.codes := codesE_eq Γ.I
theorem decodeOp_codes : Γ.codes.map decodeOp = Γ.ops := decodeOp_shenCodes _ _
theorem pt0_eq' : pt0 Γ.x = pointStr Γ.w Γ.m (fun _ => (0 : ZMod Γ.p)) := pt0_eq Γ.I Γ.hq'
theorem cl0_eq' : cl0 Γ.x = encZMod Γ.w (1 : ZMod Γ.p) := cl0_eq Γ.I Γ.hpw' Γ.hp1 Γ.hq'

/-- Every variable of the chain is a prefix variable, hence below `m`. -/
theorem chain_var_mem : ∀ (qs : Prefix) (vs : List ℕ), ∀ o ∈ shenChain qs vs,
    o.var ∈ vs ∨ o.var ∈ qs.map Prod.snd
  | [], _, _, h => by simp [shenChain] at h
  | (q, i) :: qs, vs, o, h => by
      rw [shenChain, List.mem_cons, List.mem_append] at h
      rcases h with rfl | h | h
      · right
        rw [quantOp_var]
        simp
      · rw [linOps, List.mem_map] at h
        obtain ⟨v, hv, rfl⟩ := h
        rw [List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · exact Or.inl hv
        · right; simp [Op.var]
      · rcases chain_var_mem qs (vs ++ [i]) o h with h | h
        · rw [List.mem_append, List.mem_singleton] at h
          rcases h with h | h
          · exact Or.inl h
          · right; rw [h]; simp
        · right
          rw [List.map_cons]
          exact List.mem_cons_of_mem _ h

theorem ops_var_lt : ∀ o ∈ Γ.ops, o.var < Γ.m := by
  intro o ho
  rcases chain_var_mem Γ.I.1 [] o ho with h | h
  · simp at h
  · rw [List.mem_map] at h
    obtain ⟨⟨q, v⟩, hmem, hv⟩ := h
    obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem hmem
    have := Γ.hwf.1 i hi
    rw [hgi] at this
    simp only at this hv
    rw [m, ← hv, this]
    exact hi

theorem ops_var_lt_of_lt (k : ℕ) (hk : k < Γ.n) : (Γ.ops[k]'hk).var < Γ.m :=
  Γ.ops_var_lt _ (List.getElem_mem hk)

/-- A code at position `k` decodes to the operator at `k`. -/
theorem decodeOp_codes_getElem (k : ℕ) (hk : k < Γ.n) :
    decodeOp (Γ.codes[k]'(by rw [codes_length]; exact hk)) = Γ.ops[k]'hk := by
  have h := Γ.decodeOp_codes
  calc decodeOp (Γ.codes[k]'(by rw [codes_length]; exact hk))
      = (Γ.codes.map decodeOp)[k]'(by rw [List.length_map, codes_length]; exact hk) :=
        (List.getElem_map decodeOp).symm
    _ = Γ.ops[k]'hk := List.getElem_of_eq h _

/-- The variable digits of a code are the variable of its operator. -/
theorem binValLE_code_var (c : OpCode) : binValLE c.2 = (decodeOp c).var := by
  rcases c with ⟨kind, v⟩
  rcases kind with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl

/-! ## Represented states -/

/-- The string of the verifier's state after `k` rounds: the flag `ok`, the rest of the
schedule, the point `a` and a claim string `cl` (the encoding of the abstract claim whenever
the flag is up). -/
noncomputable def encSt (ok : Bool) (k : ℕ) (a : ℕ → ZMod Γ.p) (cl : List Bool) : List Bool :=
  shSt [ok] (DataEncode.bitstringEncode (Γ.codes.drop k)) (pointStr Γ.w Γ.m a) cl

/-- A message is well formed when it is the coefficient blocks of the polynomial it parses to:
`D + 1` blocks of width `w`, every block below `p`. -/
def MsgWF (msg : List Bool) : Prop :=
  msg = (coeffBlocks Γ.w (parsePoly (p := Γ.p) Γ.w Γ.D msg) (Γ.D + 1)).flatten

noncomputable instance decMsgWF (msg : List Bool) : Decidable (Γ.MsgWF msg) :=
  inferInstanceAs (Decidable (msg = _))

theorem encZMod_length' (C : ZMod Γ.p) : (encZMod Γ.w C).length = Γ.w := encZMod_length _ _

/-- Encoded lists only get shorter when dropped. -/
theorem length_bitstringEncode_drop {α : Type} [DataEncode α] (l : List α) (k : ℕ) :
    (DataEncode.bitstringEncode (l.drop k)).length ≤ (DataEncode.bitstringEncode l).length := by
  rw [length_bitstringEncode_list, length_bitstringEncode_list, List.map_drop]
  have := List.sum_take_add_sum_drop (l.map fun a => (DataEncode.bitstringEncode a).length) k
  omega

/-- The clamp is the identity on a represented state. -/
theorem clampSt_encSt (ok : Bool) (k : ℕ) (a : ℕ → ZMod Γ.p) (cl : List Bool)
    (hcl : cl.length ≤ Γ.w) : clampSt Γ.x (Γ.encSt ok k a cl) = Γ.encSt ok k a cl := by
  rw [clampSt, encSt]
  simp only [stFlag_mkSt, stOps_mkSt, stPt_mkSt, stCl_mkSt]
  rw [List.take_of_length_le (by simp), List.take_of_length_le (by
      rw [codesE_eq']; exact length_bitstringEncode_drop _ _),
    List.take_of_length_le (by rw [pt0_eq', pointStr_length, pointStr_length]),
    List.take_of_length_le (by rw [qStr_length]; exact hcl)]

/-! ## Reading the head of the schedule -/

/-- The variable digits of a schedule code are `Nat.bits` of a number. -/
theorem codes_snd_bits : ∀ (qs : Prefix) (vs : List ℕ), ∀ c ∈ shenCodes qs vs, ∃ v, c.2 = Nat.bits v
  | [], _, _, h => by simp [shenCodes] at h
  | (q, i) :: qs, vs, c, h => by
      rw [shenCodes, List.mem_append, levelCodes, List.mem_cons, List.mem_map] at h
      rcases h with (rfl | ⟨v, _, rfl⟩) | h
      · exact ⟨i, rfl⟩
      · exact ⟨v, rfl⟩
      · exact codes_snd_bits qs (vs ++ [i]) c h

theorem posCount_drop (k : ℕ) :
    posCount (DataEncode.bitstringEncode (Γ.codes.drop k)) = List.replicate (Γ.n - k) true := by
  rw [posCount_eq, List.length_drop, codes_length]

theorem posAt_drop_zero (k : ℕ) (hk : k < Γ.n) :
    posAt (DataEncode.bitstringEncode (Γ.codes.drop k)) 0
      = DataEncode.bitstringEncode (Γ.codes[k]'(by rw [codes_length]; exact hk)) := by
  rw [posAt_eq_of_lt (l := Γ.codes.drop k) (i := 0) (by rw [List.length_drop, codes_length]; omega),
    List.getElem_drop]
  rfl

/-- The head code's kind and variable digits, decoded. -/
theorem head_kind (k : ℕ) (hk : k < Γ.n) :
    decOne (fstEnc (posAt (DataEncode.bitstringEncode (Γ.codes.drop k)) 0))
      = (Γ.codes[k]'(by rw [codes_length]; exact hk)).1 := by
  rw [posAt_drop_zero Γ k hk]
  rcases hc : Γ.codes[k]'(by rw [codes_length]; exact hk) with ⟨kind, v⟩
  rw [fstEnc_eq]
  exact decOne_encode kind

theorem head_var (k : ℕ) (hk : k < Γ.n) :
    decOne (sndEnc (posAt (DataEncode.bitstringEncode (Γ.codes.drop k)) 0))
      = (Γ.codes[k]'(by rw [codes_length]; exact hk)).2 := by
  rw [posAt_drop_zero Γ k hk]
  rcases hc : Γ.codes[k]'(by rw [codes_length]; exact hk) with ⟨kind, v⟩
  rw [sndEnc_eq]
  exact decOne_encode v

/-- The variable of the head code is the variable of the operator, in unary. -/
theorem headVarU_encSt (k : ℕ) (hk : k < Γ.n) (ok : Bool) (a : ℕ → ZMod Γ.p) (cl : List Bool) :
    headVarU (Γ.encSt ok k a cl) (DataEncode.bitstringEncode (Γ.codes.drop k))
      = List.replicate (Γ.ops[k]'hk).var true := by
  rw [headVarU, head_var Γ k hk]
  have hmem : (Γ.codes[k]'(by rw [codes_length]; exact hk)) ∈ Γ.codes := List.getElem_mem _
  obtain ⟨v, hv⟩ := codes_snd_bits Γ.I.1 [] _ hmem
  have hvar : v = (Γ.ops[k]'hk).var := by
    rw [← decodeOp_codes_getElem Γ k hk, ← binValLE_code_var, hv, binValLE_bits]
  rw [hv, unaryVal_eq, pairSnd_pair, binValLE_bits, hvar]
  rw [pairSnd_pair, pair_length, clampPoly_eval, Nat.size_eq_bits_len]
  have h1 := two_pow_size_le v
  have hvm : v < Γ.m := hvar ▸ Γ.ops_var_lt_of_lt k hk
  have hst : Γ.m * Γ.w ≤ (Γ.encSt ok k a cl).length := by
    rw [encSt, shSt_length, pointStr_length]
    omega
  have hw := Γ.hw0
  have : Γ.m ≤ Γ.m * Γ.w := Nat.le_mul_of_pos_right _ hw
  omega

/-! ## Messages -/

theorem length_flatten_blocks (w : ℕ) (bs : List (List Bool)) (hw : ∀ b ∈ bs, b.length = w) :
    bs.flatten.length = bs.length * w := by
  rw [List.length_flatten]
  induction bs with
  | nil => simp
  | cons b bs ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons, hw b List.mem_cons_self,
        ih fun d hd => hw d (List.mem_cons_of_mem _ hd)]
      ring

/-- A string of `k · w` bits is the concatenation of its `w`-blocks. -/
theorem flatten_wBlocks (w : ℕ) : ∀ (k : ℕ) (msg : List Bool), msg.length = k * w →
    ((List.range k).map fun j => wBlock msg (j * w) w).flatten = msg
  | 0, msg, h => by
      simp only [List.range_zero, List.map_nil, List.flatten_nil]
      exact (List.eq_nil_of_length_eq_zero (by simpa using h)).symm
  | k + 1, msg, h => by
      rw [List.range_succ_eq_map, List.map_cons, List.flatten_cons, List.map_map]
      have hrest := flatten_wBlocks w k (msg.drop w) (by rw [List.length_drop, h]; ring_nf; omega)
      have hmap : ((List.range k).map ((fun j => wBlock msg (j * w) w) ∘ Nat.succ))
          = (List.range k).map fun j => wBlock (msg.drop w) (j * w) w := by
        refine List.map_congr_left fun j _ => ?_
        simp only [Function.comp, wBlock, List.drop_drop]
        congr 2
        rw [Nat.succ_eq_add_one]
        ring
      rw [hmap, hrest, Nat.zero_mul, wBlock, List.drop_zero, List.take_append_drop]

theorem coeffBlocks_flatten_length' (w D : ℕ) (f : Polynomial (ZMod Γ.p)) :
    (coeffBlocks w f (D + 1)).flatten.length = (D + 1) * w :=
  coeffBlocks_flatten_length w f (D + 1)

/-- **Well-formedness of a message** is the length and the block conditions. -/
theorem msgWF_iff (msg : List Bool) :
    Γ.MsgWF msg ↔ msg.length = (Γ.D + 1) * Γ.w ∧
      ∀ j < Γ.D + 1, binValLE (wBlock msg (j * Γ.w) Γ.w) < Γ.p := by
  constructor
  · intro h
    rw [MsgWF] at h
    refine ⟨by rw [h, coeffBlocks_flatten_length'], fun j hj => ?_⟩
    conv_lhs => rw [h]
    rw [wBlock_flatten Γ.w _ j (fun b hb => by
        rw [coeffBlocks, List.mem_map] at hb
        obtain ⟨i, _, rfl⟩ := hb
        simp) (by simp [coeffBlocks]; omega)]
    simp only [coeffBlocks, List.getElem_map, binValLE_encZMod Γ.w Γ.hpw']
    exact ZMod.val_lt _
  · rintro ⟨hlen, hblk⟩
    rw [MsgWF]
    set bs := (List.range (Γ.D + 1)).map fun j => wBlock msg (j * Γ.w) Γ.w with hbs
    have hmsg : msg = bs.flatten := (flatten_wBlocks Γ.w (Γ.D + 1) msg hlen).symm
    have hbw : ∀ b ∈ bs, b.length = Γ.w := by
      intro b hb
      rw [hbs, List.mem_map] at hb
      obtain ⟨j, hj, rfl⟩ := hb
      rw [List.mem_range] at hj
      exact length_wBlock (by rw [hlen]; nlinarith)
    have hbv : ∀ b ∈ bs, binValLE b < Γ.p := by
      intro b hb
      rw [hbs, List.mem_map] at hb
      obtain ⟨j, hj, rfl⟩ := hb
      exact hblk j (List.mem_range.mp hj)
    have hkey := coeffBlocks_parsePoly (p := Γ.p) Γ.w Γ.D Γ.hpw' bs (by simp [hbs]) hbw hbv
    conv_lhs => rw [hmsg]
    rw [← hmsg, hmsg, hkey]

/-- The length check. -/
theorem lenEq_msg (msg : List Bool) :
    lenEqFlag msg (mulLen (DU Γ.x ++ [true]) (qStr Γ.x)) = [true]
      ↔ msg.length = (Γ.D + 1) * Γ.w := by
  rw [lenEqFlag_eq_true_iff, length_mulLen, List.length_append, DU_len, qStr_length]
  rfl

/-- The block check, on a message of the right length. -/
theorem blocksOK_iff (msg : List Bool) (hlen : msg.length = (Γ.D + 1) * Γ.w) :
    blocksOK (qStr Γ.x) msg = [true]
      ↔ ∀ j < Γ.D + 1, binValLE (wBlock msg (j * Γ.w) Γ.w) < Γ.p := by
  have hw := Γ.hw0
  have hq := Γ.qStr_length
  have hdiv : divFn2 (pair (qStr Γ.x) msg) = List.replicate (Γ.D + 1) true := by
    rw [divFn2_eq (by rw [hq]; exact hw), hlen, hq, Nat.mul_div_cancel _ hw]
  rw [blocksOK, hdiv, emptyFlag_eq_true_iff, ← List.length_eq_zero_iff, length_countOver,
    Finset.sum_eq_zero_iff]
  have hterm : ∀ j ∈ Finset.range (Γ.D + 1),
      (badBlock (pair (pair (qStr Γ.x) msg) (List.replicate j true))).length
        = if binValLE (wBlock msg (j * Γ.w) Γ.w) < Γ.p then 0 else 1 := by
    intro j hj
    rw [Finset.mem_range] at hj
    simp only [badBlock, pairFst_pair, pairSnd_pair, length_mulLen, List.length_replicate, hq]
    have hbl : (wBlock msg (j * Γ.w) Γ.w).length = Γ.w :=
      length_wBlock (by rw [hlen]; nlinarith)
    have hlt := ltFlag_eq_true_iff (wBlock msg (j * Γ.w) Γ.w) (qStr Γ.x) (by rw [hq, hbl])
    rw [Γ.hq', binValLE_bitsOfLenLE _ _ Γ.hpw'] at hlt
    rw [Γ.hq']
    by_cases h : binValLE (wBlock msg (j * Γ.w) Γ.w) < Γ.p
    · rw [if_pos h, hlt.mpr h, selectHead_cons_true]
      rfl
    · rw [if_neg h]
      rcases ltFlag_flag (wBlock msg (j * Γ.w) Γ.w) (bitsOfLenLE Γ.w Γ.p) (by simp [hbl])
        with hf | hf
      · exact absurd (hlt.mp hf) h
      · rw [hf, selectHead_cons_false]
        rfl
  constructor
  · intro h j hj
    have := h j (Finset.mem_range.mpr hj)
    rw [hterm j (Finset.mem_range.mpr hj)] at this
    split_ifs at this with hh
    exact hh
  · intro h j hj
    rw [hterm j hj, if_pos (h j (Finset.mem_range.mp hj))]

/-- The degree-and-blocks check is well-formedness. -/
theorem degOK_iff (msg : List Bool) :
    andBit (lenEqFlag msg (mulLen (DU Γ.x ++ [true]) (qStr Γ.x))) (blocksOK (qStr Γ.x) msg) = [true]
      ↔ Γ.MsgWF msg := by
  rw [andBit_eq_true_iff (lenEqFlag_flag _ _) (by unfold blocksOK; exact emptyFlag_flag _),
    lenEq_msg, msgWF_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (Γ.blocksOK_iff msg h1).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (Γ.blocksOK_iff msg h1).mpr h2⟩

/-! ## The round on a represented state -/

theorem hornerEval_length_le (q x cs : List Bool) : (hornerEval q x cs).length ≤ q.length := by
  rw [hornerEval, hornerStepP_iterate x q (List.replicate q.length false, cs), hornerPack,
    pairFst_pair]
  have := (hornerStep_iterate_length q x (List.replicate q.length false) cs cs.length).1
  simpa using this

/-- **The round.** On a represented state with schedule position `k < n`, the round pops the
schedule, moves the point to the reduced coin block at the operator's variable, keeps the flag
up exactly when the message is well formed and passes the operator's check, and (on a
well-formed message) sets the claim to the prover's polynomial at the challenge. -/
theorem roundStep_encSt (k : ℕ) (hk : k < Γ.n) (ok : Bool) (a : ℕ → ZMod Γ.p) (cl : List Bool)
    (msg coin : List Bool) (hcoin : coin.length = Γ.w) :
    ∃ cl' : List Bool,
      roundStep Γ.x (Γ.encSt ok k a cl) msg coin
        = shSt [ok && (decide (Γ.MsgWF msg) &&
              decide (encZMod Γ.w ((Γ.ops[k]'hk).check a (parsePoly (p := Γ.p) Γ.w Γ.D msg))
                = cl))]
            (DataEncode.bitstringEncode (Γ.codes.drop (k + 1)))
            (pointStr Γ.w Γ.m (Function.update a (Γ.ops[k]'hk).var
              (reduceBits Γ.w Γ.p (BitString.ofList coin hcoin)))) cl' ∧
      cl'.length ≤ Γ.w ∧
      (Γ.MsgWF msg → cl' = encZMod Γ.w ((parsePoly (p := Γ.p) Γ.w Γ.D msg).eval
        (reduceBits Γ.w Γ.p (BitString.ofList coin hcoin)))) := by
  haveI : NeZero Γ.p := ⟨Γ.hp.ne_zero⟩
  have hw := Γ.hw0
  have hq := Γ.qStr_length
  set s := parsePoly (p := Γ.p) Γ.w Γ.D msg with hs
  set t := reduceBits Γ.w Γ.p (BitString.ofList coin hcoin) with ht
  set c := Γ.codes[k]'(by rw [codes_length]; exact hk) with hc
  have hcv : (decodeOp c).var = (Γ.ops[k]'hk).var := by rw [hc, decodeOp_codes_getElem]
  have hvm : (Γ.ops[k]'hk).var < Γ.m := Γ.ops_var_lt_of_lt k hk
  have hne : emptyFlag (posCount (DataEncode.bitstringEncode (Γ.codes.drop k))) = [false] := by
    rw [posCount_drop]
    rcases emptyFlag_flag (List.replicate (Γ.n - k) true) with h | h
    · rw [emptyFlag_eq_true_iff, List.replicate_eq_nil_iff] at h
      omega
    · exact h
  have hiU := Γ.headVarU_encSt k hk ok a cl
  rw [encSt] at hiU
  have hav : wBlock (pointStr Γ.w Γ.m a)
      (mulLen (List.replicate (Γ.ops[k]'hk).var true) (qStr Γ.x)).length (qStr Γ.x).length
        = encZMod Γ.w (a (decodeOp c).var) := by
    rw [length_mulLen, List.length_replicate, hq, hcv]
    exact wBlock_pointStr Γ.w Γ.m a hvm
  have hkind : decOne (fstEnc (posAt (DataEncode.bitstringEncode (Γ.codes.drop k)) 0)) = c.1 :=
    Γ.head_kind k hk
  have htc : reduceMod (qStr Γ.x) coin = encZMod Γ.w t := by
    rw [ht, Γ.hq']
    conv_lhs => rw [← BitString.toList_ofList coin hcoin]
    exact reduceMod_eq Γ.w Γ.hpw' Γ.hp1 _
  have hdrop : dropChild (DataEncode.bitstringEncode (Γ.codes.drop k))
      = DataEncode.bitstringEncode (Γ.codes.drop (k + 1)) := by
    rw [dropChild_bitstringEncode, List.tail_drop]
  have hrep : replaceBlock (pointStr Γ.w Γ.m a) (qStr Γ.x)
      (List.replicate (Γ.ops[k]'hk).var true) (encZMod Γ.w t)
        = pointStr Γ.w Γ.m (Function.update a (Γ.ops[k]'hk).var t) :=
    replaceBlock_pointStr Γ.w Γ.m a _ hq hvm t
  have hdeg : ∀ h : Γ.MsgWF msg,
      msg = (coeffBlocks Γ.w s (Γ.D + 1)).flatten := fun h => h
  have hsd : s.natDegree < Γ.D + 1 := Nat.lt_succ_of_le (parsePoly_natDegree_le Γ.w Γ.D msg)
  refine ⟨hornerEval (qStr Γ.x) (encZMod Γ.w t) msg, ?_,
    by rw [← hq]; exact hornerEval_length_le _ _ _, ?_⟩
  · rw [roundStep]
    simp only [encSt, stOps_mkSt, stPt_mkSt, stFlag_mkSt, stCl_mkSt]
    rw [hne, selectHead_cons_false, hiU, hav, hkind, htc, hdrop, hrep]
    -- the clamp is the identity
    have hflag : ∀ f : List Bool, f = [true] ∨ f = [false] → f.length ≤ 1 := by
      rintro f (rfl | rfl) <;> simp
    rw [clampSt]
    simp only [stFlag_mkSt, stOps_mkSt, stPt_mkSt, stCl_mkSt]
    rw [List.take_of_length_le (hflag _ (andBit_flag _ _)),
      List.take_of_length_le (by rw [codesE_eq']; exact length_bitstringEncode_drop _ _),
      List.take_of_length_le (by rw [pt0_eq', pointStr_length, pointStr_length]),
      List.take_of_length_le (hornerEval_length_le _ _ _)]
    -- the flag
    congr 1
    by_cases hWF : Γ.MsgWF msg
    · have hd : andBit (lenEqFlag msg (mulLen (DU Γ.x ++ [true]) (qStr Γ.x)))
          (blocksOK (qStr Γ.x) msg) = [true] := (Γ.degOK_iff msg).mpr hWF
      have hchk : eqFlag (opCheckVal (qStr Γ.x) c.1 (encZMod Γ.w (a (decodeOp c).var)) msg)
          cl = [decide (encZMod Γ.w ((Γ.ops[k]'hk).check a s) = cl)] := by
        have hval : opCheckVal (qStr Γ.x) c.1 (encZMod Γ.w (a (decodeOp c).var)) msg
            = encZMod Γ.w ((Γ.ops[k]'hk).check a s) := by
          conv_lhs => rw [hdeg hWF]
          rw [Γ.hq', opCheckVal_eq Γ.w Γ.hpw' hw c a s (Γ.D + 1) hsd, hc,
            decodeOp_codes_getElem]
        rw [hval]
        by_cases hce : encZMod Γ.w ((Γ.ops[k]'hk).check a s) = cl
        · rw [decide_eq_true hce, (eqFlag_eq_true_iff _ _).mpr hce]
        · rcases eqFlag_flag (encZMod Γ.w ((Γ.ops[k]'hk).check a s)) cl with h | h
          · exact absurd ((eqFlag_eq_true_iff _ _).mp h) hce
          · rw [h, decide_eq_false hce]
      rw [hd, hchk, decide_eq_true hWF]
      cases ok <;> cases hce : decide (encZMod Γ.w ((Γ.ops[k]'hk).check a s) = cl) <;>
        simp [andBit]
    · have hd : andBit (lenEqFlag msg (mulLen (DU Γ.x ++ [true]) (qStr Γ.x)))
          (blocksOK (qStr Γ.x) msg) = [false] := by
        rcases andBit_flag (lenEqFlag msg (mulLen (DU Γ.x ++ [true]) (qStr Γ.x)))
          (blocksOK (qStr Γ.x) msg) with h | h
        · exact absurd ((Γ.degOK_iff msg).mp h) hWF
        · exact h
      rw [hd, decide_eq_false hWF]
      rcases eqFlag_flag (opCheckVal (qStr Γ.x) c.1 (encZMod Γ.w (a (decodeOp c).var)) msg)
        cl with h | h <;> rw [h] <;> cases ok <;> simp [andBit]
  · intro hWF
    conv_lhs => rw [hdeg hWF]
    rw [Γ.hq']
    exact hornerEval_encZMod Γ.w Γ.hpw' hw s (Γ.D + 1) hsd t

end ShenCtx

end Complexity
