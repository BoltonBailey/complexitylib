/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive
public import Complexitylib.Classes.Containments.Internal.TranscriptEnc
public import Complexitylib.Classes.PCP.Internal.Materialize
public import Complexitylib.Classes.PCP.Internal.UnaryDivMod
public import Complexitylib.Classes.PCP.Internal.UnaryList

/-!
# Sequential repetition of an interactive protocol

⚠️ Unreviewed by Bolton

The `K`-fold sequential repetition of a protocol plays it `K` times in a row, each run on its own
block of coins, and accepts by majority. The verifier of the repeated protocol sees the whole
transcript so far, encoded, and has to work out from it which run it is in, extract that run's
sub-transcript, and hand it — re-encoded — together with the run's coin block to the base
verifier. All of that is polynomial-time string processing in Cobham's algebra:

- the run index is `|τ| / (2 R)`, a unary division (`Complexity.divFn2`);
- the sub-transcript is the encoded list of the messages from position `2 R i` on, written out by
  the list encoder (`Complexity.listEncFn`) from the entry scanner `Complexity.posAt`;
- the coin block is a `drop` and a `take`.

The verdict decides each run with the base verdict's decision function and counts the accepting
runs with `Complexity.countOver`.

## Main definitions

- `Complexity.RepArgs` — the base protocol, its round and coin polynomials, and a decision
  function for its verdict
- `Complexity.repVmsg`, `Complexity.repVerdict` — the repeated verifier
- `Complexity.repeatProtocol` — the repeated protocol

## Main results

- `Complexity.repVmsg_view` — what the repeated verifier says on a genuine view
- `Complexity.mem_repVerdict_view` — and how it decides
-/

@[expose] public section

namespace Complexity

open Cobham

/-! ## The data of a repetition -/

/-- What sequential repetition needs from the base protocol: the protocol, polynomials giving
its round and coin counts, and a polynomial-time decision function for its verdict. -/
structure RepArgs where
  /-- The base protocol. -/
  prot : Protocol
  /-- Its round count, as a polynomial. -/
  rp : Polynomial ℕ
  /-- Its coin count, as a polynomial. -/
  cp : Polynomial ℕ
  /-- The round count is the polynomial. -/
  rounds_eq : ∀ n, prot.rounds n = rp.eval n
  /-- The coin count is the polynomial. -/
  coins_eq : ∀ n, prot.coins n = cp.eval n
  /-- A decision function for the verdict. -/
  g : List Bool → Bool
  /-- It is polynomial-time. -/
  g_mem : (fun z => [g z]) ∈ FP
  /-- It decides the verdict. -/
  g_spec : ∀ z, z ∈ prot.verdict ↔ g z = true

/-- Composition, stated on lambdas so it elaborates against a target. -/
theorem comp_mem_FP' {f g : List Bool → List Bool} (hf : f ∈ FP) (hg : g ∈ FP) :
    (fun w => g (f w)) ∈ FP :=
  mem_FP_comp hf hg

namespace RepArgs

variable (A : RepArgs)

/-! ## Reading the view -/

/-- The input, read off a view. -/
def vx (z : List Bool) : List Bool := pairFst (pairFst z)

/-- The coins, read off a view. -/
def vr (z : List Bool) : List Bool := pairSnd (pairFst z)

/-- The encoded transcript, read off a view. -/
def ve (z : List Bool) : List Bool := pairSnd z

theorem vx_mem_FP : vx ∈ FP :=
  mem_FP_comp (f := pairFst) (g := pairFst) Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP
theorem vr_mem_FP : vr ∈ FP :=
  mem_FP_comp (f := pairFst) (g := pairSnd) Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
theorem ve_mem_FP : ve ∈ FP := Cobham.sndBlock_mem_FP

@[simp] theorem vx_view (x r : List Bool) (τ : Transcript) : vx (protocolView x r τ) = x := by
  rw [vx, protocolView, pairFst_pair, pairFst_pair]

@[simp] theorem vr_view (x r : List Bool) (τ : Transcript) : vr (protocolView x r τ) = r := by
  rw [vr, protocolView, pairFst_pair, pairSnd_pair]

@[simp] theorem ve_view (x r : List Bool) (τ : Transcript) :
    ve (protocolView x r τ) = DataEncode.bitstringEncode τ := by
  rw [ve, protocolView, pairSnd_pair]

/-- Twice the round count, in unary. -/
noncomputable def rTwo (z : List Bool) : List Bool := mulC 2 (polyRuler A.rp (vx z))

theorem rTwo_mem_FP : A.rTwo ∈ FP := mulC_mem_FP (polyRulerFn_mem_FP A.rp vx_mem_FP) 2

@[simp] theorem rTwo_length (z : List Bool) : (A.rTwo z).length = A.rp.eval (vx z).length * 2 := by
  rw [rTwo, length_mulC, polyRuler_length]

/-- The coin count, in unary. -/
noncomputable def cRuler (z : List Bool) : List Bool := polyRuler A.cp (vx z)

theorem cRuler_mem_FP : A.cRuler ∈ FP := polyRulerFn_mem_FP A.cp vx_mem_FP

@[simp] theorem cRuler_length (z : List Bool) : (A.cRuler z).length = A.cp.eval (vx z).length := by
  rw [cRuler, polyRuler_length]

/-- The number of messages so far, in unary. -/
noncomputable def cnt (z : List Bool) : List Bool := posCount (ve z)

theorem cnt_mem_FP : cnt ∈ FP := posCount_mem_FP ve_mem_FP

theorem cnt_view (x r : List Bool) (τ : Transcript) :
    cnt (protocolView x r τ) = List.replicate τ.length true := by
  rw [cnt, ve_view, posCount_eq]

/-- The run index `|τ| / (2 R)`, in unary. -/
noncomputable def idx (z : List Bool) : List Bool := divFn2 (pair (A.rTwo z) (cnt z))

theorem idx_mem_FP : A.idx ∈ FP :=
  mem_FP_comp (Cobham.pairFn_mem_FP A.rTwo_mem_FP cnt_mem_FP) divFn2_mem_FP

theorem idx_view (x r : List Bool) (τ : Transcript) (hR : 0 < A.rp.eval x.length) :
    A.idx (protocolView x r τ)
      = List.replicate (τ.length / (A.rp.eval x.length * 2)) true := by
  rw [idx, divFn2_eq (by rw [rTwo_length, vx_view]; omega), cnt_view, rTwo_length, vx_view,
    List.length_replicate]

/-! ## Coin blocks -/

/-- The coin block of run `i`, given `i` in unary. -/
noncomputable def coinBlock (z u : List Bool) : List Bool :=
  ((vr z).drop (mulLen u (A.cRuler z)).length).take (A.cRuler z).length

theorem coinBlock_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun w => A.coinBlock (a w) (b w)) ∈ FP := by
  have hr : (fun w => vr (a w)) ∈ FP := comp_mem_FP' ha vr_mem_FP
  have hc : (fun w => A.cRuler (a w)) ∈ FP := comp_mem_FP' ha A.cRuler_mem_FP
  have hm : (fun w => mulLen (b w) (A.cRuler (a w))) ∈ FP := mulLen_mem_FP hb hc
  exact Cobham.takeLenFn_mem_FP hc (dropLenFn_mem_FP hm hr)

theorem coinBlock_view (x r : List Bool) (τ : Transcript) (i : ℕ) :
    A.coinBlock (protocolView x r τ) (List.replicate i true)
      = (r.drop (i * A.cp.eval x.length)).take (A.cp.eval x.length) := by
  rw [coinBlock, vr_view, length_mulLen, List.length_replicate, cRuler_length, vx_view]

/-! ## Sub-transcripts -/

/-- The entry rule of the sub-transcript encoder: on `pair (pair e off) (unary j)`, the
`(|off| + j)`-th message of the encoded transcript `e`, as its own serialization. -/
noncomputable def entry (w : List Bool) : List Bool :=
  posAt (pairFst (pairFst w)) (pairSnd (pairFst w) ++ pairSnd w).length

theorem entry_mem_FP : entry ∈ FP := by
  have he : (fun w : List Bool => pairFst (pairFst w)) ∈ FP :=
    comp_mem_FP' Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP
  have ho : (fun w : List Bool => pairSnd (pairFst w) ++ pairSnd w) ∈ FP :=
    Cobham.appendFn_mem_FP (comp_mem_FP' Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP)
      Cobham.sndBlock_mem_FP
  exact posAt_mem_FP ho he

theorem entry_pair (e off u : List Bool) :
    entry (pair (pair e off) u) = posAt e (off.length + u.length) := by
  rw [entry, pairFst_pair, pairFst_pair, pairSnd_pair, pairSnd_pair, List.length_append]

/-- The encoding of the messages from position `|off|` on, `n` of them. -/
noncomputable def subEnc (e off n : List Bool) : List Bool :=
  listEncFn entry (pair n (pair e off))

theorem subEnc_mem_FP {a b c : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP)
    (hc : c ∈ FP) : (fun w => subEnc (a w) (b w) (c w)) ∈ FP :=
  comp_mem_FP' (Cobham.pairFn_mem_FP hc (Cobham.pairFn_mem_FP ha hb))
    (materialize_mem_FP entry_mem_FP)

/-- **The sub-transcript encoder writes the sub-transcript**: `|n|` messages from position
`|off|` on. -/
theorem subEnc_eq (τ : Transcript) (off n : List Bool) (hn : off.length + n.length ≤ τ.length) :
    subEnc (DataEncode.bitstringEncode τ) off n
      = DataEncode.bitstringEncode ((τ.drop off.length).take n.length) := by
  rw [subEnc]
  have hlen : ((τ.drop off.length).take n.length).length = n.length := by
    rw [List.length_take, List.length_drop]
    omega
  refine listEncFn_eq_bitstringEncode _ (by rw [pairFst_pair, hlen]) fun j hj => ?_
  rw [pairSnd_pair, entry_pair, List.length_replicate]
  rw [hlen] at hj
  rw [posAt_eq_of_lt (l := τ) (by omega)]
  congr 1
  rw [List.getElem_take, List.getElem_drop]

/-- With no messages asked for, the sub-transcript is empty whatever the offset. -/
theorem subEnc_nil (e off : List Bool) :
    subEnc e off [] = DataEncode.bitstringEncode ([] : Transcript) := by
  rw [subEnc]
  exact listEncFn_eq_bitstringEncode ([] : Transcript) (by rw [pairFst_pair]; rfl)
    fun j hj => by simp at hj

/-! ## The repeated verifier -/

/-- The offset `2 R i` of run `i`, given `i` in unary. -/
noncomputable def offset (z u : List Bool) : List Bool := mulLen u (A.rTwo z)

theorem offset_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun w => A.offset (a w) (b w)) ∈ FP :=
  mulLen_mem_FP hb (comp_mem_FP' ha A.rTwo_mem_FP)

@[simp] theorem offset_length (z u : List Bool) :
    (A.offset z u).length = u.length * (A.rp.eval (vx z).length * 2) := by
  rw [offset, length_mulLen, rTwo_length]

/-- The repeated verifier's next message: run the base verifier on the current run's coin block
and sub-transcript. -/
noncomputable def repVmsg (z : List Bool) : List Bool :=
  A.prot.vmsg (pair (pair (vx z) (A.coinBlock z (A.idx z)))
    (subEnc (ve z) (A.offset z (A.idx z)) ((cnt z).drop (A.offset z (A.idx z)).length)))

theorem repVmsg_mem_FP : A.repVmsg ∈ FP := by
  have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hoff : (fun z => A.offset z (A.idx z)) ∈ FP := A.offset_mem_FP hid A.idx_mem_FP
  have hrest : (fun z => (cnt z).drop (A.offset z (A.idx z)).length) ∈ FP :=
    dropLenFn_mem_FP hoff cnt_mem_FP
  have harg : (fun z => pair (pair (vx z) (A.coinBlock z (A.idx z)))
      (subEnc (ve z) (A.offset z (A.idx z)) ((cnt z).drop (A.offset z (A.idx z)).length))) ∈ FP :=
    Cobham.pairFn_mem_FP (Cobham.pairFn_mem_FP vx_mem_FP (A.coinBlock_mem_FP hid A.idx_mem_FP))
      (subEnc_mem_FP ve_mem_FP hoff hrest)
  exact mem_FP_comp (g := A.prot.vmsg) harg A.prot.vmsg_mem

/-- **The repeated verifier on a genuine view**: the base verifier on the run's coin block and
the run's sub-transcript. -/
theorem repVmsg_view (x r : List Bool) (τ : Transcript) (hR : 0 < A.rp.eval x.length) :
    A.repVmsg (protocolView x r τ)
      = A.prot.vmsg (protocolView x
          ((r.drop (τ.length / (A.rp.eval x.length * 2) * A.cp.eval x.length)).take
            (A.cp.eval x.length))
          (τ.drop (τ.length / (A.rp.eval x.length * 2) * (A.rp.eval x.length * 2)))) := by
  rw [repVmsg, idx_view A x r τ hR, coinBlock_view, ve_view, cnt_view, vx_view,
    List.drop_replicate]
  have hoff : (A.offset (protocolView x r τ) (List.replicate
      (τ.length / (A.rp.eval x.length * 2)) true)).length
      = τ.length / (A.rp.eval x.length * 2) * (A.rp.eval x.length * 2) := by
    rw [offset_length, List.length_replicate, vx_view]
  have hle : τ.length / (A.rp.eval x.length * 2) * (A.rp.eval x.length * 2) ≤ τ.length :=
    Nat.div_mul_le_self _ _
  rw [subEnc_eq τ _ _ (by rw [hoff, List.length_replicate]; omega), hoff, List.length_replicate]
  have htake : (τ.drop (τ.length / (A.rp.eval x.length * 2) * (A.rp.eval x.length * 2))).take
      (τ.length - τ.length / (A.rp.eval x.length * 2) * (A.rp.eval x.length * 2))
      = τ.drop (τ.length / (A.rp.eval x.length * 2) * (A.rp.eval x.length * 2)) :=
    List.take_of_length_le (by rw [List.length_drop])
  rw [htake]
  rfl

/-- **The repeated verifier always speaks as the base verifier does** on some view, whatever
the input: this is what bounds its message length. -/
theorem repVmsg_shape (x r : List Bool) (τ : Transcript) :
    ∃ (r' : List Bool) (τ' : Transcript),
      A.repVmsg (protocolView x r τ) = A.prot.vmsg (protocolView x r' τ') := by
  rw [repVmsg, ve_view, cnt_view, vx_view, List.drop_replicate]
  set off := A.offset (protocolView x r τ) (A.idx (protocolView x r τ)) with hoffdef
  refine ⟨A.coinBlock (protocolView x r τ) (A.idx (protocolView x r τ)), ?_⟩
  by_cases hle : off.length ≤ τ.length
  · refine ⟨(τ.drop off.length).take
      (List.replicate (τ.length - off.length) true).length, ?_⟩
    rw [subEnc_eq τ _ _ (by rw [List.length_replicate]; omega)]
    rfl
  · refine ⟨[], ?_⟩
    rw [show τ.length - off.length = 0 by omega, List.replicate_zero, subEnc_nil]
    rfl

/-- The verdict of run `i`, on `pair z (unary i)`: one bit. -/
noncomputable def runBit (w : List Bool) : List Bool :=
  A.g (pair (pair (vx (pairFst w)) (A.coinBlock (pairFst w) (pairSnd w)))
    (subEnc (ve (pairFst w)) (A.offset (pairFst w) (pairSnd w)) (A.rTwo (pairFst w))))
    |> fun b => if b then [true] else []

theorem runBit_mem_FP : A.runBit ∈ FP := by
  have hz : (fun w : List Bool => pairFst w) ∈ FP := Cobham.fstBlock_mem_FP
  have hu : (fun w : List Bool => pairSnd w) ∈ FP := Cobham.sndBlock_mem_FP
  have harg : (fun w => pair (pair (vx (pairFst w)) (A.coinBlock (pairFst w) (pairSnd w)))
      (subEnc (ve (pairFst w)) (A.offset (pairFst w) (pairSnd w)) (A.rTwo (pairFst w)))) ∈ FP :=
    Cobham.pairFn_mem_FP
      (Cobham.pairFn_mem_FP (comp_mem_FP' hz vx_mem_FP) (A.coinBlock_mem_FP hz hu))
      (subEnc_mem_FP (comp_mem_FP' hz ve_mem_FP) (A.offset_mem_FP hz hu)
        (comp_mem_FP' hz A.rTwo_mem_FP))
  have hg : (fun w => [A.g (pair (pair (vx (pairFst w)) (A.coinBlock (pairFst w) (pairSnd w)))
      (subEnc (ve (pairFst w)) (A.offset (pairFst w) (pairSnd w)) (A.rTwo (pairFst w))))]) ∈ FP :=
    comp_mem_FP' harg A.g_mem
  have := Cobham.selectHeadFn_mem_FP hg (constFn_mem_FP [true]) (constFn_mem_FP [])
  refine mem_FP_of_eq this fun w => ?_
  simp only [runBit]
  cases A.g _ <;> simp [selectHead]

/-- How many of the `K` runs accept, in unary. -/
noncomputable def acceptCount (K : ℕ) (z : List Bool) : List Bool :=
  countOver A.runBit (pair (List.replicate K true) z)

theorem acceptCount_mem_FP (K : ℕ) : A.acceptCount K ∈ FP := by
  have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have harg : (fun z : List Bool => pair (List.replicate K true) z) ∈ FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP _) hid
  exact mem_FP_comp (g := countOver A.runBit) harg (countOver_mem_FP A.runBit_mem_FP)

/-- The repeated verdict: a strict majority of the runs accept. -/
noncomputable def repVerdict (K : ℕ) : Language :=
  {z | K + 1 ≤ 2 * (A.acceptCount K z).length}

theorem repVerdict_mem_P (K : ℕ) : A.repVerdict K ∈ P := by
  refine mem_P_of_decisionFn (lenLeFlagFn_mem_FP (mulC_mem_FP (A.acceptCount_mem_FP K) 2)
    (constFn_mem_FP (List.replicate (K + 1) false))) fun z => ?_
  have key : (∃ b ∈ lenLeFlag (mulC 2 (A.acceptCount K z)) (List.replicate (K + 1) false),
      b = true) ↔ lenLeFlag (mulC 2 (A.acceptCount K z)) (List.replicate (K + 1) false)
        = [true] := by
    rcases lenLeFlag_flag (mulC 2 (A.acceptCount K z)) (List.replicate (K + 1) false)
      with h | h <;> simp [h]
  rw [key, lenLeFlag_eq_true_iff, length_mulC, List.length_replicate, repVerdict,
    Set.mem_setOf_eq]
  omega

/-- The verdict of run `i` on a genuine view, as the base decision function on the run's coin
block and full sub-transcript. -/
theorem runBit_view (x r : List Bool) (τ : Transcript) (i : ℕ)
    (hi : i * (A.rp.eval x.length * 2) + A.rp.eval x.length * 2 ≤ τ.length) :
    A.runBit (pair (protocolView x r τ) (List.replicate i true))
      = if A.g (protocolView x ((r.drop (i * A.cp.eval x.length)).take (A.cp.eval x.length))
          ((τ.drop (i * (A.rp.eval x.length * 2))).take (A.rp.eval x.length * 2)))
        then [true] else [] := by
  simp only [runBit, pairFst_pair, pairSnd_pair, coinBlock_view, ve_view, vx_view]
  have hoff : (A.offset (protocolView x r τ) (List.replicate i true)).length
      = i * (A.rp.eval x.length * 2) := by
    rw [offset_length, List.length_replicate, vx_view]
  rw [subEnc_eq τ _ _ (by rw [hoff, rTwo_length, vx_view]; exact hi), hoff, rTwo_length, vx_view]
  rfl

/-- **The repeated verdict on a genuine view.** -/
theorem mem_repVerdict_view (K : ℕ) (x r : List Bool) (τ : Transcript)
    (hτ : K * (A.rp.eval x.length * 2) ≤ τ.length) :
    protocolView x r τ ∈ A.repVerdict K
      ↔ K + 1 ≤ 2 * ((Finset.range K).filter fun i =>
          A.g (protocolView x ((r.drop (i * A.cp.eval x.length)).take (A.cp.eval x.length))
            ((τ.drop (i * (A.rp.eval x.length * 2))).take (A.rp.eval x.length * 2)))
              = true).card := by
  rw [repVerdict, Set.mem_setOf_eq, acceptCount, length_countOver]
  have hsum : (∑ i ∈ Finset.range K,
      (A.runBit (pair (protocolView x r τ) (List.replicate i true))).length)
      = ((Finset.range K).filter fun i =>
          A.g (protocolView x ((r.drop (i * A.cp.eval x.length)).take (A.cp.eval x.length))
            ((τ.drop (i * (A.rp.eval x.length * 2))).take (A.rp.eval x.length * 2)))
              = true).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [runBit_view A x r τ i (by nlinarith)]
    split_ifs <;> simp_all
  rw [hsum]

end RepArgs

end Complexity
