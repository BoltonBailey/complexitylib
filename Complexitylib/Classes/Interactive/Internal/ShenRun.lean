/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive.Internal.ShenSem
public import Complexitylib.Classes.Interactive.Internal.RepeatSem

/-!
# The interaction as a replay from the challenges

⚠️ Unreviewed by Bolton

The verifier's round depends on its coin block only through its value mod `p`, so the whole
interaction with a prover `S` is a function of the list of challenges: `replay` rebuilds the
transcript and the verifier's state from that list. `transcript_eq_replay` is the invariant:
the protocol's transcript after `j` rounds, with the verifier's next message, is the replay of
the first `j` coin blocks.

## Main definitions

- `ShenCtx.coinVal`, `ShenCtx.roundF` — the round on a challenge value
- `ShenCtx.replay` — the interaction from a challenge list

## Main results

- `ShenCtx.roundStep_eq_roundF`, `ShenCtx.roundF_encSt`, `ShenCtx.roundF_encSt_end`
- `shenVmsg_view_zero`, `shenVmsg_view_succ` — the verifier's message on a view
- `ShenCtx.transcript_eq_replay` — the transcript invariant
-/

@[expose] public section

namespace Complexity

open Cobham OpChain Shen

/-! ## The verifier's message on a view -/

theorem posCount_transcript (τ : Transcript) :
    posCount (DataEncode.bitstringEncode τ) = List.replicate τ.length true := by
  erw [posCount_eq]

theorem shenVmsg_view_zero (Wp : Polynomial ℕ) (x r : List Bool) :
    shenVmsg Wp (protocolView x r []) = st0 x := by
  rw [shenVmsg, RepArgs.ve_view, RepArgs.vx_view, posCount_transcript, List.length_nil,
    List.replicate_zero, divC_eq two_pos, List.length_nil, Nat.zero_div, List.replicate_zero,
    emptyFlag_nil, selectHead_cons_true]

theorem shenVmsg_view_succ (Wp : Polynomial ℕ) (x r : List Bool) (τ : Transcript) (j : ℕ)
    (hτ : τ.length = 2 * j + 2) :
    shenVmsg Wp (protocolView x r τ)
      = roundStep x (τ[2 * j]'(by omega)) (τ[2 * j + 1]'(by omega))
          (wBlock r (j * Wp.eval x.length) (qStr x).length) := by
  have hpc : divC 2 (posCount (DataEncode.bitstringEncode τ)) = List.replicate (j + 1) true := by
    rw [posCount_transcript, divC_eq two_pos, List.length_replicate, hτ]
    congr 1
    omega
  rw [shenVmsg, RepArgs.ve_view, RepArgs.vx_view, RepArgs.vr_view, hpc, List.replicate_succ,
    emptyFlag_cons, selectHead_cons_false, prevSt, lastMsg, roundCoin, hpc]
  simp only [dropOne, List.drop_replicate, length_mulC, List.length_replicate, List.length_drop,
    coinWidth, polyRuler_length, length_mulLen, Nat.add_sub_cancel]
  rw [show (j + 1) * 2 - 1 = 2 * j + 1 by omega, show j * 2 = 2 * j by omega]
  erw [posAt_eq_of_lt (by omega), posAt_eq_of_lt (by omega)]
  rw [decOne_encode, decOne_encode]

namespace ShenCtx

variable (Γ : ShenCtx)

/-! ## The round on a challenge value -/

/-- The challenge a coin block stands for. -/
def coinVal (coin : List Bool) : ZMod Γ.p := (binValLE coin : ZMod Γ.p)

theorem coinVal_toList (v : Fin Γ.w → Bool) :
    Γ.coinVal (BitString.toList v) = reduceBits Γ.w Γ.p v := rfl

theorem coinVal_encZMod (t : ZMod Γ.p) : Γ.coinVal (encZMod Γ.w t) = t := by
  rw [coinVal, binValLE_encZMod Γ.w Γ.hpw', ZMod.natCast_zmod_val]

/-- The round, on a challenge value. -/
noncomputable def roundF (st msg : List Bool) (t : ZMod Γ.p) : List Bool :=
  roundStep Γ.x st msg (encZMod Γ.w t)

theorem roundStep_congr_coin (x st msg c c' : List Bool)
    (h : reduceMod (qStr x) c = reduceMod (qStr x) c') :
    roundStep x st msg c = roundStep x st msg c' := by
  simp only [roundStep, h]

theorem reduceMod_eq_encZMod (coin : List Bool) (hcoin : coin.length = Γ.w) :
    reduceMod (qStr Γ.x) coin = encZMod Γ.w (Γ.coinVal coin) := by
  rw [Γ.hq']
  conv_lhs => rw [← BitString.toList_ofList coin hcoin]
  rw [reduceMod_eq Γ.w Γ.hpw' Γ.hp1, reduceBits, BitString.toList_ofList]
  rfl

/-- The round depends on the coin block only through its value. -/
theorem roundStep_eq_roundF (st msg coin : List Bool) (hcoin : coin.length = Γ.w) :
    roundStep Γ.x st msg coin = Γ.roundF st msg (Γ.coinVal coin) := by
  refine roundStep_congr_coin _ _ _ _ _ ?_
  rw [Γ.reduceMod_eq_encZMod coin hcoin,
    Γ.reduceMod_eq_encZMod (encZMod Γ.w (Γ.coinVal coin)) (encZMod_length' Γ _), coinVal_encZMod]

/-- `roundStep_encSt` on a challenge value. -/
theorem roundF_encSt (k : ℕ) (hk : k < Γ.n) (ok : Bool) (a : ℕ → ZMod Γ.p) (cl : List Bool)
    (msg : List Bool) (t : ZMod Γ.p) :
    ∃ cl' : List Bool,
      Γ.roundF (Γ.encSt ok k a cl) msg t
        = Γ.encSt (ok && (decide (Γ.MsgWF msg) &&
              decide (encZMod Γ.w ((Γ.ops[k]'hk).check a (parsePoly (p := Γ.p) Γ.w Γ.D msg))
                = cl))) (k + 1) (Function.update a (Γ.ops[k]'hk).var t) cl' ∧
      cl'.length ≤ Γ.w ∧
      (Γ.MsgWF msg → cl' = encZMod Γ.w ((parsePoly (p := Γ.p) Γ.w Γ.D msg).eval t)) := by
  obtain ⟨cl', h1, h3, h2⟩ := Γ.roundStep_encSt k hk ok a cl msg _ (encZMod_length' Γ t)
  have ht : reduceBits Γ.w Γ.p (BitString.ofList (encZMod Γ.w t) (encZMod_length' Γ t)) = t := by
    rw [reduceBits, BitString.toList_ofList, binValLE_encZMod Γ.w Γ.hpw', ZMod.natCast_zmod_val]
  rw [ht] at h1 h2
  exact ⟨cl', h1, h3, h2⟩

/-- Once the schedule is exhausted the round is the identity. -/
theorem roundF_encSt_end (ok : Bool) (a : ℕ → ZMod Γ.p) (cl : List Bool) (hcl : cl.length ≤ Γ.w)
    (msg : List Bool) (t : ZMod Γ.p) :
    Γ.roundF (Γ.encSt ok Γ.n a cl) msg t = Γ.encSt ok Γ.n a cl := by
  have hops : stOps (Γ.encSt ok Γ.n a cl) = DataEncode.bitstringEncode (Γ.codes.drop Γ.n) := by
    rw [encSt, stOps_mkSt]
  simp only [roundF, roundStep, hops, posCount_drop, Nat.sub_self, List.replicate_zero,
    emptyFlag_nil, selectHead_cons_true, clampSt_encSt Γ ok Γ.n a cl hcl]

/-! ## The replay -/

/-- One round of the replay: the verifier's state is appended, the prover answers, and the
state moves on the challenge. -/
noncomputable def stepPair (S : ProverStrategy) (ts : Transcript × List Bool) (t : ZMod Γ.p) :
    Transcript × List Bool :=
  (ts.1 ++ [ts.2, S (ts.1 ++ [ts.2])], Γ.roundF ts.2 (S (ts.1 ++ [ts.2])) t)

/-- The replay from a transcript and state. -/
noncomputable def replayFrom (S : ProverStrategy) :
    Transcript × List Bool → List (ZMod Γ.p) → Transcript × List Bool
  | ts, [] => ts
  | ts, t :: hist => replayFrom S (Γ.stepPair S ts t) hist

theorem replayFrom_append (S : ProverStrategy) :
    ∀ (hist : List (ZMod Γ.p)) (ts : Transcript × List Bool) (t : ZMod Γ.p),
      Γ.replayFrom S ts (hist ++ [t]) = Γ.stepPair S (Γ.replayFrom S ts hist) t
  | [], ts, t => rfl
  | t' :: hist, ts, t => by
      rw [List.cons_append, replayFrom, replayFrom]
      exact replayFrom_append S hist _ t

/-- The interaction from the initial state, on a list of challenges. -/
noncomputable def replay (S : ProverStrategy) (hist : List (ZMod Γ.p)) : Transcript × List Bool :=
  Γ.replayFrom S ([], st0 Γ.x) hist

theorem replay_nil (S : ProverStrategy) : Γ.replay S [] = ([], st0 Γ.x) := rfl

theorem replay_append (S : ProverStrategy) (hist : List (ZMod Γ.p)) (t : ZMod Γ.p) :
    Γ.replay S (hist ++ [t]) = Γ.stepPair S (Γ.replay S hist) t :=
  Γ.replayFrom_append S hist _ t

theorem replay_length (S : ProverStrategy) :
    ∀ hist : List (ZMod Γ.p), (Γ.replay S hist).1.length = 2 * hist.length := by
  intro hist
  induction hist using List.reverseRecOn with
  | nil => rfl
  | append_singleton hist t ih =>
      rw [replay_append, stepPair, List.length_append, ih, List.length_append]
      simp only [List.length_cons, List.length_nil]
      omega

/-! ## The transcript invariant -/

/-- The challenges of the first `j` rounds, read off the coin string. -/
noncomputable def coinsOf (W : ℕ) (r : List Bool) (j : ℕ) : List (ZMod Γ.p) :=
  (List.range j).map fun i => Γ.coinVal (wBlock r (i * W) Γ.w)

theorem coinsOf_succ (W : ℕ) (r : List Bool) (j : ℕ) :
    Γ.coinsOf W r (j + 1) = Γ.coinsOf W r j ++ [Γ.coinVal (wBlock r (j * W) Γ.w)] := by
  rw [coinsOf, coinsOf, List.range_succ, List.map_append, List.map_singleton]

theorem coinsOf_length (W : ℕ) (r : List Bool) (j : ℕ) : (Γ.coinsOf W r j).length = j := by
  rw [coinsOf, List.length_map, List.length_range]

/-- **The transcript invariant.** With `W` coins per round and enough coins for the rounds
played, the transcript after `j` rounds and the verifier's next message are the replay of the
first `j` challenges. -/
theorem transcript_eq_replay (P : Protocol) (x₀ : List Bool) (Wp : Polynomial ℕ)
    (hv : ∀ r τ, P.vmsg (protocolView x₀ r τ) = shenVmsg Wp (protocolView Γ.x r τ))
    (S : ProverStrategy) (r : List Bool) (W : ℕ) (hW : Wp.eval Γ.x.length = W) (j : ℕ)
    (hr : ∀ i < j, i * W + Γ.w ≤ r.length) :
    P.transcript S x₀ r j = (Γ.replay S (Γ.coinsOf W r j)).1 ∧
      shenVmsg Wp (protocolView Γ.x r (P.transcript S x₀ r j))
        = (Γ.replay S (Γ.coinsOf W r j)).2 := by
  induction j with
  | zero => exact ⟨rfl, by rw [Protocol.transcript, shenVmsg_view_zero]; rfl⟩
  | succ j ih =>
      obtain ⟨ih1, ih2⟩ := ih fun i hi => hr i (by omega)
      have hlen : (wBlock r (j * W) Γ.w).length = Γ.w := length_wBlock (hr j (by omega))
      have hview : ∀ σ, Protocol.view x₀ r σ = protocolView x₀ r σ := fun _ => rfl
      obtain ⟨τ, hτ⟩ : ∃ τ, τ = P.transcript S x₀ r j := ⟨_, rfl⟩
      obtain ⟨v, hv'⟩ : ∃ v, v = shenVmsg Wp (protocolView Γ.x r τ) := ⟨_, rfl⟩
      rw [← hτ] at ih1 ih2
      rw [← hv'] at ih2
      have htr : P.transcript S x₀ r (j + 1) = τ ++ [v, S (τ ++ [v])] := by
        rw [Protocol.transcript_succ, hview, ← hτ, hv, ← hv']
      have hl : τ.length = 2 * j := by rw [ih1, replay_length, coinsOf_length]
      have hl' : (τ ++ [v, S (τ ++ [v])]).length = 2 * j + 2 := by simp [hl]
      rw [coinsOf_succ, replay_append, stepPair, ← ih1, ← ih2, htr]
      refine ⟨rfl, ?_⟩
      rw [shenVmsg_view_succ Wp Γ.x r _ j hl', hW,
        Γ.roundStep_eq_roundF _ _ _ (by rw [qStr_length]; exact hlen)]
      have e1 : (τ ++ [v, S (τ ++ [v])])[2 * j]'(by omega) = v := by
        rw [List.getElem_append_right (by omega)]
        simp [hl]
      have e2 : (τ ++ [v, S (τ ++ [v])])[2 * j + 1]'(by omega) = S (τ ++ [v]) := by
        rw [List.getElem_append_right (by omega)]
        simp [hl]
      rw [e1, e2, qStr_length]

end ShenCtx

end Complexity
