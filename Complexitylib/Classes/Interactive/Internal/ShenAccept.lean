/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive.Internal.ShenFold

/-!
# The verdict on the final transcript

⚠️ Unreviewed by Bolton

With at least `n + 1` rounds the verifier's last state is the state after the schedule is
exhausted, and its verdict reads that state: the flag is up and the claim is the matrix's value
at the point. `accepts_spec` packages this with the state invariant.

## Main results

- `lastSt_transcript`, `ShenCtx.replay_snd_stable`
- `ShenCtx.accepts_spec` — acceptance in terms of the abstract run
-/

@[expose] public section

namespace Complexity

open Cobham OpChain Shen

/-- The last verifier state of a transcript of `2 j + 2` messages. -/
theorem lastSt_transcript (τ : Transcript) (j : ℕ) (hτ : τ.length = 2 * j + 2) :
    lastSt (DataEncode.bitstringEncode τ) = τ[2 * j]'(by omega) := by
  rw [lastSt, posCount_transcript, divC_eq two_pos, List.length_replicate, hτ,
    show (2 * j + 2) / 2 = j + 1 by omega]
  simp only [dropOne, List.length_drop, length_mulC, List.length_replicate]
  rw [show (j + 1) * 2 - 1 - 1 = 2 * j by omega]
  erw [posAt_eq_of_lt (by omega)]
  rw [decOne_encode]

namespace ShenCtx

variable (Γ : ShenCtx)

/-- The arithmetized matrix. -/
noncomputable def f : (ℕ → ZMod Γ.p) → ZMod Γ.p := QBF.arith (cnfQBF Γ.I.2)

theorem NU_length' : (NU Γ.x).length = 6 * Γ.n * Γ.D + 1 := by
  have h := NU_length Γ.I
  have h2 : (DU (DataEncode.bitstringEncode Γ.I)).length = Γ.D := Γ.DU_len
  rw [h2] at h
  exact h

theorem φE_eq' : φE Γ.x = DataEncode.bitstringEncode Γ.I.2 := φE_eq Γ.I

theorem lit_lt : ∀ c ∈ Γ.I.2, ∀ l ∈ c, l.2 < Γ.m := Γ.hwf.2

/-- After the schedule is exhausted the state no longer moves. -/
theorem replay_snd_stable (S : ProverStrategy) (W : ℕ) (r : List Bool) :
    ∀ k, Γ.n ≤ k →
      (Γ.replay S (Γ.coinsOf W r k)).2 = (Γ.replay S (Γ.coinsOf W r Γ.n)).2 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k _ ih =>
      rw [coinsOf_succ, replay_append, stepPair]
      simp only
      rw [ih]
      obtain ⟨ok, cl, hst, hcl, -, -⟩ :=
        Γ.replay_state S (Γ.coinsOf W r Γ.n) (by rw [coinsOf_length])
      rw [coinsOf_length] at hst
      rw [hst, roundF_encSt_end Γ ok _ cl hcl]

/-- **Acceptance.** With `R ≥ n + 1` rounds of `W ≥ w` coins, the verifier accepts exactly when
the state after the schedule has its flag up and its claim equal to the matrix's value at its
point; the state is a represented state of the abstract run. -/
theorem accepts_spec (P : Protocol) (x₀ : List Bool) (Wp : Polynomial ℕ)
    (hv : ∀ r τ, P.vmsg (protocolView x₀ r τ) = shenVmsg Wp (protocolView Γ.x r τ))
    (hverdict : ∀ r τ, protocolView x₀ r τ ∈ P.verdict ↔ protocolView Γ.x r τ ∈ shenVerdict)
    (S : ProverStrategy) (r : List Bool) (W R : ℕ)
    (hW : Wp.eval Γ.x.length = W) (hR : P.rounds x₀.length = R) (hRn : Γ.n + 1 ≤ R)
    (hr : ∀ i < R, i * W + Γ.w ≤ r.length) :
    ∃ (ok : Bool) (cl : List Bool),
      (Γ.replay S (Γ.coinsOf W r Γ.n)).2
          = Γ.encSt ok Γ.n (Γ.absRun S (Γ.coinsOf W r Γ.n)).1 cl ∧
      cl.length ≤ Γ.w ∧
      (ok = true → (Γ.absRun S (Γ.coinsOf W r Γ.n)).2.2 = true ∧
        cl = encZMod Γ.w (Γ.absRun S (Γ.coinsOf W r Γ.n)).2.1) ∧
      ((∀ σ, Γ.MsgWF (S σ)) → ok = (Γ.absRun S (Γ.coinsOf W r Γ.n)).2.2 ∧
        cl = encZMod Γ.w (Γ.absRun S (Γ.coinsOf W r Γ.n)).2.1) ∧
      (P.Accepts S x₀ r ↔
        ok = true ∧ cl = encZMod Γ.w (Γ.f (Γ.absRun S (Γ.coinsOf W r Γ.n)).1)) := by
  obtain ⟨ok, cl, hst, hcl, hA, hB⟩ :=
    Γ.replay_state S (Γ.coinsOf W r Γ.n) (by rw [coinsOf_length])
  rw [coinsOf_length] at hst
  refine ⟨ok, cl, hst, hcl, hA, hB, ?_⟩
  rw [Protocol.Accepts, hR]
  show protocolView x₀ r _ ∈ P.verdict ↔ _
  rw [hverdict, mem_shenVerdict_iff]
  obtain ⟨htr, -⟩ := Γ.transcript_eq_replay P x₀ Wp hv S r W hW R hr
  obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
  have hlast : lastSt (DataEncode.bitstringEncode (P.transcript S x₀ r (R' + 1)))
      = (Γ.replay S (Γ.coinsOf W r Γ.n)).2 := by
    rw [htr, coinsOf_succ, replay_append, stepPair]
    simp only
    have hl := Γ.replay_length S (Γ.coinsOf W r R')
    rw [coinsOf_length] at hl
    rw [lastSt_transcript _ R' (by simp [hl]), List.getElem_append_right (by omega)]
    simp only [hl, Nat.sub_self, List.getElem_cons_zero]
    exact Γ.replay_snd_stable S W r R' (by omega)
  rw [shenVerdictFn]
  simp only [RepArgs.vx_view, RepArgs.ve_view, hlast, hst, encSt, stFlag_mkSt, stOps_mkSt,
    stPt_mkSt, stCl_mkSt]
  rw [posCount_drop, Nat.sub_self, List.replicate_zero, emptyFlag_nil,
    andBit_eq_true_iff (eqFlag_flag _ _) (andBit_flag _ _),
    andBit_eq_true_iff (Or.inl rfl) (eqFlag_flag _ _), eqFlag_eq_true_iff, eqFlag_eq_true_iff,
    φE_eq', hq', cnfEval_encZMod Γ.w Γ.m Γ.hpw' Γ.hp1 _ Γ.I.2 Γ.lit_lt]
  simp [f]

end ShenCtx

end Complexity
