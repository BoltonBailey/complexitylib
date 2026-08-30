/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive.Internal.ShenRun

/-!
# The replayed state is the abstract run

⚠️ Unreviewed by Bolton

A prover `S` induces an abstract strategy `PS`: the polynomial parsed from its message on the
replayed transcript. `replay_state` is the invariant linking the two runs: after `k ≤ n`
challenges the verifier's state is a represented state whose point is the abstract point, whose
flag being up forces the abstract flag up with the claim encoded, and which tracks the abstract
run exactly when every prover message is well formed.

## Main definitions

- `ShenCtx.PS`, `ShenCtx.absRun`

## Main results

- `OpChain.runFold_snoc`, `ShenCtx.absRun_append`
- `ShenCtx.replay_state` — the invariant
-/

@[expose] public section

namespace Complexity

open Cobham OpChain Shen

namespace OpChain

variable {F : Type} [Field F] [DecidableEq F]

/-- The fold on one more round. -/
theorem runFold_snoc : ∀ (os : List Op) (ds : List ℕ) (ts : List F) (o : Op) (d : ℕ)
    (P : SumCheck.Strategy F) (t : F) (st : (ℕ → F) × F × Bool),
    os.length = ts.length → ds.length = ts.length →
    runFold (os ++ [o]) (ds ++ [d]) P (ts ++ [t]) st = runStep o d (P ts) t (runFold os ds P ts st)
  | [], ds, ts, o, d, P, t, st, h1, h2 => by
      rw [List.length_nil] at h1
      obtain rfl := List.eq_nil_of_length_eq_zero h1.symm
      obtain rfl := List.eq_nil_of_length_eq_zero (h2.trans List.length_nil)
      simp [runFold]
  | o' :: os, ds, ts, o, d, P, t, st, h1, h2 => by
      cases ts with
      | nil => simp at h1
      | cons t' ts =>
        cases ds with
        | nil => simp at h2
        | cons d' ds =>
          simp only [List.cons_append, runFold, List.tail_cons, List.headD_cons]
          exact runFold_snoc os ds ts o d (fun h => P (t' :: h)) t _ (by simpa using h1)
            (by simpa using h2)

end OpChain

namespace ShenCtx

variable (Γ : ShenCtx)

/-- The abstract strategy a prover induces: the polynomial read off its message on the
replayed transcript. -/
noncomputable def PS (S : ProverStrategy) : SumCheck.Strategy (ZMod Γ.p) :=
  fun hist => parsePoly Γ.w Γ.D (S ((Γ.replay S hist).1 ++ [(Γ.replay S hist).2]))

/-- The initial point. -/
def a0 : ℕ → ZMod Γ.p := Function.const ℕ 0

/-- The abstract run of the first `|hist|` rounds. -/
noncomputable def absRun (S : ProverStrategy) (hist : List (ZMod Γ.p)) :
    (ℕ → ZMod Γ.p) × ZMod Γ.p × Bool :=
  runFold (Γ.ops.take hist.length) (List.replicate hist.length Γ.D) (Γ.PS S) hist
    (Γ.a0, (1 : ZMod Γ.p), true)

theorem absRun_nil (S : ProverStrategy) : Γ.absRun S [] = (Γ.a0, (1 : ZMod Γ.p), true) := rfl

theorem absRun_append (S : ProverStrategy) (hist : List (ZMod Γ.p)) (t : ZMod Γ.p)
    (hk : hist.length < Γ.n) :
    Γ.absRun S (hist ++ [t])
      = runStep (Γ.ops[hist.length]'hk) Γ.D (Γ.PS S hist) t (Γ.absRun S hist) := by
  rw [absRun, absRun, List.length_append, List.length_singleton,
    List.take_succ_eq_append_getElem hk, List.replicate_succ']
  exact runFold_snoc _ _ _ _ _ _ _ _ (by rw [List.length_take]; exact min_eq_left hk.le)
    List.length_replicate

/-- The initial state is the represented initial abstract state. -/
theorem st0_eq : st0 Γ.x = Γ.encSt true 0 Γ.a0 (encZMod Γ.w (1 : ZMod Γ.p)) := by
  have hwf : wfFlag Γ.x = [true] := (wfFlag_eq_true_iff Γ.I).mpr Γ.hwf
  rw [st0, encSt, List.drop_zero, codesE_eq', pt0_eq', cl0_eq', hwf]
  rfl

/-- **The state invariant.** -/
theorem replay_state (S : ProverStrategy) (hist : List (ZMod Γ.p)) (hk : hist.length ≤ Γ.n) :
    ∃ (ok : Bool) (cl : List Bool),
      (Γ.replay S hist).2 = Γ.encSt ok hist.length (Γ.absRun S hist).1 cl ∧ cl.length ≤ Γ.w ∧
      (ok = true → (Γ.absRun S hist).2.2 = true ∧ cl = encZMod Γ.w (Γ.absRun S hist).2.1) ∧
      ((∀ σ, Γ.MsgWF (S σ)) →
        ok = (Γ.absRun S hist).2.2 ∧ cl = encZMod Γ.w (Γ.absRun S hist).2.1) := by
  induction hist using List.reverseRecOn with
  | nil =>
      refine ⟨true, encZMod Γ.w (1 : ZMod Γ.p), ?_, (encZMod_length' Γ _).le, fun _ => ⟨rfl, rfl⟩,
        fun _ => ⟨rfl, rfl⟩⟩
      rw [replay_nil, absRun_nil, List.length_nil]
      exact st0_eq Γ
  | append_singleton hist t ih =>
      rw [List.length_append, List.length_singleton] at hk ⊢
      obtain ⟨ok, cl, hst, hcl, hA, hB⟩ := ih (by omega)
      have hk' : hist.length < Γ.n := by omega
      obtain ⟨⟨a, C, okA⟩, hF⟩ : ∃ q, q = Γ.absRun S hist := ⟨_, rfl⟩
      rw [← hF] at hst hA hB
      rw [replay_append, stepPair, hst, absRun_append Γ S hist t hk', ← hF]
      obtain ⟨msg, hmsg⟩ : ∃ msg, msg = S ((Γ.replay S hist).1 ++ [Γ.encSt ok hist.length a cl]) :=
        ⟨_, rfl⟩
      have hPS : Γ.PS S hist = parsePoly Γ.w Γ.D msg := by rw [PS, hmsg, hst]
      obtain ⟨cl', h1, hcl', h2⟩ := Γ.roundF_encSt hist.length hk' ok a cl msg t
      rw [← hmsg, h1, hPS]
      simp only at hA hB
      have hinj := (encZMod_injective Γ.w Γ.hpw').eq_iff (a := (Γ.ops[hist.length]'hk').check a
        (parsePoly Γ.w Γ.D msg)) (b := C)
      have hdeg : (parsePoly (p := Γ.p) Γ.w Γ.D msg).natDegree ≤ Γ.D :=
        parsePoly_natDegree_le Γ.w Γ.D msg
      refine ⟨_, cl', rfl, hcl', ?_, ?_⟩
      · intro h
        simp only [Bool.and_eq_true_iff, decide_eq_true_iff] at h
        obtain ⟨hok, hWF, hce⟩ := h
        obtain ⟨hokA, rfl⟩ := hA hok
        rw [hinj] at hce
        exact ⟨by simp [runStep, hokA, hdeg, hce], h2 hWF⟩
      · intro hWF
        have hWFm : Γ.MsgWF msg := by rw [hmsg]; exact hWF _
        obtain ⟨rfl, rfl⟩ := hB hWF
        refine ⟨?_, h2 hWFm⟩
        simp [runStep, hdeg, hinj, hWFm]

end ShenCtx

end Complexity
