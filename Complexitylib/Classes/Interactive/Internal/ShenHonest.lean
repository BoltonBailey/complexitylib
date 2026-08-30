/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive.Internal.ShenAccept

/-!
# The honest prover

⚠️ Unreviewed by Bolton

The honest prover reads the round index and the point off the verifier's state and sends the
coefficient blocks of the round's true polynomial. Its induced abstract strategy is the round
polynomial at the abstract point, so it is accepted on every challenge vector
(`accept_of_roundPolys`, a form of `OpChain.accept_honest` for strategies given by their
values).

## Main definitions

- `OpChain.ptFold` — the point after a challenge list
- `ShenCtx.ds`, `ShenCtx.hpoly`, `ShenCtx.honestS`

## Main results

- `OpChain.accept_of_roundPolys`
- `ShenCtx.chainDeg_ds`, `ShenCtx.honestS_WF`, `ShenCtx.PS_honestS`, `ShenCtx.accept_honestS`
-/

@[expose] public section

namespace Complexity

open Cobham OpChain Shen

namespace OpChain

variable {F : Type}

/-- The point after a challenge list: each round moves its variable to its challenge. -/
def ptFold : List Op → (ℕ → F) → List F → (ℕ → F)
  | o :: os, a, t :: hist => ptFold os (Function.update a o.var t) hist
  | [], a, _ => a
  | _ :: _, a, [] => a

theorem ptFold_nil (ops : List Op) (a : ℕ → F) : ptFold ops a [] = a := by
  cases ops <;> rfl

theorem ptFold_take : ∀ (ops : List Op) (a : ℕ → F) (hist : List F),
    ptFold (ops.take hist.length) a hist = ptFold ops a hist
  | _, _, [] => by rw [List.length_nil, List.take_zero, ptFold_nil, ptFold_nil]
  | [], _, _ :: _ => by rw [List.take_nil]
  | o :: os, a, t :: hist => by
      rw [List.length_cons, List.take_succ_cons, ptFold, ptFold]
      exact ptFold_take os _ hist

theorem ptFold_zero [Zero F] (m : ℕ) : ∀ (ops : List Op) (a : ℕ → F) (hist : List F),
    (∀ i, m ≤ i → a i = 0) → (∀ o ∈ ops, o.var < m) → ∀ i, m ≤ i → ptFold ops a hist i = 0
  | o :: os, a, t :: hist, ha, hops, i, hi => by
      rw [ptFold]
      refine ptFold_zero m os _ hist (fun j hj => ?_)
        (fun o' ho' => hops o' (List.mem_cons_of_mem _ ho')) i hi
      rw [Function.update_of_ne (by have := hops o List.mem_cons_self; omega)]
      exact ha j hj
  | [], _, _, ha, _, i, hi => ha i hi
  | _ :: _, _, [], ha, _, i, hi => ha i hi

variable [Field F]

/-- **A strategy that always sends the round's true polynomial is accepted.** -/
theorem accept_of_roundPolys : ∀ (ops : List Op) (ds : List ℕ) (f : (ℕ → F) → F) (a : ℕ → F)
    (P : SumCheck.Strategy F) (r : Fin ops.length → F),
    (∀ (hist : List F) (hk : hist.length < ops.length),
      (P hist).natDegree ≤ (ds.drop hist.length).headD 0 ∧
      ∀ t, (P hist).eval t = applyChain (ops.drop (hist.length + 1)) f
        (Function.update (ptFold ops a hist) (ops[hist.length]'hk).var t)) →
    accept ops ds f a (applyChain ops f a) P r
  | [], _, _, _, _, _, _ => rfl
  | o :: os, ds, f, a, P, r, hP => by
      have h0 := hP [] (by simp)
      simp only [List.length_nil, List.drop_zero, zero_add, List.drop_succ_cons,
        List.getElem_cons_zero, ptFold_nil] at h0
      refine ⟨h0.1, ?_, ?_⟩
      · rw [applyChain_cons]
        exact Op.check_eq o (applyChain os f) a h0.2
      · rw [h0.2 (r 0)]
        refine accept_of_roundPolys os ds.tail f _ _ (Fin.tail r) fun hist hk => ?_
        have h := hP (r 0 :: hist) (by simpa using hk)
        simp only [List.length_cons, List.drop_succ_cons, List.getElem_cons_succ, ptFold] at h
        rw [List.drop_tail]
        exact h

variable [DecidableEq F]

/-- The fold's point is `ptFold`. -/
theorem runFold_fst : ∀ (ops : List Op) (ds : List ℕ) (P : SumCheck.Strategy F) (ts : List F)
    (a : ℕ → F) (C : F) (ok : Bool), (runFold ops ds P ts (a, C, ok)).1 = ptFold ops a ts
  | [], _, _, ts, a, _, _ => by cases ts <;> rfl
  | _ :: _, _, _, [], _, _, _ => rfl
  | o :: os, ds, P, t :: ts, a, C, ok => by
      rw [runFold, runStep, ptFold]
      exact runFold_fst os ds.tail _ ts _ _ _

end OpChain

namespace ShenCtx

variable (Γ : ShenCtx)

/-- The degree bounds: `D` in every round. -/
def ds : List ℕ := List.replicate Γ.n Γ.D

theorem ds_drop_headD (k : ℕ) (hk : k < Γ.n) : (Γ.ds.drop k).headD 0 = Γ.D := by
  rw [ds, List.drop_replicate, show Γ.n - k = (Γ.n - k - 1) + 1 by omega, List.replicate_succ,
    List.headD_cons]

theorem qs_map_snd : Γ.I.1.map Prod.snd = List.range Γ.m := by
  refine List.ext_getElem (by simp [m]) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range]
  exact Γ.hwf.1 i (by simpa using h1)

theorem qs_nodup : (Γ.I.1.map Prod.snd).Nodup := by
  rw [qs_map_snd]
  exact List.nodup_range

theorem chainDeg_ds : ChainDeg Γ.ops Γ.ds Γ.f := by
  refine chainDeg_mono _ _ _ _ (chainDeg_uniform (F := ZMod Γ.p) Γ.I.2 Γ.I.1 Γ.qs_nodup)
    fun k hk => ?_
  have hk' : k < Γ.n := hk
  rw [ds_drop_headD Γ k hk', List.drop_replicate]
  show (List.replicate (Γ.n - k) (max 2 (litCount Γ.I.2))).headD 0 ≤ Γ.D
  rw [show Γ.n - k = (Γ.n - k - 1) + 1 by omega, List.replicate_succ, List.headD_cons, D]
  exact max_le (by omega) (by omega)

theorem chainDeg_drop {F : Type} [Field F] : ∀ (k : ℕ) (ops : List Op) (ds : List ℕ)
    (f : (ℕ → F) → F), ChainDeg ops ds f → ChainDeg (ops.drop k) (ds.drop k) f
  | 0, _, _, _, h => h
  | _ + 1, [], _, _, _ => trivial
  | k + 1, _ :: os, ds, f, h => by
      rw [List.drop_succ_cons, ← List.drop_tail]
      exact chainDeg_drop k os ds.tail f h.2

/-- The round's function is a polynomial of degree `D` in its variable. -/
theorem isPolyAt (k : ℕ) (hk : k < Γ.n) :
    QBF.IsPolyIn Γ.D (Γ.ops[k]'hk).var (applyChain (Γ.ops.drop (k + 1)) Γ.f) := by
  have h := chainDeg_drop k Γ.ops Γ.ds Γ.f Γ.chainDeg_ds
  rw [List.drop_eq_getElem_cons hk] at h
  have h1 := h.1
  rwa [ds_drop_headD Γ k hk] at h1

/-- The honest prover's polynomial for round `k` at point `a`. -/
noncomputable def hpoly (k : ℕ) (a : ℕ → ZMod Γ.p) : Polynomial (ZMod Γ.p) :=
  if h : k < Γ.n then roundPoly (Γ.isPolyAt k h) a else 0

theorem hpoly_natDegree (k : ℕ) (a : ℕ → ZMod Γ.p) : (Γ.hpoly k a).natDegree ≤ Γ.D := by
  rw [hpoly]
  split_ifs
  · exact roundPoly_natDegree _ _
  · simp

/-- The point read off a state. -/
noncomputable def ptOf (st : List Bool) : ℕ → ZMod Γ.p := fun i =>
  if i < Γ.m then (binValLE (wBlock (stPt st) (i * Γ.w) Γ.w) : ZMod Γ.p) else 0

theorem ptOf_encSt (ok : Bool) (k : ℕ) (a : ℕ → ZMod Γ.p) (cl : List Bool)
    (ha : ∀ i, Γ.m ≤ i → a i = 0) : Γ.ptOf (Γ.encSt ok k a cl) = a := by
  funext i
  rw [ptOf, encSt, stPt_mkSt]
  split_ifs with h
  · rw [wBlock_pointStr Γ.w Γ.m a h, binValLE_encZMod Γ.w Γ.hpw', ZMod.natCast_zmod_val]
  · exact (ha i (by omega)).symm

/-- The round index read off a state. -/
noncomputable def kOf (st : List Bool) : ℕ := Γ.n - (posCount (stOps st)).length

theorem kOf_encSt (ok : Bool) (k : ℕ) (a : ℕ → ZMod Γ.p) (cl : List Bool) (hk : k ≤ Γ.n) :
    Γ.kOf (Γ.encSt ok k a cl) = k := by
  rw [kOf, encSt, stOps_mkSt, posCount_drop, List.length_replicate]
  omega

/-- **The honest prover**: the coefficient blocks of the round polynomial at the state's
point. -/
noncomputable def honestS : ProverStrategy := fun σ =>
  (coeffBlocks Γ.w (Γ.hpoly (Γ.kOf (σ.getLast?.getD [])) (Γ.ptOf (σ.getLast?.getD [])))
    (Γ.D + 1)).flatten

/-- Parsing the coefficient blocks of a polynomial of degree at most `D` gives it back. -/
theorem parsePoly_coeffBlocks (g : Polynomial (ZMod Γ.p)) (hg : g.natDegree ≤ Γ.D) :
    parsePoly Γ.w Γ.D (coeffBlocks Γ.w g (Γ.D + 1)).flatten = g := by
  ext i
  by_cases hi : i ≤ Γ.D
  · obtain ⟨j, hj, rfl⟩ : ∃ j, j ≤ Γ.D ∧ i = Γ.D - j := ⟨Γ.D - i, by omega, by omega⟩
    rw [parsePoly_coeff Γ.w Γ.D _ hj, wBlock_flatten Γ.w _ j (fun b hb => by
        rw [coeffBlocks, List.mem_map] at hb
        obtain ⟨_, _, rfl⟩ := hb
        exact encZMod_length _ _) (by rw [coeffBlocks_length]; omega)]
    simp only [coeffBlocks, List.getElem_map, List.getElem_reverse, List.getElem_range,
      List.length_range]
    rw [binValLE_encZMod Γ.w Γ.hpw', ZMod.natCast_zmod_val]
    congr 1
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (parsePoly_natDegree_le _ _ _) (by omega)),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

theorem msgWF_coeffBlocks (g : Polynomial (ZMod Γ.p)) (hg : g.natDegree ≤ Γ.D) :
    Γ.MsgWF (coeffBlocks Γ.w g (Γ.D + 1)).flatten := by
  rw [MsgWF, parsePoly_coeffBlocks Γ g hg]

theorem honestS_WF : ∀ σ, Γ.MsgWF (Γ.honestS σ) := fun _ =>
  Γ.msgWF_coeffBlocks _ (Γ.hpoly_natDegree _ _)

theorem absRun_fst (S : ProverStrategy) (hist : List (ZMod Γ.p)) :
    (Γ.absRun S hist).1 = ptFold Γ.ops Γ.a0 hist := by
  rw [absRun, runFold_fst, ptFold_take]

theorem absRun_fst_zero (S : ProverStrategy) (hist : List (ZMod Γ.p)) :
    ∀ i, Γ.m ≤ i → (Γ.absRun S hist).1 i = 0 := by
  rw [absRun_fst]
  exact ptFold_zero Γ.m Γ.ops Γ.a0 hist (fun _ _ => rfl) Γ.ops_var_lt

/-- The honest prover's abstract strategy is the round polynomial at the abstract point. -/
theorem PS_honestS (hist : List (ZMod Γ.p)) (hk : hist.length < Γ.n) :
    Γ.PS Γ.honestS hist = roundPoly (Γ.isPolyAt hist.length hk) (Γ.absRun Γ.honestS hist).1 := by
  obtain ⟨ok, cl, hst, -, -, -⟩ := Γ.replay_state Γ.honestS hist hk.le
  rw [PS, hst, honestS]
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.getD_some]
  rw [kOf_encSt _ _ _ _ _ hk.le, ptOf_encSt _ _ _ _ _ (Γ.absRun_fst_zero _ _),
    parsePoly_coeffBlocks _ _ (Γ.hpoly_natDegree _ _), hpoly, dif_pos hk]

/-- **Completeness of the honest prover**, abstractly. -/
theorem accept_honestS (r : Fin Γ.ops.length → ZMod Γ.p) :
    accept Γ.ops Γ.ds Γ.f Γ.a0 (applyChain Γ.ops Γ.f Γ.a0) (Γ.PS Γ.honestS) r := by
  refine accept_of_roundPolys _ _ _ _ _ r fun hist hk => ?_
  rw [PS_honestS Γ hist hk, ds_drop_headD Γ _ hk]
  refine ⟨roundPoly_natDegree _ _, fun t => ?_⟩
  rw [roundPoly_eval, absRun_fst]

theorem ofBool_false_eq_a0 : (QBF.ofBool fun _ => false : ℕ → ZMod Γ.p) = Γ.a0 := by
  funext i
  simp [QBF.ofBool, a0]

/-- The chain's value at the origin is the truth value of the formula. -/
theorem applyChain_a0 :
    applyChain Γ.ops Γ.f Γ.a0
      = if QBF.eval (fun _ => false) (toQBF Γ.I.1 (cnfQBF Γ.I.2)) then 1 else 0 := by
  rw [← ofBool_false_eq_a0, ops, f, applyChain_shenChain_ofBool]

end ShenCtx

end Complexity
