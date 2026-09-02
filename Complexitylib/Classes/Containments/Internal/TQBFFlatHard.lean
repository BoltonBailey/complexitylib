/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.TQBFFlat
public import Complexitylib.Classes.Containments.Internal.TQBFReach
public import Complexitylib.Classes.Containments.Internal.TQBFEmitMatrix
public import Complexitylib.Classes.Containments.PSPACESubsetNPSPACE

/-!
# Every `PSPACE` language is a *flat* quantified Boolean formula

⚠️ Unreviewed by Bolton

The same statement as `exists_savitch_instance`, but through `FlatLayout`: the prefix is
`flatPrefix`, an arithmetic function of the variable index, and the matrix is a concatenation of
indexed clause families. That is the shape an `FP` emitter can write down; the Tseitin route
cannot, because its matrix mirrors a parse tree.

## Main results

- `exists_flat_instance` — the per-input instance, well formed, true exactly on the language
-/

@[expose] public section

namespace Complexity

open QBF CircuitUnrolling Shen

/-- **Every `PSPACE` language is a flat quantified Boolean formula**, one per input. -/
theorem exists_flat_instance {L : Language} (hL : L ∈ PSPACE) :
    ∃ inst : List Bool → Instance,
      (∀ x, WellFormed (inst x)) ∧
      (fun x => DataEncode.bitstringEncode (inst x)) ∈ FP ∧
      ∀ x, x ∈ L ↔
        QBF.eval (fun _ => false) (toQBF (inst x).1 (cnfQBF (inst x).2)) = true := by
  classical
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp (PSPACE_subset_NPSPACE hL)
  obtain ⟨k, tm, S₀, hdec₀, hO⟩ := hm
  -- run the construction at a *computable* polynomial space bound: the machine stays inside the
  -- larger bound, and the emitter has to be able to evaluate it
  obtain ⟨sp, hsp⟩ := BigO.pow_polynomial_bound hO
  set S : ℕ → ℕ := fun n => sp.eval n with hSdef
  have hdec : tm.DecidesInSpace L S := NTM.DecidesInSpace.mono hsp hdec₀
  set T : List Bool → ℕ := fun x => (horizonP sp).eval x.length with hTdef
  have hT : ∀ x : List Bool, x.length + S x.length + 1 < T x := fun x => by
    show x.length + Polynomial.eval x.length sp + 1 < Polynomial.eval x.length (horizonP sp)
    rw [horizonP_eval]
    omega
  set N : List Bool → ℕ := fun x => (levelsP tm sp).eval x.length with hNdef
  have hN : ∀ x : List Bool, N x = codeBound tm.Q k x.length (S x.length) :=
    fun x => levelsP_eval tm sp x.length
  set D : (x : List Bool) → SavitchData (configWidth tm (T x)) 2 :=
    fun x => cfgSavitchDataC tm (T x) x (S x.length) (hT x) with hDdef
  set Lay : List Bool → FlatLayout :=
    fun x => { W := configWidth tm (T x), Ws := 2, n := N x } with hLdef
  set VC : (x : List Bool) → ℕ → List (List CLit) :=
    fun x off => cfgValidC tm (T x) x (S x.length) off with hVCdef
  set AC : (x : List Bool) → ℕ → List (List CLit) :=
    fun x off => cfgAccC tm (T x) off with hACdef
  set BC : (x : List Bool) → ℕ → ℕ → ℕ → List (List CLit) :=
    fun x u v s => cfgBaseC tm (T x) u v s with hBCdef
  refine ⟨fun x => ((Lay x).fullPrefix,
      (Lay x).fullClauses (VC x) (BC x) (AC x) (encodeBlock tm (T x) (tm.initCfg x))),
    fun x => ?_, ?_, fun x => ?_⟩
  · exact (Lay x).wellFormed_flat (VC x) (BC x) (AC x) _
      (fun off => mem_cfgValidC_vars tm (T x) x (S x.length) off)
      (fun off => mem_cfgAccC_vars tm (T x) off)
      (fun u v s => mem_cfgBaseC_vars tm (T x) u v s)
  · exact flatInstance_mem_FP tm sp
  refine Iff.trans ?_ ((Lay x).eval_fullQBF (VC x) (BC x) (D x) (AC x) rfl
    (fun α off => cfgValidC_eval tm (T x) x (S x.length) (le_of_lt (hT x)) α off)
    (fun α off => cfgAccC_eval tm (T x) α off)
    (fun α u v s hu _ => cfgBaseC_eval tm (T x) x (S x.length) (hT x) α u v s hu)
    (fun off => mem_cfgValidC_vars tm (T x) x (S x.length) off)
    (fun off => mem_cfgAccC_vars tm (T x) off)
    (encodeBlock tm (T x) (tm.initCfg x)) (fun _ => false)).symm
  -- the standing facts about reachable configurations
  have hwin : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x (S x.length) c := fun c hc =>
    NTM.windowed_of_reachesCfg_init hdec x hc
  have hspace : ∀ c, tm.ReachesCfg (tm.initCfg x) c →
      c.WithinDecisionSpace x.length (S x.length) := fun c hc =>
    NTM.withinDecisionSpace_of_reachesCfg hdec x hc
  have hall : ∀ c, tm.ReachesCfg (tm.initCfg x) c →
      Windowed x (S x.length) c ∧ c.WithinDecisionSpace x.length (S x.length) := fun c hc =>
    ⟨hwin c hc, hspace c hc⟩
  have hinit : Windowed x (S x.length) (tm.initCfg x) ∧
      (tm.initCfg x).WithinDecisionSpace x.length (S x.length) :=
    hall _ Relation.ReflTransGen.refl
  have hvalidInit : (D x).Valid (encodeBlock tm (T x) (tm.initCfg x)) :=
    ⟨tm.initCfg x, encBlock_encodeBlock _, hinit.1, hinit.2⟩
  have hle : ∀ c, tm.ReachesCfg (tm.initCfg x) c ↔ tm.ReachesCfgLe (2 ^ N x) (tm.initCfg x) c := by
    intro c
    constructor
    · intro hc
      obtain ⟨s, hs, hstep⟩ :=
        (NTM.reachesCfg_iff_reachesCfgLe tm (tm.initCfg x) (cfgCode x.length (S x.length))
          (fun hc hc' => NTM.cfgCode_inj_of_reachesCfg hdec x hc hc')
          (N := Fintype.card (Code tm.Q k x.length (S x.length))) le_rfl c).mp hc
      refine ⟨s, le_trans hs ?_, hstep⟩
      rw [hN]
      exact card_Code_le_two_pow_codeBound tm.Q k x.length (S x.length)
    · exact fun hc => NTM.reachesCfg_of_reachesCfgLe hc
  rw [mem_iff_exists_accepting_reachable hdec x]
  constructor
  · rintro ⟨c, hc, hhalt, hout⟩
    obtain ⟨hwc, hsc⟩ := hall c hc
    refine ⟨hvalidInit, encodeBlock tm (T x) c, ⟨c, encBlock_encodeBlock c, hwc, hsc⟩, ?_, ?_⟩
    · exact (cfgAcc_encodeBlock (tm := tm) (T := T x) c).mpr ⟨hhalt, hout⟩
    · refine (reachPowC_iff x (S x.length) (hT x) (N x) _ _).mpr ?_
      exact (reachPow_iff x (S x.length) (hT x) (N x) (tm.initCfg x) c hall hinit.1 hinit.2
        hwc hsc).mpr ((hle c).mp hc)
  · rintro ⟨-, B, ⟨cB, hEncB, hwB, hsB⟩, hacc, hreach⟩
    have hB : B = encodeBlock tm (T x) cB := eq_encodeBlock_of_encBlock hEncB
    rw [hB] at hreach hacc
    have hreach' := (reachPowC_iff x (S x.length) (hT x) (N x) _ _).mp hreach
    have hcB : tm.ReachesCfg (tm.initCfg x) cB :=
      (hle cB).mpr ((reachPow_iff x (S x.length) (hT x) (N x) (tm.initCfg x) cB hall
        hinit.1 hinit.2 hwB hsB).mp hreach')
    obtain ⟨hhalt, hout⟩ := (cfgAcc_encodeBlock (tm := tm) (T := T x) cB).mp hacc
    exact ⟨cB, hcB, hhalt, hout⟩

end Complexity
