/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.TQBFReach
public import Complexitylib.Classes.Containments.PSPACESubsetNPSPACE

/-!
# Every `PSPACE` language is a quantified Boolean formula

⚠️ Unreviewed by Bolton

Putting the pieces together: a polynomial-space machine's configuration graph is a `SavitchData`
(`cfgSavitchData`), its reachability relation is the abstract `ReachPow` (`reachPow_iff`), and
Savitch's recursion turns that into a well-formed prenex CNF formula (`SavitchData.savitch_spec`).
So every language in `PSPACE` has, for each input, a well-formed quantified Boolean formula that
is true exactly when the input is in the language.

## Main results

- `exists_savitch_instance` — the per-input instance and its two properties
-/

@[expose] public section

namespace Complexity

open QBF CircuitUnrolling Shen

/-- **Every `PSPACE` language is a quantified Boolean formula**, one per input, in the
well-formed prenex-CNF shape Shen's protocol consumes. What is *not* claimed here is that the
instance can be written down in polynomial time; that is the remaining obligation for
`PSPACE ⊆ IP`. -/
theorem exists_savitch_instance {L : Language} (hL : L ∈ PSPACE) :
    ∃ inst : List Bool → Instance,
      (∀ x, WellFormed (inst x)) ∧
      ∀ x, x ∈ L ↔
        QBF.eval (fun _ => false) (toQBF (inst x).1 (cnfQBF (inst x).2)) = true := by
  classical
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp (PSPACE_subset_NPSPACE hL)
  obtain ⟨k, tm, S, hdec, -⟩ := hm
  -- the layout horizon and the number of Savitch levels
  set T : List Bool → ℕ := fun x => x.length + S x.length + 2 with hTdef
  have hT : ∀ x : List Bool, x.length + S x.length + 1 < T x := fun x => by
    show x.length + S x.length + 1 < x.length + S x.length + 2
    omega
  set N : List Bool → ℕ := fun x => Fintype.card (Code tm.Q k x.length (S x.length)) with hNdef
  -- the data of the configuration space
  set D : (x : List Bool) → SavitchData (configWidth tm (T x)) 1 :=
    fun x => cfgSavitchData tm (T x) x (S x.length) (hT x) with hDdef
  refine ⟨fun x => ((D x).savitchPrefix (encodeBlock tm (T x) (tm.initCfg x)) (N x),
    (D x).savitchCNF (encodeBlock tm (T x) (tm.initCfg x)) (N x)), fun x => ?_, fun x => ?_⟩
  · exact (D x).wellFormed_savitch _ _
  refine Iff.trans ?_ ((D x).eval_savitch _ _ _).symm
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
  -- reachability within the code count is reachability
  have hle : ∀ c, tm.ReachesCfg (tm.initCfg x) c ↔ tm.ReachesCfgLe (2 ^ N x) (tm.initCfg x) c := by
    intro c
    constructor
    · intro hc
      obtain ⟨s, hs, hstep⟩ :=
        (NTM.reachesCfg_iff_reachesCfgLe tm (tm.initCfg x) (cfgCode x.length (S x.length))
          (fun hc hc' => NTM.cfgCode_inj_of_reachesCfg hdec x hc hc') (N := N x) le_rfl c).mp hc
      exact ⟨s, le_trans hs (Nat.le_of_lt (Nat.lt_two_pow_self)), hstep⟩
    · exact fun hc => NTM.reachesCfg_of_reachesCfgLe hc
  rw [mem_iff_exists_accepting_reachable hdec x]
  constructor
  · rintro ⟨c, hc, hhalt, hout⟩
    obtain ⟨hwc, hsc⟩ := hall c hc
    refine ⟨hvalidInit, encodeBlock tm (T x) c, ⟨c, encBlock_encodeBlock c, hwc, hsc⟩, ?_, ?_⟩
    · exact (cfgAcc_encodeBlock (tm := tm) (T := T x) c).mpr ⟨hhalt, hout⟩
    · exact (reachPow_iff x (S x.length) (hT x) (N x) (tm.initCfg x) c hall hinit.1 hinit.2
        hwc hsc).mpr ((hle c).mp hc)
  · rintro ⟨-, B, ⟨cB, hEncB, hwB, hsB⟩, hacc, hreach⟩
    have hB : B = encodeBlock tm (T x) cB := eq_encodeBlock_of_encBlock hEncB
    rw [hB] at hreach hacc
    have hcB : tm.ReachesCfg (tm.initCfg x) cB :=
      (hle cB).mpr ((reachPow_iff x (S x.length) (hT x) (N x) (tm.initCfg x) cB hall
        hinit.1 hinit.2 hwB hsB).mp hreach)
    obtain ⟨hhalt, hout⟩ := (cfgAcc_encodeBlock (tm := tm) (T := T x) cB).mp hacc
    exact ⟨cB, hcB, hhalt, hout⟩

end Complexity
