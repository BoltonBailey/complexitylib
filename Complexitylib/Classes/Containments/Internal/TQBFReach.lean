/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.TQBFConfig
public import Complexitylib.Classes.Containments.Internal.BoundedReach
public import Complexitylib.Classes.Containments.Internal.SavitchReach

/-!
# Block reachability is machine reachability

⚠️ Unreviewed by Bolton

A windowed, space-bounded configuration is determined by its block (`blockInj`), so the
reachability relation `SavitchData.ReachPow` on blocks is exactly `NTM.ReachesCfgLe` on the
configurations they encode, as long as everything reachable stays windowed and inside the space
bound. `reachPow_iff` is that equivalence.

## Main definitions

- `encodeBlock` — a configuration's block

## Main results

- `encBlock_encodeBlock`, `eq_encodeBlock_of_encBlock`
- `reachPow_to_reaches`, `reaches_to_reachPow`, `reachPow_iff`
-/

@[expose] public section

namespace Complexity

open QBF CircuitUnrolling

variable {k : ℕ} {tm : NTM k} {T : ℕ}

/-- The block of a configuration. -/
noncomputable def encodeBlock (tm : NTM k) (T : ℕ) (c : Cfg k tm.Q) :
    Fin (configWidth tm T) → Bool :=
  fun i => ConfigAtom.value c ((configAtomEquiv tm T).symm i)

theorem symm_configAtomEquiv (atom : ConfigAtom tm T) :
    (configAtomEquiv tm T).symm ⟨configIndex tm T atom, configIndex_lt tm T atom⟩ = atom := by
  rw [Equiv.symm_apply_eq]
  exact (Fin.ext (configAtomEquiv_apply_val tm T atom)).symm

theorem encBlock_encodeBlock (c : Cfg k tm.Q) : EncBlock tm T (encodeBlock tm T c) c := by
  intro atom
  rw [blockAtom, encodeBlock, symm_configAtomEquiv]

theorem mk_configIndex_symm (i : Fin (configWidth tm T)) :
    (⟨configIndex tm T ((configAtomEquiv tm T).symm i), configIndex_lt tm T _⟩ :
      Fin (configWidth tm T)) = i := by
  refine Fin.ext ?_
  show configIndex tm T ((configAtomEquiv tm T).symm i) = i.val
  rw [← configAtomEquiv_apply_val, Equiv.apply_symm_apply]

theorem eq_encodeBlock_of_encBlock {u : Fin (configWidth tm T) → Bool} {c : Cfg k tm.Q}
    (h : EncBlock tm T u c) : u = encodeBlock tm T c := by
  funext i
  have hi := h ((configAtomEquiv tm T).symm i)
  rw [blockAtom] at hi
  rw [mk_configIndex_symm] at hi
  rw [hi, encodeBlock]

theorem reachesCfgLe_one_choiceStep (tm : NTM k) (b : Bool) (c : Cfg k tm.Q) :
    tm.ReachesCfgLe 1 c (choiceStep tm b c) := by
  rw [choiceStep_eq]
  split_ifs with h
  · exact ⟨0, by omega, NTM.ReachesCfgIn.refl c⟩
  · exact ⟨1, le_rfl, NTM.ReachesCfgIn.head ⟨h, b, rfl⟩ (NTM.ReachesCfgIn.refl _)⟩

theorem windowed_choiceStep {x : List Bool} {S : ℕ} {c : Cfg k tm.Q} (b : Bool)
    (hw : Windowed x S c) (hs : c.WithinDecisionSpace x.length S) :
    Windowed x S (choiceStep tm b c) := by
  rw [choiceStep_eq]
  split_ifs with h
  · exact hw
  · exact hw.stepCfg b hs

section

variable (x : List Bool) (S : ℕ) (hT : x.length + S + 1 < T)

/-- **Block reachability gives machine reachability.** -/
theorem reachPow_to_reaches : ∀ (n : ℕ) (u v : Fin (configWidth tm T) → Bool),
    (cfgSavitchData tm T x S hT).ReachPow n u v →
    ∀ cu cv : Cfg k tm.Q, EncBlock tm T u cu → Windowed x S cu →
      cu.WithinDecisionSpace x.length S →
      EncBlock tm T v cv → Windowed x S cv → cv.WithinDecisionSpace x.length S →
      tm.ReachesCfgLe (2 ^ n) cu cv
  | 0, u, v, h, cu, cv, hu, hwu, hsu, hv, hwv, hsv => by
      obtain ⟨-, -, σ, c, hEnc, hwc, hsc, hcase⟩ := h
      have hcu : c = cu := blockInj tm T x S (le_of_lt hT) hEnc hwc hu hwu hsu
      subst hcu
      rw [pow_zero]
      rcases hcase with hvu | hstep
      · have : cv = c := by
          refine blockInj (u := v) tm T x S (le_of_lt hT) hv hwv ?_ hwc hsc
          rw [hvu]
          exact hEnc
        rw [this]
        exact ⟨0, by omega, NTM.ReachesCfgIn.refl c⟩
      · have hstepW : Windowed x S (choiceStep tm (σ 0) c) := windowed_choiceStep _ hwc hsc
        have : choiceStep tm (σ 0) c = cv :=
          blockInj tm T x S (le_of_lt hT) hstep hstepW hv hwv hsv
        rw [← this]
        exact reachesCfgLe_one_choiceStep tm (σ 0) c
  | n + 1, u, v, h, cu, cv, hu, hwu, hsu, hv, hwv, hsv => by
      obtain ⟨m, h1, h2⟩ := h
      obtain ⟨cm, hEncm, hwm, hsm⟩ := SavitchData.ReachPow.valid_right _ n h1
      refine (NTM.reachesCfgLe_two_pow_succ_iff tm n cu cv).mpr ⟨cm, ?_, ?_⟩
      · exact reachPow_to_reaches n u m h1 cu cm hu hwu hsu hEncm hwm hsm
      · exact reachPow_to_reaches n m v h2 cm cv hEncm hwm hsm hv hwv hsv

/-- **Machine reachability gives block reachability**, as long as everything reachable stays
windowed and inside the space bound. -/
theorem reaches_to_reachPow : ∀ (n : ℕ) (cu cv : Cfg k tm.Q),
    tm.ReachesCfgLe (2 ^ n) cu cv →
    (∀ c, tm.ReachesCfg cu c → Windowed x S c ∧ c.WithinDecisionSpace x.length S) →
    Windowed x S cu → cu.WithinDecisionSpace x.length S →
    (cfgSavitchData tm T x S hT).ReachPow n (encodeBlock tm T cu) (encodeBlock tm T cv)
  | 0, cu, cv, h, hall, hwu, hsu => by
      rw [pow_zero] at h
      have hreach : tm.ReachesCfg cu cv := NTM.reachesCfg_of_reachesCfgLe h
      obtain ⟨hwv, hsv⟩ := hall cv hreach
      have hbase : ∃ σ : Fin 1 → Bool, CfgBase tm T x S (encodeBlock tm T cu)
          (encodeBlock tm T cv) σ := by
        rcases (NTM.reachesCfgLe_one_iff tm cu cv).mp h with h0 | ⟨hne, b, h0⟩
        · refine ⟨fun _ => false, cu, encBlock_encodeBlock cu, hwu, hsu, Or.inl ?_⟩
          rw [h0]
        · refine ⟨fun _ => b, cu, encBlock_encodeBlock cu, hwu, hsu, Or.inr ?_⟩
          rw [choiceStep_eq, if_neg hne, ← h0]
          exact encBlock_encodeBlock _
      obtain ⟨σ, hσ⟩ := hbase
      exact ⟨⟨cu, encBlock_encodeBlock cu, hwu, hsu⟩, ⟨cv, encBlock_encodeBlock cv, hwv, hsv⟩,
        σ, hσ⟩
  | n + 1, cu, cv, h, hall, hwu, hsu => by
      obtain ⟨cm, h1, h2⟩ := (NTM.reachesCfgLe_two_pow_succ_iff tm n cu cv).mp h
      have hreachm : tm.ReachesCfg cu cm := NTM.reachesCfg_of_reachesCfgLe h1
      obtain ⟨hwm, hsm⟩ := hall cm hreachm
      exact ⟨encodeBlock tm T cm,
        reaches_to_reachPow n cu cm h1 hall hwu hsu,
        reaches_to_reachPow n cm cv h2
          (fun c hc => hall c (hreachm.trans hc)) hwm hsm⟩

/-- **Block reachability is machine reachability.** -/
theorem reachPow_iff (n : ℕ) (cu cv : Cfg k tm.Q)
    (hall : ∀ c, tm.ReachesCfg cu c → Windowed x S c ∧ c.WithinDecisionSpace x.length S)
    (hwu : Windowed x S cu) (hsu : cu.WithinDecisionSpace x.length S)
    (hwv : Windowed x S cv) (hsv : cv.WithinDecisionSpace x.length S) :
    (cfgSavitchData tm T x S hT).ReachPow n (encodeBlock tm T cu) (encodeBlock tm T cv) ↔
      tm.ReachesCfgLe (2 ^ n) cu cv :=
  ⟨fun h => reachPow_to_reaches x S hT n _ _ h cu cv (encBlock_encodeBlock cu) hwu hsu
      (encBlock_encodeBlock cv) hwv hsv,
    fun h => reaches_to_reachPow x S hT n cu cv h hall hwu hsu⟩

/-- **The clause-form data has the same reachability relation.** -/
theorem reachPowC_iff : ∀ (n : ℕ) (u v : Fin (configWidth tm T) → Bool),
    (cfgSavitchDataC tm T x S hT).ReachPow n u v ↔
      (cfgSavitchData tm T x S hT).ReachPow n u v
  | 0, u, v => by
      show ((cfgSavitchDataC tm T x S hT).Valid u ∧ (cfgSavitchDataC tm T x S hT).Valid v ∧
          ∃ σ, (cfgSavitchDataC tm T x S hT).Base u v σ) ↔
        ((cfgSavitchData tm T x S hT).Valid u ∧ (cfgSavitchData tm T x S hT).Valid v ∧
          ∃ σ, (cfgSavitchData tm T x S hT).Base u v σ)
      show (CfgValid tm T x S u ∧ CfgValid tm T x S v ∧ ∃ σ, CfgBaseC tm T x S u v σ) ↔
        (CfgValid tm T x S u ∧ CfgValid tm T x S v ∧ ∃ σ, CfgBase tm T x S u v σ)
      rw [exists_cfgBaseC_iff]
  | n + 1, u, v => by
      show (∃ m, (cfgSavitchDataC tm T x S hT).ReachPow n u m ∧
          (cfgSavitchDataC tm T x S hT).ReachPow n m v) ↔
        (∃ m, (cfgSavitchData tm T x S hT).ReachPow n u m ∧
          (cfgSavitchData tm T x S hT).ReachPow n m v)
      constructor
      · rintro ⟨m, h1, h2⟩
        exact ⟨m, (reachPowC_iff n u m).mp h1, (reachPowC_iff n m v).mp h2⟩
      · rintro ⟨m, h1, h2⟩
        exact ⟨m, (reachPowC_iff n u m).mpr h1, (reachPowC_iff n m v).mpr h2⟩

end

/-- **The acceptance predicate on a block is the machine's.** -/
theorem cfgAcc_encodeBlock (c : Cfg k tm.Q) :
    CfgAcc tm T (encodeBlock tm T c) ↔ (c.state = tm.qhalt ∧ c.output.cells 1 = Γ.one) := by
  rw [CfgAcc, encBlock_encodeBlock c (.state tm.qhalt),
    encBlock_encodeBlock c (.cell .output ⟨1, by omega⟩ Γ.one)]
  show (decide (c.state = tm.qhalt) = true ∧
    decide ((TapeSlot.output.get c).cells 1 = Γ.one) = true) ↔ _
  rw [decide_eq_true_iff, decide_eq_true_iff]
  rfl

end Complexity
