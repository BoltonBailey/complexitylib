/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.SavitchSim
public import Complexitylib.Classes.Containments.Internal.SavitchBound
public import Complexitylib.Classes.Containments.Internal.BinArith

/-!
# What Savitch's recursion computes

⚠️ Unreviewed by Bolton

`Complexity.Sav.rchB` and `Complexity.Sav.accB` are the values the abstract
machine returns, defined purely on bitstrings: a level-`n` reachability question
is answered by trying every string of the enumeration's width as a midpoint. This
file identifies them with reachability in the configuration graph, for as long as
the strings involved are codes of configurations reachable from the start.

The two directions are both easy once the statement is right. Soundness follows
because a midpoint that passes the first half is itself the code of a reachable
configuration, so the induction hypothesis applies to it; completeness follows
because the enumeration is *every* string of the code width, and a code has
exactly that width.

## Main results

- `Complexity.baseReachB_cfgCode`, `Complexity.baseAccB_cfgCode` — the base tests
- `Complexity.rchB_cfgCode`, `Complexity.accB_cfgCode` — the recursion
-/

@[expose] public section

namespace Complexity

open Cobham

variable {k : ℕ}

/-! ## The bottom of the enumeration -/

@[simp] theorem binValLE_savZero (k : ℕ) (R : List Bool) : binValLE (savZero k R) = 0 := by
  rw [savZero, padTo_nil, binValLE_replicate_false]

/-! ## The base tests as propositions -/

theorem baseReachB_eq_true_iff (tm : NTM k) (R u v : List Bool) :
    baseReachB tm R u v = true ↔
      u = v ∨ nstepFn tm false R u = v ∨ nstepFn tm true R u = v := by
  have hb : baseReachB tm R u v = true ↔ baseReach tm R u v = [true] := by
    rw [baseReach_eq]; simp
  rw [hb, baseReach,
    orBit_eq_true_iff (eqFlag_flag _ _) (orBit_flag (eqFlag_flag _ _) (eqFlag_flag _ _)),
    orBit_eq_true_iff (eqFlag_flag _ _) (eqFlag_flag _ _), eqFlag_eq_true_iff,
    eqFlag_eq_true_iff, eqFlag_eq_true_iff]

theorem baseAccB_eq_true_iff (tm : NTM k) (R rl u : List Bool) :
    baseAccB tm R rl u = true ↔
      acceptFlag (stateCode tm.qhalt) R rl u = [true] ∨
        acceptFlag (stateCode tm.qhalt) R rl (nstepFn tm false R u) = [true] ∨
        acceptFlag (stateCode tm.qhalt) R rl (nstepFn tm true R u) = [true] := by
  have hb : baseAccB tm R rl u = true ↔ baseAcc tm R rl u = [true] := by
    rw [baseAcc_eq]; simp
  rw [hb, baseAcc,
    orBit_eq_true_iff (acceptFlag_flag _ _ _ _)
      (orBit_flag (acceptFlag_flag _ _ _ _) (acceptFlag_flag _ _ _ _)),
    orBit_eq_true_iff (acceptFlag_flag _ _ _ _) (acceptFlag_flag _ _ _ _)]

/-! ## One step of the graph -/

namespace NTM

variable {tm : NTM k}

theorem eq_of_reachesCfgIn_of_halted {s : ℕ} {c c' : Cfg k tm.Q}
    (h : tm.ReachesCfgIn s c c') (hh : c.state = tm.qhalt) : c' = c := by
  cases h with
  | refl _ => rfl
  | head hstep _ => exact absurd hh hstep.1

theorem eq_of_reachesCfgLe_of_halted {t : ℕ} {c c' : Cfg k tm.Q}
    (h : tm.ReachesCfgLe t c c') (hh : c.state = tm.qhalt) : c' = c := by
  obtain ⟨s, _, hw⟩ := h
  exact eq_of_reachesCfgIn_of_halted hw hh

theorem reachesCfg_of_reachesCfgIn {s : ℕ} {c c' : Cfg k tm.Q}
    (h : tm.ReachesCfgIn s c c') : tm.ReachesCfg c c' := by
  induction h with
  | refl c => exact NTM.reachesCfg_refl tm c
  | head hstep _ ih => exact NTM.reachesCfg_head hstep ih

theorem reachesCfg_of_reachesCfgLe {t : ℕ} {c c' : Cfg k tm.Q}
    (h : tm.ReachesCfgLe t c c') : tm.ReachesCfg c c' := by
  obtain ⟨s, _, hw⟩ := h
  exact reachesCfg_of_reachesCfgIn hw

theorem reachesCfgLe_one_iff (tm : NTM k) (c c' : Cfg k tm.Q) :
    tm.ReachesCfgLe 1 c c' ↔ c' = c ∨ (c.state ≠ tm.qhalt ∧ ∃ b, c' = tm.stepCfg b c) := by
  constructor
  · rintro ⟨s, hs, hw⟩
    cases hw with
    | refl _ => exact Or.inl rfl
    | head hstep hrest =>
        cases hrest with
        | refl _ => exact Or.inr ⟨hstep.1, hstep.2⟩
        | head _ _ => omega
  · rintro (rfl | ⟨hne, b, rfl⟩)
    · exact ⟨0, by omega, NTM.ReachesCfgIn.refl _⟩
    · exact ⟨1, le_rfl, NTM.ReachesCfgIn.head ⟨hne, b, rfl⟩ (NTM.ReachesCfgIn.refl _)⟩

end NTM

/-! ## The recursion against the graph -/

section

variable (tm : NTM k) {L : Language} {S : ℕ → ℕ} (hdec : tm.DecidesInSpace L S)
  (x : List Bool) (W : ℕ) (hq : Fintype.card tm.Q ≤ blockWidth W)
  (hW : x.length + S x.length + 1 ≤ W)

include hdec hW hq in
theorem baseReachB_cfgCode {c : Cfg k tm.Q} (hc : tm.ReachesCfg (tm.initCfg x) c)
    (v : List Bool) :
    baseReachB tm (blockRuler W) (Cobham.cfgCode W c) v = true ↔
      ∃ c', tm.ReachesCfgLe 1 c c' ∧ v = Cobham.cfgCode W c' := by
  have hinv : CodeInv W c := codeInv_of_reachesCfg tm hdec x hc W hW
  rw [baseReachB_eq_true_iff]
  by_cases hh : c.state = tm.qhalt
  · rw [nstepFn_code_halted tm false W c hq hinv hh, nstepFn_code_halted tm true W c hq hinv hh]
    constructor
    · intro h
      exact ⟨c, NTM.reachesCfgLe_refl tm 1 c,
        by rcases h with h | h | h <;> exact h.symm⟩
    · rintro ⟨c', hle, rfl⟩
      exact Or.inl (by rw [NTM.eq_of_reachesCfgLe_of_halted hle hh])
  · rw [nstepFn_code tm false W c hq hinv hh, nstepFn_code tm true W c hq hinv hh]
    constructor
    · rintro (h | h | h)
      · exact ⟨c, NTM.reachesCfgLe_refl tm 1 c, h.symm⟩
      · exact ⟨tm.stepCfg false c,
          (NTM.reachesCfgLe_one_iff tm c _).mpr (Or.inr ⟨hh, false, rfl⟩), h.symm⟩
      · exact ⟨tm.stepCfg true c,
          (NTM.reachesCfgLe_one_iff tm c _).mpr (Or.inr ⟨hh, true, rfl⟩), h.symm⟩
    · rintro ⟨c', hle, rfl⟩
      rcases (NTM.reachesCfgLe_one_iff tm c c').mp hle with rfl | ⟨_, b, rfl⟩
      · exact Or.inl rfl
      · cases b
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)

include hdec hW hq in
theorem baseAccB_cfgCode {c : Cfg k tm.Q} (hc : tm.ReachesCfg (tm.initCfg x) c) :
    baseAccB tm (blockRuler W) (savRuler k (blockRuler W)) (Cobham.cfgCode W c) = true ↔
      ∃ c', tm.ReachesCfgLe 1 c c' ∧ c'.state = tm.qhalt ∧ c'.output.cells 1 = Γ.one := by
  have hW1 : 1 ≤ W := by omega
  have hruler : W ≤ (savRuler k (blockRuler W)).length := by
    rw [savRuler, wideRuler_length, blockRuler_length, blockWidth]
    have hcb : 1 ≤ codeBlocks k := by rw [codeBlocks]; omega
    calc W ≤ 1 * (2 * (W + 1)) := by omega
      _ ≤ codeBlocks k * (2 * (W + 1)) := Nat.mul_le_mul_right _ hcb
  have hflag : ∀ c'' : Cfg k tm.Q, tm.ReachesCfg (tm.initCfg x) c'' →
      (acceptFlag (stateCode tm.qhalt) (blockRuler W) (savRuler k (blockRuler W))
        (Cobham.cfgCode W c'') = [true] ↔
        c''.state = tm.qhalt ∧ c''.output.cells 1 = Γ.one) := fun c'' hc'' =>
    acceptFlag_cfgCode tm W c'' hq (codeInv_of_reachesCfg tm hdec x hc'' W hW) hW1 _ hruler
  have hinv : CodeInv W c := codeInv_of_reachesCfg tm hdec x hc W hW
  rw [baseAccB_eq_true_iff]
  by_cases hh : c.state = tm.qhalt
  · rw [nstepFn_code_halted tm false W c hq hinv hh, nstepFn_code_halted tm true W c hq hinv hh,
      hflag c hc]
    constructor
    · intro h
      exact ⟨c, NTM.reachesCfgLe_refl tm 1 c, by rcases h with h | h | h <;> exact h⟩
    · rintro ⟨c', hle, h1, h2⟩
      rw [NTM.eq_of_reachesCfgLe_of_halted hle hh] at h1 h2
      exact Or.inl ⟨h1, h2⟩
  · have hs : ∀ b : Bool, tm.ReachesCfg (tm.initCfg x) (tm.stepCfg b c) := fun b =>
      hc.trans (NTM.reachesCfg_of_reachesCfgLe
        ((NTM.reachesCfgLe_one_iff tm c _).mpr (Or.inr ⟨hh, b, rfl⟩)))
    rw [nstepFn_code tm false W c hq hinv hh, nstepFn_code tm true W c hq hinv hh,
      hflag c hc, hflag _ (hs false), hflag _ (hs true)]
    constructor
    · rintro (h | h | h)
      · exact ⟨c, NTM.reachesCfgLe_refl tm 1 c, h⟩
      · exact ⟨tm.stepCfg false c,
          (NTM.reachesCfgLe_one_iff tm c _).mpr (Or.inr ⟨hh, false, rfl⟩), h⟩
      · exact ⟨tm.stepCfg true c,
          (NTM.reachesCfgLe_one_iff tm c _).mpr (Or.inr ⟨hh, true, rfl⟩), h⟩
    · rintro ⟨c', hle, h1, h2⟩
      rcases (NTM.reachesCfgLe_one_iff tm c c').mp hle with rfl | ⟨_, b, rfl⟩
      · exact Or.inl ⟨h1, h2⟩
      · cases b
        · exact Or.inr (Or.inl ⟨h1, h2⟩)
        · exact Or.inr (Or.inr ⟨h1, h2⟩)

include hdec hW hq in
/-- **The recursion decides bounded reachability.** -/
theorem rchB_cfgCode :
    ∀ (n : ℕ) (c : Cfg k tm.Q), tm.ReachesCfg (tm.initCfg x) c → ∀ v : List Bool,
      Sav.rchB (baseReachB tm (blockRuler W)) (savZero k (blockRuler W)) n
          (Cobham.cfgCode W c) v = true ↔
        ∃ c', tm.ReachesCfgLe (2 ^ n) c c' ∧ v = Cobham.cfgCode W c' := by
  intro n
  induction n with
  | zero =>
      intro c hc v
      rw [Sav.rchB, pow_zero]
      exact baseReachB_cfgCode tm hdec x W hq hW hc v
  | succ n ih =>
      intro c hc v
      rw [Sav.rchB]
      constructor
      · intro h
        obtain ⟨i, _, hP⟩ := Sav.exists_of_anyMid h
        rw [Bool.and_eq_true] at hP
        obtain ⟨cm, hcm, hwm⟩ := (ih c hc _).mp hP.1
        have hcm' : tm.ReachesCfg (tm.initCfg x) cm :=
          hc.trans (NTM.reachesCfg_of_reachesCfgLe hcm)
        obtain ⟨c', hc', hv⟩ := (ih cm hcm' v).mp (by rw [← hwm]; exact hP.2)
        exact ⟨c', (NTM.reachesCfgLe_two_pow_succ_iff tm n c c').mpr ⟨cm, hcm, hc'⟩, hv⟩
      · rintro ⟨c', hle, rfl⟩
        obtain ⟨cm, h₁, h₂⟩ := (NTM.reachesCfgLe_two_pow_succ_iff tm n c c').mp hle
        have hcm' : tm.ReachesCfg (tm.initCfg x) cm :=
          hc.trans (NTM.reachesCfg_of_reachesCfgLe h₁)
        refine Sav.anyMid_of_length (w := Cobham.cfgCode W cm) (binValLE_savZero k _) ?_ ?_
        · rw [cfgCode_length, savZero_length]
        · rw [Bool.and_eq_true]
          exact ⟨(ih c hc _).mpr ⟨cm, h₁, rfl⟩, (ih cm hcm' _).mpr ⟨c', h₂, rfl⟩⟩

include hdec hW hq in
/-- **The recursion decides bounded acceptance.** -/
theorem accB_cfgCode :
    ∀ (n : ℕ) (c : Cfg k tm.Q), tm.ReachesCfg (tm.initCfg x) c →
      (Sav.accB (baseReachB tm (blockRuler W))
          (fun u => baseAccB tm (blockRuler W) (savRuler k (blockRuler W)) u)
          (savZero k (blockRuler W)) n (Cobham.cfgCode W c) = true ↔
        ∃ c', tm.ReachesCfgLe (2 ^ n) c c' ∧ c'.state = tm.qhalt ∧
          c'.output.cells 1 = Γ.one) := by
  intro n
  induction n with
  | zero =>
      intro c hc
      rw [Sav.accB, pow_zero]
      exact baseAccB_cfgCode tm hdec x W hq hW hc
  | succ n ih =>
      intro c hc
      rw [Sav.accB]
      constructor
      · intro h
        obtain ⟨i, _, hP⟩ := Sav.exists_of_anyMid h
        rw [Bool.and_eq_true] at hP
        obtain ⟨cm, hcm, hwm⟩ := (rchB_cfgCode tm hdec x W hq hW n c hc _).mp hP.1
        have hcm' : tm.ReachesCfg (tm.initCfg x) cm :=
          hc.trans (NTM.reachesCfg_of_reachesCfgLe hcm)
        obtain ⟨c', hc', h1, h2⟩ := (ih cm hcm').mp (by rw [← hwm]; exact hP.2)
        exact ⟨c', (NTM.reachesCfgLe_two_pow_succ_iff tm n c c').mpr ⟨cm, hcm, hc'⟩, h1, h2⟩
      · rintro ⟨c', hle, h1, h2⟩
        obtain ⟨cm, hm₁, hm₂⟩ := (NTM.reachesCfgLe_two_pow_succ_iff tm n c c').mp hle
        have hcm' : tm.ReachesCfg (tm.initCfg x) cm :=
          hc.trans (NTM.reachesCfg_of_reachesCfgLe hm₁)
        refine Sav.anyMid_of_length (w := Cobham.cfgCode W cm) (binValLE_savZero k _) ?_ ?_
        · rw [cfgCode_length, savZero_length]
        · rw [Bool.and_eq_true]
          exact ⟨(rchB_cfgCode tm hdec x W hq hW n c hc _).mpr ⟨cm, hm₁, rfl⟩,
            (ih cm hcm').mpr ⟨c', hm₂, h1, h2⟩⟩

end

end Complexity
