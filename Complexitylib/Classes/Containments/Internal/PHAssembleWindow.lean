/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.PHAssemble
public import Complexitylib.Classes.Containments.Internal.PHLoopWindow

/-!
# The whole enumerator, in space

⚠️ Unreviewed by Bolton

Five of the machine's six phases are short, and their windows come from their running times; the
sixth is the counting loop, whose window is one iteration wide. Composing them is what
`TM.seqTM_keepsWindowOn` is for.

## Main results

- `PolyExists.afterCopyX_heads` — how far the copy phase can leave a head
- `PolyExists.enumPark_keepsWindowOn` and the other per-phase windows
-/

@[expose] public section

namespace Complexity

namespace PolyExists

variable {k : ℕ}

/-- The copy phase leaves every head inside the input's width. -/
theorem afterCopyX_heads (k : ℕ) (x : List Bool) (inp : Tape)
    (work : Fin (enumTapes k) → Tape) (out : Tape) (h : afterCopyX k x inp work out) :
    ∀ i, (work i).head ≤ x.length + 1 := by
  intro i
  by_cases hi : i = xIdx k
  · rw [hi, h.2.2.2.1.1]
  · rw [h.2.2.1 i hi]
    show (1 : ℕ) ≤ x.length + 1
    omega

theorem copiedBank_head (k : ℕ) (x : List Bool) (i : Fin (enumTapes k)) :
    (copiedBank k x i).head = 1 := by
  rw [copiedBank]
  by_cases h : i = xIdx k
  · rw [h, Function.update_self]
    exact strTape_head x
  · rw [Function.update_of_ne h]
    rfl

/-- The parking phase's window. -/
theorem enumPark_keepsWindowOn (k : ℕ) (x : List Bool) (W : ℕ) (hW : 1 ≤ W) :
    (TM.skipTM (n := enumTapes k)).KeepsWindowOn
      (fun c => c.state = (TM.skipTM (n := enumTapes k)).qstart ∧
        (c.input = Tape.init (x.map Γ.ofBool) ∧
          c.work = (fun _ => Tape.init ([] : List Γ)) ∧ c.output = Tape.init ([] : List Γ)))
      x.length W :=
  (TM.keepsWindowOn_of_hoareTime (h₀ := 0) (enumPark_hoareTime k x)
    (fun inp work out hpre i => by rw [hpre.2.1]; exact le_of_eq rfl)
    (fun inp work out hpre => by rw [hpre.1]; show (0 : ℕ) ≤ x.length + 0 + 1; omega)
    (fun inp work out hpre => by rw [hpre.2.2]; show (0 : ℕ) ≤ 0 + 1; omega)).mono_space hW

/-- The input copy's window. -/
theorem copyX_keepsWindowOn (k : ℕ) (x : List Bool) (W : ℕ) (hW : 1 + (x.length + 1) ≤ W) :
    (TM.copyInputToWorkTM (xIdx k)).KeepsWindowOn
      (fun c => c.state = (TM.copyInputToWorkTM (xIdx k)).qstart ∧
        (c.input = strTape x ∧ c.work = (fun _ => TM.blankTape) ∧ c.output = TM.blankTape))
      x.length W :=
  (TM.keepsWindowOn_of_hoareTime (h₀ := 1) (copyX_hoareTime k x)
    (fun inp work out hpre i => by rw [hpre.2.1]; exact le_of_eq rfl)
    (fun inp work out hpre => by rw [hpre.1]; show (1 : ℕ) ≤ x.length + 1 + 1; omega)
    (fun inp work out hpre => by
      rw [hpre.2.2]
      show (1 : ℕ) ≤ 1 + 1
      omega)).mono_space hW

/-- The rewind's window. -/
theorem rewindX_keepsWindowOn (k : ℕ) (x : List Bool) (B W : ℕ) (hB : x.length + 1 ≤ B)
    (hW : (x.length + 1) + (1 + 1 + (2 * (max (B + 2) (1 * (B + 3) + 1) + 1) + 1)) ≤ W) :
    (TM.parkRewindTM [xIdx k]).KeepsWindowOn
      (fun c => c.state = (TM.parkRewindTM [xIdx k]).qstart ∧
        afterCopyX k x c.input c.work c.output)
      x.length W :=
  (TM.keepsWindowOn_of_hoareTime (h₀ := x.length + 1) (rewindX_hoareTime k x B hB)
    (fun inp work out hpre i => afterCopyX_heads k x inp work out hpre i)
    (fun inp work out hpre => by rw [hpre.2.1]; omega)
    (fun inp work out hpre => by
      rw [hpre.2.2.2.2.2]
      show (1 : ℕ) ≤ x.length + 1 + 1
      omega)).mono_space hW

/-- The prologue's window. -/
theorem prologue_keepsWindowOn (k : ℕ) (p q : Polynomial ℕ) (x : List Bool) (W : ℕ)
    (hW : 1 + prologueTime p q x.length ≤ W) :
    (prologueTM k p q).KeepsWindowOn
      (fun c => c.state = (prologueTM k p q).qstart ∧
        (c.input = strTape x ∧ c.work = copiedBank k x ∧ c.output = TM.blankTape))
      x.length W :=
  (TM.keepsWindowOn_of_hoareTime (h₀ := 1) (prologueTM_hoareTime k p q x)
    (fun inp work out hpre i => by
      rw [hpre.2.1, copiedBank_head])
    (fun inp work out hpre => by rw [hpre.1]; show (1 : ℕ) ≤ x.length + 1 + 1; omega)
    (fun inp work out hpre => by
      rw [hpre.2.2]
      show (1 : ℕ) ≤ 1 + 1
      omega)).mono_space hW

/-- The epilogue's window. -/
theorem epilogue_keepsWindowOn (k : ℕ) (x : List Bool) (N H A R : ℕ) (I : Tape)
    (hI : TM.Parked I) (hIsi : Tape.StartInvariant I) (hIhead : I.head = 1) (W : ℕ)
    (hW : 1 + epilogueTime A ≤ W) :
    (epilogueTM k).KeepsWindowOn
      (fun c => c.state = (epilogueTM k).qstart ∧
        (c.input = I ∧ c.work = enumBank k x N H N A R ∧ c.output = NTM.outSlot Γw.one))
      x.length W :=
  (TM.keepsWindowOn_of_hoareTime (h₀ := 1) (epilogueTM_hoareTime k x N H A R I hI hIsi)
    (fun inp work out hpre i => by rw [hpre.2.1, enumBank_head])
    (fun inp work out hpre => by rw [hpre.1, hIhead]; omega)
    (fun inp work out hpre => by
      rw [hpre.2.2]
      show (1 : ℕ) ≤ 1 + 1
      omega)).mono_space hW

/-- **The whole machine keeps a window.** Five short phases, whose windows come from their
running times, and one long loop, whose window is one iteration wide. -/
theorem enumTM_keepsWindowOn (M : TM k) {L' : Language} (p q : Polynomial ℕ) (x : List Bool)
    (N H A R : ℕ) (W : ℕ)
    (hloopW : (TM.loopTM (bodyTM M) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).KeepsWindowOn
      (fun c => c.state =
          (TM.loopTM (bodyTM M) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).qstart ∧
        NTM.tallyPre (cIdx k) (aIdx k) (rIdx k) (strTape x) (enumRest k x N H 1)
          (enumP L' x) 0 c.input c.work c.output) x.length W)
    {bnd : ℕ}
    (hloopC : (TM.loopTM (bodyTM M) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).HoareTime
      (NTM.tallyPre (cIdx k) (aIdx k) (rIdx k) (strTape x) (enumRest k x N H 1) (enumP L' x) 0)
      (fun inp work out => inp = strTape x ∧ work = enumBank k x N H N A R ∧
        out = NTM.outSlot Γw.one) bnd)
    (hprologuePost : (prologueTM k p q).HoareTime
      (fun inp work out => inp = strTape x ∧ work = copiedBank k x ∧ out = TM.blankTape)
      (fun inp work out => inp = strTape x ∧ work = enumBank k x N H 0 0 0 ∧
        out = TM.blankTape) (prologueTime p q x.length))
    (B : ℕ) (hBx : x.length + 1 ≤ B)
    (hWpark : 1 ≤ W) (hWcopy : 1 + (x.length + 1) ≤ W)
    (hWrewind : (x.length + 1) + (1 + 1 + (2 * (max (B + 2) (1 * (B + 3) + 1) + 1) + 1)) ≤ W)
    (hWprol : 1 + prologueTime p q x.length ≤ W)
    (hWepi : 1 + epilogueTime A ≤ W) :
    ∀ c, (enumTM M p q).reaches ((enumTM M p q).initCfg x) c →
      c.WithinDecisionSpace x.length W := by
  set I : Tape := strTape x with hIdef
  have hI : TM.Parked I := strTape_parked x
  have hIsi : Tape.StartInvariant I := strTape_startInvariant x
  have hIhead : I.head = 1 := rfl
  have hs : 1 ≤ W := hWpark
  have hpinnedPre : ∀ {Q : Type} (c : Cfg (enumTapes k) Q) (qs : Q)
      (W' : Fin (enumTapes k) → Tape) (O : Tape), (∀ i, (W' i).head = 1) →
      (∀ i, Tape.StartInvariant (W' i)) → O.head = 1 → Tape.StartInvariant O →
      c.state = qs → c.input = I → c.work = W' → c.output = O →
      c.state = qs ∧ c.WithinDecisionSpace x.length W ∧ TM.CfgStartInvariant c := by
    intro Q c qs W' O hW'h hW'si hOh hOsi hst hi hw ho
    refine ⟨hst, ⟨⟨fun i => ?_, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
    · rw [hw, hW'h i]; omega
    · rw [hi, hIhead]; omega
    · rw [ho, hOh]; omega
    · rw [hi]; exact hIsi
    · intro i; rw [hw]; exact hW'si i
    · rw [ho]; exact hOsi
  -- the epilogue
  have w6 := epilogue_keepsWindowOn k x N H A R I hI hIsi hIhead W hWepi
  -- loop and epilogue
  have c56 := TM.seqTM_keepsWindowOn
    (TM.loopTM (bodyTM M) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))) (epilogueTM k) hs
    (mid := fun inp work out => inp = I ∧ work = enumBank k x N H N A R ∧
      out = NTM.outSlot Γw.one)
    (fun c hc => by
      obtain ⟨hi, hw, sy, -, ho⟩ := hc.2
      exact hpinnedPre c _ (enumBank k x N H 0 0 0) (NTM.outSlot sy)
        (fun i => enumBank_head k x N H 0 0 0 i)
        (fun i => enumBank_startInvariant k x N H 0 0 0 i) rfl
        ⟨rfl, fun j hj => (NTM.outSlot_parked sy).2 j hj⟩ hc.1 hi hw ho)
    hloopW
    (fun c hc => hoare_post_of hloopC c hc.1 hc.2)
    w6
    (fun inp work out h =>
      ⟨rfl, by
          show TM.transitionInput inp = I
          rw [h.1]
          exact TM.transitionInput_eq_self hI.read_ne_start,
        by
          show (fun i => TM.transitionTape (work i)) = enumBank k x N H N A R
          rw [h.2.1]
          exact funext fun i => TM.transitionTape_eq_self
            (enumBank_parked k x N H N A R i).read_ne_start,
        by
          show TM.transitionTape out = NTM.outSlot Γw.one
          rw [h.2.2]
          exact TM.transitionTape_eq_self (NTM.outSlot_parked _).read_ne_start⟩)
  -- prologue
  have c46 := TM.seqTM_keepsWindowOn (prologueTM k p q) _ hs
    (mid := fun inp work out => inp = I ∧ work = enumBank k x N H 0 0 0 ∧ out = TM.blankTape)
    (fun c hc => by
      obtain ⟨hi, hw, ho⟩ := hc.2
      exact hpinnedPre c _ (copiedBank k x) TM.blankTape (copiedBank_head k x)
        (fun i => by
          rw [copiedBank]
          by_cases hix : i = xIdx k
          · rw [hix, Function.update_self]
            exact strTape_startInvariant x
          · rw [Function.update_of_ne hix]
            exact TM.blankTape_startInvariant) rfl TM.blankTape_startInvariant hc.1 hi hw ho)
    (prologue_keepsWindowOn k p q x W hWprol)
    (fun c hc => hoare_post_of hprologuePost c hc.1 hc.2)
    c56
    (fun inp work out h => ⟨⟨(TM.loopTM (bodyTM M)
        (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).qstart, TM.transitionInput inp,
        fun i => TM.transitionTape (work i), TM.transitionTape out⟩,
      ⟨rfl, by rw [h.1]; exact TM.transitionInput_eq_self hI.read_ne_start,
        by
          rw [h.2.1]
          exact funext fun i => TM.transitionTape_eq_self
            (enumBank_parked k x N H 0 0 0 i).read_ne_start,
        ⟨Γw.blank, by decide, by
          rw [h.2.2, TM.transitionTape_eq_self TM.blankTape_parked.read_ne_start]
          exact NTM.outSlot_blank_eq_blankTape.symm⟩⟩, rfl⟩)
  -- rewind
  have c36 := TM.seqTM_keepsWindowOn (TM.parkRewindTM [xIdx k]) _ hs
    (mid := fun inp work out => inp = I ∧ work = copiedBank k x ∧ out = TM.blankTape)
    (fun c hc => by
      obtain ⟨hIp', hwP', hoP'⟩ := afterCopyX_parked k x hc.2
      refine ⟨hc.1, ⟨⟨fun i => le_trans (afterCopyX_heads k x _ _ _ hc.2 i) (by omega),
        by rw [hc.2.2.1]; omega⟩, ?_⟩, ?_, ?_, ?_⟩
      · rw [hc.2.2.2.2.2.2]
        show (1 : ℕ) ≤ W + 1
        omega
      · exact ⟨by rw [hc.2.1]; exact (strTape_startInvariant x).1,
          fun j hj => hIp'.2 j hj⟩
      · intro i
        by_cases hix : i = xIdx k
        · rw [hix]
          exact ⟨hc.2.2.2.2.2.1, fun j hj => (hwP' (xIdx k)).2 j hj⟩
        · rw [hc.2.2.2.1 i hix]
          exact TM.blankTape_startInvariant
      · rw [hc.2.2.2.2.2.2]
        exact TM.blankTape_startInvariant)
    (rewindX_keepsWindowOn k x B W hBx hWrewind)
    (fun c hc => hoare_post_of (rewindX_hoareTime k x B hBx) c hc.1 hc.2)
    c46
    (fun inp work out h => ⟨⟨(prologueTM k p q).qstart, TM.transitionInput inp,
        fun i => TM.transitionTape (work i), TM.transitionTape out⟩,
      ⟨rfl, by rw [h.1]; exact TM.transitionInput_eq_self hI.read_ne_start,
        by
          rw [h.2.1]
          exact funext fun i => TM.transitionTape_eq_self (copiedBank_parked k x i).read_ne_start,
        by
          rw [h.2.2]
          exact TM.transitionTape_eq_self TM.blankTape_parked.read_ne_start⟩, rfl⟩)
  -- copy
  have c26 := TM.seqTM_keepsWindowOn (TM.copyInputToWorkTM (xIdx k)) _ hs
    (mid := afterCopyX k x)
    (fun c hc => by
      obtain ⟨hi, hw, ho⟩ := hc.2
      exact hpinnedPre c _ (fun _ => TM.blankTape) TM.blankTape (fun _ => rfl)
        (fun _ => TM.blankTape_startInvariant) rfl TM.blankTape_startInvariant hc.1 hi hw ho)
    (copyX_keepsWindowOn k x W hWcopy)
    (fun c hc => hoare_post_of (copyX_hoareTime k x) c hc.1 hc.2)
    c36
    (fun inp work out h => ⟨⟨(TM.parkRewindTM [xIdx k]).qstart, TM.transitionInput inp,
        fun i => TM.transitionTape (work i), TM.transitionTape out⟩,
      ⟨rfl, afterCopyX_trans k x inp work out h⟩, rfl⟩)
  -- park
  have c16 := TM.seqTM_keepsWindowOn (TM.skipTM (n := enumTapes k)) _ hs
    (mid := fun inp work out => inp = I ∧ work = (fun _ => TM.blankTape) ∧ out = TM.blankTape)
    (fun c hc => by
      obtain ⟨hi, hw, ho⟩ := hc.2
      refine ⟨hc.1, ⟨⟨fun i => by rw [hw]; show (0 : ℕ) ≤ W; omega,
        by rw [hi]; show (0 : ℕ) ≤ x.length + W + 1; omega⟩, ?_⟩, ?_, ?_, ?_⟩
      · rw [ho]
        show (0 : ℕ) ≤ W + 1
        omega
      · rw [hi]
        exact Tape.StartInvariant.init_ofBool x
      · intro i
        rw [hw]
        exact Tape.StartInvariant.init_nil
      · rw [ho]
        exact Tape.StartInvariant.init_nil)
    (enumPark_keepsWindowOn k x W hWpark)
    (fun c hc => hoare_post_of (enumPark_hoareTime k x) c hc.1 hc.2)
    c26
    (fun inp work out h => ⟨⟨(TM.copyInputToWorkTM (xIdx k)).qstart, TM.transitionInput inp,
        fun i => TM.transitionTape (work i), TM.transitionTape out⟩,
      ⟨rfl, by rw [h.1]; exact TM.transitionInput_eq_self hI.read_ne_start,
        by
          rw [h.2.1]
          exact funext fun i => TM.transitionTape_eq_self TM.blankTape_parked.read_ne_start,
        by
          rw [h.2.2]
          exact TM.transitionTape_eq_self TM.blankTape_parked.read_ne_start⟩, rfl⟩)
  intro c hD
  exact c16 _ ⟨⟨(TM.skipTM (n := enumTapes k)).qstart, Tape.init (x.map Γ.ofBool),
    fun _ => Tape.init ([] : List Γ), Tape.init ([] : List Γ)⟩, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ c hD

end PolyExists

end Complexity
