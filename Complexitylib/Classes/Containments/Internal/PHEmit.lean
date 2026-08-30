/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.PHLayout
public import Complexitylib.Models.TuringMachine.Placement.Hoare
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Retarget
public import Complexitylib.Models.TuringMachine.Hoare.RetargetOutput

/-!
# Building the pair the matrix machine reads

⚠️ Unreviewed by Bolton

`TM.pairInputWorkTM` emits `pair first second`, reading the first component off a work tape and
the second off its input tape. The enumerator needs `pair x w` with the witness second, so the
witness has to be what the emitter reads as an input — which `TM.retargetInput` arranges, since it
runs a machine with its input supplied on the last work tape. `TM.retargetOutput` then sends the
emitted pair to a work tape rather than the real output, which a loop body cannot write to.

The emitter's own contract says only that the pair appears; it says nothing about the tapes it
read. `PolyExists.pairFrame_hoareTime` restates its exact-execution theorem as the contract that
does: both sources come back with their cells intact and their heads left past the content, which
the rewind that follows the stage puts back.

## Main results

- `PolyExists.pairFrame_hoareTime` — the emitter's contract, framed
- `PolyExists.emitCore`, `PolyExists.emitTM` — the emitter as a stage of the enumerator
- `PolyExists.emitCore_hoareTime` — the stage's contract, on the three tapes it uses
- `PolyExists.emitTM`, `PolyExists.emitTM_hoareTime` — the same, placed in the layout
-/

@[expose] public section

namespace Complexity

namespace PolyExists

/-- **The pair emitter, framed.** Beyond the pair, this records what the sources look like when
the stage ends: their cells are untouched and the first component is still readable, its head
having been left past the content. -/
theorem pairFrame_hoareTime {n : ℕ} (firstIdx : Fin n) (first second : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀ = (Tape.init (second.map Γ.ofBool)).move Dir3.right)
    (hsourceHead : (work₀ firstIdx).head = 1)
    (hsourceOutput : (work₀ firstIdx).HasOutput first)
    (hwork : ∀ i, (work₀ i).StartInvariant ∧ 1 ≤ (work₀ i).head)
    (houtput : out₀ = (Tape.init []).move Dir3.right) :
    (TM.pairInputWorkTM firstIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp.cells = inp₀.cells ∧
        (work firstIdx).cells = (work₀ firstIdx).cells ∧
        (work firstIdx).HasOutput first ∧
        (∀ i, i ≠ firstIdx → work i = work₀ i) ∧
        out.HasBinaryPrefix (pair first second))
      (TM.pairInputWorkTime first second) := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  obtain ⟨c', hreach, hhalt, -, hinpc, -, hcells, hout, hother, hprefix⟩ :=
    TM.pairInputWorkTM_reachesIn firstIdx first second hinput hsourceHead hsourceOutput
      hwork houtput
  exact ⟨c', TM.pairInputWorkTime first second, le_refl _, hreach, hhalt, hinpc, hcells, hout,
    hother, hprefix⟩

/-- The emitter as a three-tape machine: the input copy, the witness it reads as an input, and
the tape the pair is written to. -/
def emitCore : TM 3 := (TM.retargetInput (TM.pairInputWorkTM (0 : Fin 1))).retargetOutput

/-- **The emitter stage's contract.** Started with the input copy rewound, the witness in
virtual-input shape, and the target tape blank, it leaves the pair on the target tape and both
sources with their cells intact. -/
theorem emitCore_hoareTime (x w : List Bool) (X : Tape)
    (hXhead : X.head = 1) (hXout : X.HasOutput x) (hXSI : Tape.StartInvariant X) :
    emitCore.HoareTime
      (fun _inp work out => work 0 = X ∧
        work 1 = (Tape.init (w.map Γ.ofBool)).move Dir3.right ∧
        work 2 = TM.parkedBlank ∧ out = TM.parkedBlank)
      (fun _inp work out => (work 0).cells = X.cells ∧ (work 0).HasOutput x ∧
        (work 1).cells = ((Tape.init (w.map Γ.ofBool)).move Dir3.right).cells ∧
        (work 2).HasBinaryPrefix (pair x w) ∧ out = TM.parkedBlank)
      (TM.pairInputWorkTime x w) := by
  set W : Tape := (Tape.init (w.map Γ.ofBool)).move Dir3.right with hWdef
  have hWSI : Tape.StartInvariant W := (TM.startInvariant_initOfBool w).move Dir3.right
  have hWhead : 1 ≤ W.head := by rw [hWdef]; exact le_of_eq rfl
  have hsource := pairFrame_hoareTime (0 : Fin 1) x w W (fun _ => X) TM.parkedBlank rfl
    hXhead hXout (fun _ => ⟨hXSI, le_of_eq hXhead.symm⟩) rfl
  have hretarget := TM.retargetInput_hoareTime (TM.pairInputWorkTM (0 : Fin 1)) hsource
    (fun inp _ _ hpre => by rw [hpre.1]; exact hWSI)
    (fun _ _ _ hpre i => by rw [hpre.2.1]; exact hXSI)
    (fun _ _ _ hpre => by
      rw [hpre.2.2]
      exact (TM.startInvariant_initNil).move Dir3.right)
  have hout := TM.retargetOutput_hoareTime _ hretarget
  rintro inp work out ⟨h0, h1, h2, ho⟩
  have hfun : (fun i : Fin 1 => work (Fin.castSucc (⟨i.val, by omega⟩ : Fin 2)))
      = fun _ : Fin 1 => X := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    rw [hi]
    exact h0
  obtain ⟨c', t, ht, hreach, hhalt, hpost, houtEq⟩ :=
    hout inp work out ⟨⟨h1, hfun, h2⟩, ho⟩
  obtain ⟨vin, innerWork, hpostSrc, hinner, hvin⟩ := hpost
  have h00 : c'.work 0 = innerWork 0 := hinner 0
  have h11 : c'.work 1 = vin := hvin
  refine ⟨c', t, ht, hreach, hhalt, ?_, ?_, ?_, ?_, houtEq⟩
  · rw [h00]
    exact hpostSrc.2.1
  · rw [h00]
    exact hpostSrc.2.2.1
  · rw [h11]
    exact hpostSrc.1
  · exact hpostSrc.2.2.2.2

/-- The emitter placed in the enumerator's layout: it uses the first three tapes, which is where
the input copy, the witness, and the pair sit. -/
def emitTM (k : ℕ) : TM (enumTapes k) := TM.placeWorkTM 0 (k + 9) emitCore

theorem placeWorkIdx_zero (k : ℕ) : TM.placeWorkIdx (n := 3) 0 (k + 9) 0 = xIdx k := by
  apply Fin.ext
  show 0 + 0 = 0
  omega

theorem placeWorkIdx_one (k : ℕ) : TM.placeWorkIdx (n := 3) 0 (k + 9) 1 = wIdx k := by
  apply Fin.ext
  show 0 + 1 = 1
  omega

theorem placeWorkIdx_two (k : ℕ) : TM.placeWorkIdx (n := 3) 0 (k + 9) 2 = y1Idx k := by
  apply Fin.ext
  show 0 + 2 = 2
  omega

/-- A tape of the layout is outside the emitter's block exactly when its index is at least
three. -/
theorem not_inMiddle_iff (k : ℕ) (i : Fin (enumTapes k)) :
    ¬ TM.placeWorkInMiddle (post := k + 9) 0 3 i ↔ 3 ≤ i.val := by
  constructor
  · intro h
    by_contra hlt
    exact h ⟨Nat.zero_le _, by omega⟩
  · rintro h ⟨-, hlt⟩
    omega

/-- **The placed emitter's contract.** The three tapes it uses come back as
`PolyExists.emitCore_hoareTime` describes them; every other tape of the layout is untouched. -/
theorem emitTM_hoareTime (k : ℕ) (x w : List Bool) (X : Tape)
    (hXhead : X.head = 1) (hXout : X.HasOutput x) (hXSI : Tape.StartInvariant X)
    (extras : Fin (enumTapes k) → Tape)
    (hinv : ∀ i, ¬ TM.placeWorkInMiddle (post := k + 9) 0 3 i → Tape.StartInvariant (extras i))
    (hhead : ∀ i, ¬ TM.placeWorkInMiddle (post := k + 9) 0 3 i → 1 ≤ (extras i).head) :
    (emitTM k).HoareTime
      (fun _inp work out =>
        (∀ i, ¬ TM.placeWorkInMiddle (post := k + 9) 0 3 i → work i = extras i) ∧
        work (xIdx k) = X ∧
        work (wIdx k) = (Tape.init (w.map Γ.ofBool)).move Dir3.right ∧
        work (y1Idx k) = TM.parkedBlank ∧ out = TM.parkedBlank)
      (fun _inp work out =>
        (∀ i, ¬ TM.placeWorkInMiddle (post := k + 9) 0 3 i → work i = extras i) ∧
        (work (xIdx k)).cells = X.cells ∧ (work (xIdx k)).HasOutput x ∧
        (work (wIdx k)).cells = ((Tape.init (w.map Γ.ofBool)).move Dir3.right).cells ∧
        (work (y1Idx k)).HasBinaryPrefix (pair x w) ∧ out = TM.parkedBlank)
      (TM.pairInputWorkTime x w) := by
  have h := TM.placeWorkTM_hoareTime emitCore (emitCore_hoareTime x w X hXhead hXout hXSI)
    0 (k + 9) extras hinv hhead
  rintro inp work out ⟨hframe, hX, hW, hY, ho⟩
  obtain ⟨c', t, ht, hreach, hhalt, hframe', hpost⟩ :=
    h inp work out ⟨hframe,
      by show work (TM.placeWorkIdx (n := 3) 0 (k + 9) 0) = X
         rw [placeWorkIdx_zero k]; exact hX,
      by show work (TM.placeWorkIdx (n := 3) 0 (k + 9) 1)
             = (Tape.init (w.map Γ.ofBool)).move Dir3.right
         rw [placeWorkIdx_one k]; exact hW,
      by show work (TM.placeWorkIdx (n := 3) 0 (k + 9) 2) = TM.parkedBlank
         rw [placeWorkIdx_two k]; exact hY, ho⟩
  exact ⟨c', t, ht, hreach, hhalt, hframe',
    by rw [← placeWorkIdx_zero k]; exact hpost.1,
    by rw [← placeWorkIdx_zero k]; exact hpost.2.1,
    by rw [← placeWorkIdx_one k]; exact hpost.2.2.1,
    by rw [← placeWorkIdx_two k]; exact hpost.2.2.2.1, hpost.2.2.2.2⟩

end PolyExists

end Complexity
