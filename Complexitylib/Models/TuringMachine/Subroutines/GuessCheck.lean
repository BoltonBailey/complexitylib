/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.GuessAssembly
public import Complexitylib.Models.TuringMachine.Subroutines.Scan
public import Complexitylib.Models.TuringMachine.Subroutines.InputMatch

/-!
# Guess a block of registers, then check them

⚠️ Unreviewed by Bolton

A nondeterministic construction that works on registers has the same shape wherever it appears:
guess a block of tapes, run a scan over them, and conjoin the scan's verdict into an accumulator
that no guess can reach. `Complexity.TM.guessCheckTM` is that shape, parameterized by the
scanner — so a new check needs only a new `Complexity.Scanner`, not a new machine.

The accumulator only ever loses its one, which is what makes a single failed check final in a
loop that has no way to stop early.

## Main definitions

- `TM.guessCheckTM` — guess, scan, and record
- `TM.guessCheckAdv` — its advancing states

## Main results

- `TM.guessCheckTM_hoareTime` — what one stage leaves on the tapes
- `TM.guessProtocol_guessCheckTM` — a stage consumes its guesses in order
-/

@[expose] public section

namespace Complexity

namespace TM

variable {jj : ℕ}

/-- **One guess-and-check stage, with the check left open.** Guess the registers named by
`guessReg`, run `D` on them, and conjoin the verdict it leaves on the result register into
`accIdx`. -/
noncomputable def guessThenCheckTM (r : ℕ) (D : TM (jj + 2))
    (guessReg : ℕ → Fin (jj + 2 + r + 1)) (w : ℕ → ℕ) (t : ℕ)
    (targets : List (Fin (jj + 2 + r))) (accIdx : Fin (jj + 2 + r + 1)) :
    TM (jj + 2 + r + 1) :=
  seqTM (guessStageTM guessReg w t targets)
    (seqTM (liftLast (liftMany D r))
      (andCellTM (Fin.castAdd r (Fin.last (jj + 1))).castSucc accIdx))

/-- **One guess-and-check stage.** Guess the registers named by `guessReg`, scan them with `S`,
and conjoin the verdict into `accIdx`. -/
noncomputable def guessCheckTM (r : ℕ) (S : Scanner jj)
    (guessReg : ℕ → Fin (jj + 2 + r + 1)) (w : ℕ → ℕ) (t : ℕ)
    (targets : List (Fin (jj + 2 + r))) (accIdx : Fin (jj + 2 + r + 1)) :
    TM (jj + 2 + r + 1) :=
  guessThenCheckTM r (twoPassTM S) guessReg w t targets accIdx

/-- Its advancing states: the guess stage's, and then none. -/
noncomputable def guessThenCheckAdv (r : ℕ) (D : TM (jj + 2))
    (guessReg : ℕ → Fin (jj + 2 + r + 1)) (w : ℕ → ℕ) (t : ℕ)
    (targets : List (Fin (jj + 2 + r))) (accIdx : Fin (jj + 2 + r + 1)) :
    (guessThenCheckTM r D guessReg w t targets accIdx).Q → Bool :=
  seqAdv (seqAdv (guessBlocksAdv guessReg w t) (fun _ => false))
    (seqAdv (fun _ => false) (fun _ => false))

/-- **A guess-and-check stage respects the guess protocol**, so it may sit inside a
nondeterministic assembly. -/
theorem guessProtocol_guessThenCheckTM (r : ℕ) (D : TM (jj + 2))
    (guessReg : ℕ → Fin (jj + 2 + r + 1)) (w : ℕ → ℕ) (t : ℕ)
    (targets : List (Fin (jj + 2 + r))) (accIdx : Fin (jj + 2 + r + 1))
    (hacc : accIdx ≠ Fin.last (jj + 2 + r)) :
    GuessProtocol (guessThenCheckTM r D guessReg w t targets accIdx)
      (guessThenCheckAdv r D guessReg w t targets accIdx) :=
  guessProtocol_seqTM (guessProtocol_guessStageTM guessReg w t targets)
    (guessProtocol_seqTM (guessProtocol_liftLast _)
      (guessProtocol_andCellTM _ _ (Fin.castSucc_lt_last _).ne hacc))

/-- **The contract of a guess-and-check stage, with the check left open.** The guessed tapes are
named by `Complexity.TM.guessBlocksTapes`; what they contain is the caller's business, and the
verdict the check leaves on the result register is what the accumulator records. -/
theorem guessThenCheck_hoareTime (r : ℕ) (D : TM (jj + 2))
    (guessReg : ℕ → Fin (jj + 2 + r + 1)) (w : ℕ → ℕ) (t : ℕ)
    (targets : List (Fin (jj + 2 + r))) (accIdx : Fin (jj + 2 + r + 1)) (hnodup : targets.Nodup)
    (hall : ∀ i : Fin (jj + 2), Fin.castAdd r i ∈ targets)
    (haux : ∀ c : Fin r, Fin.natAdd (jj + 2) c ∉ targets)
    (hauxG : ∀ p c, p < t → guessReg p ≠ (Fin.natAdd (jj + 2) c).castSucc)
    (haccReg : ∀ i : Fin (jj + 2), accIdx ≠ (Fin.castAdd r i).castSucc)
    (haccLast : accIdx ≠ Fin.last (jj + 2 + r))
    (hj : ∀ p, guessReg p ≠ Fin.last (jj + 2 + r)) (B : ℕ) (hB : 1 ≤ B)
    (inp₀ out₀ : Tape) (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (hinpSI : inp₀.StartInvariant) (houtSI : out₀.StartInvariant)
    (hinp : inp₀.read ≠ Γ.start) (hout : out₀.read ≠ Γ.start)
    (hinvW : ∀ i, (W₀ i).StartInvariant) (hhW : ∀ i, 1 ≤ (W₀ i).head)
    (hinj : ∀ p q, p < t → q < t → guessReg p = guessReg q → p = q)
    (hbound : ∀ i, i ∈ targets → (guessBlocksTapes guessReg w t W₀ i.castSucc).head ≤ B)
    (cells' : Fin (jj + 1) → ℕ → Γ) (v : Bool) (bD : ℕ)
    (hcells' : ∀ i : Fin (jj + 1), (⟨1, cells' i⟩ : Tape).StartInvariant)
    (hD : D.HoareTime
      (fun inp work out => inp = parkTape inp₀ ∧ out = parkTape out₀ ∧
        work = Fin.snoc (fun i : Fin (jj + 1) => (⟨1, (guessBlocksTapes guessReg w t W₀
            (Fin.castAdd r i.castSucc).castSucc).cells⟩ : Tape))
          (⟨1, (guessBlocksTapes guessReg w t W₀
            (Fin.castAdd r (Fin.last (jj + 1))).castSucc).cells⟩ : Tape))
      (fun inp work out => inp = parkTape inp₀ ∧ out = parkTape out₀ ∧
        work = Fin.snoc (fun i : Fin (jj + 1) => (⟨1, cells' i⟩ : Tape))
          ((⟨1, (guessBlocksTapes guessReg w t W₀
            (Fin.castAdd r (Fin.last (jj + 1))).castSucc).cells⟩ : Tape).write (Γ.ofBool v)))
      bD) :
    (guessThenCheckTM r D guessReg w t targets accIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧ work = W₀)
      (fun inp work out =>
        work (Fin.last (jj + 2 + r)) = guessBlocksTapes guessReg w t W₀ (Fin.last (jj + 2 + r)) ∧
        (∀ c : Fin r, (Fin.natAdd (jj + 2) c).castSucc ≠ accIdx →
          work (Fin.natAdd (jj + 2) c).castSucc = W₀ (Fin.natAdd (jj + 2) c).castSucc) ∧
        inp = parkTape inp₀ ∧ out = parkTape out₀ ∧
        (∀ i : Fin (jj + 2), work (Fin.castAdd r i).castSucc =
          (Fin.snoc (fun i : Fin (jj + 1) => (⟨1, cells' i⟩ : Tape))
          ((⟨1, (guessBlocksTapes guessReg w t W₀
              (Fin.castAdd r (Fin.last (jj + 1))).castSucc).cells⟩ : Tape).write
            (Γ.ofBool v)) : Fin (jj + 2) → Tape) i) ∧
        work accIdx = ⟨(W₀ accIdx).head, Function.update (W₀ accIdx).cells (W₀ accIdx).head
          (if v = true ∧ (W₀ accIdx).read = Γ.one then Γ.one else Γ.zero)⟩)
      (guessBlocksTime w t + 1 + (1 + 1 + (targets.length * (B + 3) + 1)) + 1 +
        (bD + 1 + 1)) := by
  classical
  set G := guessBlocksTapes guessReg w t W₀ with hG
  set cells : Fin (jj + 1) → ℕ → Γ :=
    fun i => (G (Fin.castAdd r i.castSucc).castSucc).cells with hcells
  set resT : Tape := ⟨1, (G (Fin.castAdd r (Fin.last (jj + 1))).castSucc).cells⟩ with hresT
  obtain ⟨ginv, ghh, -, -, -⟩ := guessBlocksTapes_spec guessReg hj w t W₀ hinvW hhW hinj
  have hstage := guessStageTM_hoareTime guessReg hj w t targets hnodup B hB inp₀ out₀ W₀
    hinpSI houtSI hinp hout hinvW hhW hinj hbound
  have hresSI : resT.StartInvariant :=
    ⟨(ginv ((Fin.castAdd r (Fin.last (jj + 1))).castSucc)).1,
      fun q hq => (ginv ((Fin.castAdd r (Fin.last (jj + 1))).castSucc)).2 q hq⟩
  set W₁ : Fin (jj + 2) → Tape :=
    Fin.snoc (fun i : Fin (jj + 1) => (⟨1, cells' i⟩ : Tape)) (resT.write (Γ.ofBool v)) with hW₁
  have hGns : ∀ i, (G i).read ≠ Γ.start := fun i => (ginv i).read_ne_start (ghh i)
  have hGaux : ∀ c : Fin r, G (Fin.natAdd (jj + 2) c).castSucc
      = W₀ (Fin.natAdd (jj + 2) c).castSucc := by
    intro c
    refine (guessBlocksTapes_spec guessReg hj w t W₀ hinvW hhW hinj).2.2.2.1
      _ (fun hc => ?_) (fun p hp hc => hauxG p c hp hc.symm)
    exact absurd (congrArg Fin.val hc) (by simp [Fin.natAdd]; omega)
  have hresW : (resT.write (Γ.ofBool v)).StartInvariant := by
    have := hresSI.write (Γw.ofBool v)
    rwa [Γw.ofBool_toΓ] at this
  have hW₁inv : ∀ i, (W₁ i).StartInvariant := by
    intro i
    refine Fin.lastCases ?_ ?_ i
    · rw [hW₁, Fin.snoc_last]
      exact hresW
    · intro q
      rw [hW₁, Fin.snoc_castSucc]
      exact hcells' q
  have hW₁head : ∀ i, 1 ≤ (W₁ i).head := by
    intro i
    refine Fin.lastCases ?_ ?_ i
    · rw [hW₁, Fin.snoc_last]
      show 1 ≤ (resT.write (Γ.ofBool v)).head
      rw [Tape.write_head]
    · intro q
      rw [hW₁, Fin.snoc_castSucc]
  have hand : (andCellTM (Fin.castAdd r (Fin.last (jj + 1))).castSucc accIdx).HoareTime
      (fun inp work out =>
        work (Fin.last (jj + 2 + r)) = G (Fin.last (jj + 2 + r)) ∧
        (∀ c : Fin r,
          work (Fin.natAdd (jj + 2) c).castSucc = W₀ (Fin.natAdd (jj + 2) c).castSucc) ∧
        inp = parkTape inp₀ ∧ out = parkTape out₀ ∧
        (∀ i : Fin (jj + 2), work (Fin.castAdd r i).castSucc = W₁ i))
      (fun inp work out =>
        work (Fin.last (jj + 2 + r)) = G (Fin.last (jj + 2 + r)) ∧
        (∀ c : Fin r, (Fin.natAdd (jj + 2) c).castSucc ≠ accIdx →
          work (Fin.natAdd (jj + 2) c).castSucc = W₀ (Fin.natAdd (jj + 2) c).castSucc) ∧
        inp = parkTape inp₀ ∧ out = parkTape out₀ ∧
        (∀ i : Fin (jj + 2), work (Fin.castAdd r i).castSucc = W₁ i) ∧
        work accIdx = ⟨(W₀ accIdx).head, Function.update (W₀ accIdx).cells (W₀ accIdx).head
          (if v = true ∧ (W₀ accIdx).read = Γ.one then Γ.one else Γ.zero)⟩)
      1 := by
    rintro inp work out ⟨hglast, hgaux, rfl, rfl, hregs⟩
    have hidx : ∀ P : Fin (jj + 2 + r + 1) → Prop, P (Fin.last (jj + 2 + r)) →
        (∀ i : Fin (jj + 2), P (Fin.castAdd r i).castSucc) →
        (∀ c : Fin r, P (Fin.natAdd (jj + 2) c).castSucc) → ∀ i, P i := by
      intro P hlastP hregP hauxP i
      refine Fin.lastCases hlastP ?_ i
      intro k
      exact Fin.addCases (fun i => hregP i) (fun c => hauxP c) k
    have hacc : work accIdx = W₀ accIdx := by
      refine hidx (fun i => i = accIdx → work i = W₀ i) ?_ ?_ ?_ accIdx rfl
      · exact fun hc => absurd hc.symm haccLast
      · exact fun i hc => absurd hc.symm (haccReg i)
      · exact fun c _ => hgaux c
    have hinv' : ∀ i, (work i).StartInvariant := by
      refine hidx _ ?_ ?_ ?_
      · rw [hglast]; exact ginv _
      · intro i; rw [hregs i]; exact hW₁inv i
      · intro c; rw [hgaux c]; exact hinvW _
    have hh' : ∀ i, 1 ≤ (work i).head := by
      refine hidx _ ?_ ?_ ?_
      · rw [hglast]; exact ghh _
      · intro i; rw [hregs i]; exact hW₁head i
      · intro c; rw [hgaux c]; exact hhW _
    obtain ⟨c', tt, htt, hreach, hhalt, hin', hout', hother', hacc'⟩ :=
      andCellTM_hoareTime' (Fin.castAdd r (Fin.last (jj + 1))).castSucc accIdx
        (parkTape inp₀) (parkTape out₀) work hinv' hh'
        (parkTape_parked houtSI).read_ne_start (parkTape inp₀) work
        (parkTape out₀) ⟨rfl, rfl, rfl⟩
    rw [transitionInput_eq_self (parkTape_parked hinpSI).read_ne_start] at hin'
    have hsrcRead : (work (Fin.castAdd r (Fin.last (jj + 1))).castSucc).read = Γ.ofBool v := by
      rw [hregs (Fin.last (jj + 1)), hW₁, Fin.snoc_last]
      show (resT.write (Γ.ofBool v)).read = _
      rw [Tape.write, if_neg (show resT.head ≠ 0 by rw [hresT]; exact one_ne_zero)]
      show Function.update resT.cells resT.head (Γ.ofBool v) resT.head = _
      rw [Function.update_self]
    refine ⟨c', tt, htt, hreach, hhalt, ?_, ?_, hin', hout', ?_, ?_⟩
    · rw [hother' _ (Ne.symm haccLast), hglast]
    · intro c hc
      rw [hother' _ hc, hgaux c]
    · intro i
      rw [hother' _ (fun hcc => haccReg i hcc.symm), hregs i]
    · rw [hacc', hacc, hsrcRead]
      have hcond : (Γ.ofBool v = Γ.one) ↔ (v = true) := by
        cases v <;> simp [Γ.ofBool]
      simp only [hcond]
  have hmany := liftMany_hoareTime _ hD r
    (fun c => W₀ (Fin.natAdd (jj + 2) c).castSucc)
    (fun c => (hinvW _).read_ne_start (hhW _))
  have hlift := liftLast_hoareTime _ hmany (G (Fin.last (jj + 2 + r)))
    (hGns (Fin.last (jj + 2 + r)))
  refine seqTM_hoareTime _ _ hstage ?_ (seqTM_hoareTime _ _ hlift ?_ hand)
  · rintro inp work out ⟨hlast, hinpP, hwork, houtP⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show transitionTape (work (Fin.last (jj + 2 + r))) = G (Fin.last (jj + 2 + r))
      rw [hlast]
      exact transitionTape_eq_self (hGns _)
    · intro c
      show transitionTape (work (Fin.natAdd (jj + 2) c).castSucc) = _
      have hc : work (Fin.natAdd (jj + 2) c).castSucc
          = parkTape (G (Fin.natAdd (jj + 2) c).castSucc) := by
        have := congrFun hwork (Fin.natAdd (jj + 2) c)
        rw [this, if_neg (haux c)]
      rw [hc, hGaux c, parkTape_eq_self (hhW _)]
      exact transitionTape_eq_self ((hinvW _).read_ne_start (hhW _))
    · rw [hinpP]
      exact transitionInput_eq_self (parkTape_parked hinpSI).read_ne_start
    · rw [houtP]
      exact transitionTape_eq_self (parkTape_parked houtSI).read_ne_start
    · funext i
      show transitionTape (work (Fin.castAdd r i).castSucc) = _
      have hi : work (Fin.castAdd r i).castSucc
          = (⟨1, (G (Fin.castAdd r i).castSucc).cells⟩ : Tape) := by
        have := congrFun hwork (Fin.castAdd r i)
        rw [this, if_pos (hall i)]
      rw [hi, transitionTape_eq_self (by
        show (⟨1, (G (Fin.castAdd r i).castSucc).cells⟩ : Tape).read ≠ Γ.start
        exact fun hc => (ginv (Fin.castAdd r i).castSucc).2 1 le_rfl hc)]
      refine Fin.lastCases ?_ ?_ i
      · rw [Fin.snoc_last]
      · intro q
        rw [Fin.snoc_castSucc]
  · rintro inp work out ⟨hlast, hgaux, hin, hout', hregs⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show transitionTape (work (Fin.last (jj + 2 + r))) = _
      rw [hlast]
      exact transitionTape_eq_self (hGns _)
    · intro c
      have h : work (Fin.natAdd (jj + 2) c).castSucc = W₀ (Fin.natAdd (jj + 2) c).castSucc :=
        hgaux c
      show transitionTape (work (Fin.natAdd (jj + 2) c).castSucc) = _
      rw [h]
      exact transitionTape_eq_self ((hinvW _).read_ne_start (hhW _))
    · rw [hin]
      exact transitionInput_eq_self (parkTape_parked hinpSI).read_ne_start
    · rw [hout']
      exact transitionTape_eq_self (parkTape_parked houtSI).read_ne_start
    · intro i
      show transitionTape (work (Fin.castAdd r i).castSucc) = _
      rw [show work (Fin.castAdd r i).castSucc = W₁ i from congrFun hregs i]
      exact transitionTape_eq_self ((hW₁inv i).read_ne_start (hW₁head i))

/-- **The contract of a guess-and-check stage.** The guessed tapes are named by
`Complexity.TM.guessBlocksTapes`; what they contain is the caller's business, and the scanner's
verdict is what the accumulator records. -/
theorem guessCheckTM_hoareTime (r : ℕ) (S : Scanner jj)
    (guessReg : ℕ → Fin (jj + 2 + r + 1)) (w : ℕ → ℕ) (t : ℕ)
    (targets : List (Fin (jj + 2 + r))) (accIdx : Fin (jj + 2 + r + 1)) (hnodup : targets.Nodup)
    (hall : ∀ i : Fin (jj + 2), Fin.castAdd r i ∈ targets)
    (haux : ∀ c : Fin r, Fin.natAdd (jj + 2) c ∉ targets)
    (hauxG : ∀ p c, p < t → guessReg p ≠ (Fin.natAdd (jj + 2) c).castSucc)
    (haccReg : ∀ i : Fin (jj + 2), accIdx ≠ (Fin.castAdd r i).castSucc)
    (haccLast : accIdx ≠ Fin.last (jj + 2 + r))
    (hj : ∀ p, guessReg p ≠ Fin.last (jj + 2 + r)) (B : ℕ) (hB : 1 ≤ B)
    (inp₀ out₀ : Tape) (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (hinpSI : inp₀.StartInvariant) (houtSI : out₀.StartInvariant)
    (hinp : inp₀.read ≠ Γ.start) (hout : out₀.read ≠ Γ.start)
    (hinvW : ∀ i, (W₀ i).StartInvariant) (hhW : ∀ i, 1 ≤ (W₀ i).head)
    (hinj : ∀ p q, p < t → q < t → guessReg p = guessReg q → p = q)
    (hbound : ∀ i, i ∈ targets → (guessBlocksTapes guessReg w t W₀ i.castSucc).head ≤ B)
    (len : ℕ)
    (hok : ScanOk (parkTape inp₀)
      (⟨1, (guessBlocksTapes guessReg w t W₀
        (Fin.castAdd r (Fin.last (jj + 1))).castSucc).cells⟩ : Tape)
      (parkTape out₀))
    (ht : ScanTape (fun i : Fin (jj + 1) =>
      (guessBlocksTapes guessReg w t W₀ (Fin.castAdd r i.castSucc).castSucc).cells) len) :
    (guessCheckTM r S guessReg w t targets accIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧ work = W₀)
      (fun inp work out =>
        work (Fin.last (jj + 2 + r)) = guessBlocksTapes guessReg w t W₀ (Fin.last (jj + 2 + r)) ∧
        (∀ c : Fin r, (Fin.natAdd (jj + 2) c).castSucc ≠ accIdx →
          work (Fin.natAdd (jj + 2) c).castSucc = W₀ (Fin.natAdd (jj + 2) c).castSucc) ∧
        inp = parkTape inp₀ ∧ out = parkTape out₀ ∧
        (∀ i : Fin (jj + 2), work (Fin.castAdd r i).castSucc =
          (Fin.snoc (fun i : Fin (jj + 1) =>
            (⟨1, (guessBlocksTapes guessReg w t W₀
              (Fin.castAdd r i.castSucc).castSucc).cells⟩ : Tape))
          ((⟨1, (guessBlocksTapes guessReg w t W₀
              (Fin.castAdd r (Fin.last (jj + 1))).castSucc).cells⟩ : Tape).write
            (Γ.ofBool (S.emit (S.run (scanCol (fun i : Fin (jj + 1) =>
              (guessBlocksTapes guessReg w t W₀
                (Fin.castAdd r i.castSucc).castSucc).cells)) len))))
            : Fin (jj + 2) → Tape) i) ∧
        work accIdx = ⟨(W₀ accIdx).head, Function.update (W₀ accIdx).cells (W₀ accIdx).head
          (if S.emit (S.run (scanCol (fun i : Fin (jj + 1) =>
              (guessBlocksTapes guessReg w t W₀
                (Fin.castAdd r i.castSucc).castSucc).cells)) len) = true ∧
              (W₀ accIdx).read = Γ.one
            then Γ.one else Γ.zero)⟩)
      (guessBlocksTime w t + 1 + (1 + 1 + (targets.length * (B + 3) + 1)) + 1 +
        (2 * len + 3 + 1 + 1)) :=
  guessThenCheck_hoareTime r (twoPassTM S) guessReg w t targets accIdx hnodup hall haux hauxG
    haccReg haccLast hj B hB inp₀ out₀ W₀ hinpSI houtSI hinp hout hinvW hhW hinj hbound
    (fun i => (guessBlocksTapes guessReg w t W₀ (Fin.castAdd r i.castSucc).castSucc).cells)
    (S.emit (S.run (scanCol (fun i : Fin (jj + 1) =>
      (guessBlocksTapes guessReg w t W₀ (Fin.castAdd r i.castSucc).castSucc).cells)) len))
    (2 * len + 3) (fun i => ⟨ht.start i, fun p hp => ht.ne_start i p hp⟩)
    (twoPassTM_hoareTime S _ len (parkTape inp₀) (parkTape out₀) _ hok ht)

end TM

end Complexity
