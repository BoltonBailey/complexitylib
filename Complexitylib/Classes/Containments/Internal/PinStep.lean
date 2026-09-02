/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.FamStep
public import Complexitylib.Classes.Containments.Internal.ConstScan

/-!
# Starting a walk

⚠️ Unreviewed by Bolton

A walk runs from the code its first tuple holds, so an enclosing loop that walks once per
candidate has to put the initial code back into that tuple before each walk. The stage that does
it is an ordinary guess-and-check stage — `Complexity.TM.guessCheckTM` — over the same register
block a walk step guesses, with the walk's scanner replaced by
`Complexity.Scanner.bitsEq` on each block: guess the tuple, then check it spells out the code the
caller names.

Because the block it guesses is the one a walk's *second* stage guesses, every layout fact the
walk needed — `Complexity.stepTargets`, `Complexity.stepReg_inj`,
`Complexity.head_guessBlocksTapes_le` — applies unchanged.

## Main definitions

- `pinScanner` — the check that a register tuple spells out a given code
- `pinStepTM` — guess the tuple and run that check

## Main results

- `pinScanner_run` — the check accepts exactly when the tuple holds the code
- `guessProtocol_pinStepTM` — the stage consumes its guesses in order
-/

@[expose] public section

namespace Complexity

variable {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ}

/-- **The check that a register tuple spells out a known code.** -/
noncomputable def pinScanner {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ) {jj : ℕ}
    (cA : ℕ → Fin (jj + 1)) (a₀ : Code tm.Q kk x.length S) : Scanner jj :=
  Scanner.all (kk + 3) (fun p => Scanner.bitsEq jj (cA p.val) (codeBlockScan tm x S a₀ p.val))

/-- **It accepts exactly when the tuple holds the code.** -/
theorem pinScanner_run {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cA : ℕ → Fin (jj + 1)) (a₀ : Code tm.Q kk x.length S) (cols : ℕ → Fin (jj + 1) → Γ)
    (len : ℕ) (hlen : walkScanLen tm x.length S ≤ len) :
    (pinScanner tm x S cA a₀).emit ((pinScanner tm x S cA a₀).run cols len) = true ↔
      ∀ p, p < kk + 3 → HoldsBits cols 0 (cA p) (codeBlockScan tm x S a₀ p) := by
  have hblk : ∀ p : ℕ, (codeBlockScan tm x S a₀ p).length ≤ len := by
    intro p
    rw [codeBlockScan_length tm x S a₀ p]
    exact le_trans (blockLen_le tm x.length S p) hlen
  rw [pinScanner, Scanner.all_emit_run]
  constructor
  · intro h p hp
    exact (Scanner.bitsEq_run jj (cA p) (codeBlockScan tm x S a₀ p) cols len (hblk p)).mp
      (h ⟨p, hp⟩)
  · intro h p
    exact (Scanner.bitsEq_run jj (cA p.val) (codeBlockScan tm x S a₀ p.val) cols len
      (hblk p.val)).mpr (h p.val p.isLt)

/-- **The stage that starts a walk**: guess the first tuple, then check it holds the code. -/
noncomputable def pinStepTM {rr : ℕ} (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (a₀ : Code tm.Q kk x.length S) (cc : Fin rr) : TM (jj + 2 + rr + 1) :=
  famStepTM L (TM.twoPassTM (pinScanner tm x S L.toWalkLayout.codeA a₀)) 0 cc

/-- Its advancing states. -/
noncomputable def pinStepAdv {rr : ℕ} (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (a₀ : Code tm.Q kk x.length S) (cc : Fin rr) : (pinStepTM x L a₀ cc).Q → Bool :=
  famStepAdv L (TM.twoPassTM (pinScanner tm x S L.toWalkLayout.codeA a₀)) 0 cc

/-- **The stage respects the guess protocol.** -/
theorem guessProtocol_pinStepTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (a₀ : Code tm.Q kk x.length S) (cc : Fin rr) :
    TM.GuessProtocol (pinStepTM x L a₀ cc) (pinStepAdv x L a₀ cc) :=
  guessProtocol_famStepTM L _ 0 cc

/-- **What a pin stage does.** Whatever the guess was, the stage runs and leaves the tapes fit for
the next one; and if the accumulator survives, the first tuple holds the code the caller named. -/
theorem pinStep_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (a₀ : Code tm.Q kk x.length S) (g : ℕ → Bool) (s : ℕ) (cc : Fin r) (B : ℕ)
    (hB1 : 1 ≤ B) (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) (inp₀ out₀ : Tape)
    (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (htapes : WalkTapes (r := r) x L g s cc Wa Wt inp₀ W₀ out₀) :
    ∃ (c' : Cfg (jj + 2 + r + 1) (pinStepTM x L a₀ cc).Q) (t : ℕ),
      t ≤ famTime x L r B ∧
      (pinStepTM x L a₀ cc).reachesIn t
        ⟨(pinStepTM x L a₀ cc).qstart, inp₀, W₀, out₀⟩ c' ∧
      (pinStepTM x L a₀ cc).halted c' ∧
      WalkTapes (r := r) x L g (s + 1) cc Wa Wt c'.input c'.work c'.output ∧
      c'.input = TM.parkTape inp₀ ∧
      (∀ n, n < L.toWalkLayout.spares → ∀ p, p < kk + 3 → ∀ q,
        (c'.work (walkReg (L.toWalkLayout.spareReg n p))).cells q
          = (W₀ (walkReg (L.toWalkLayout.spareReg n p))).cells q) ∧
      ((c'.work (auxIdx jj cc)).read = Γ.one →
        (W₀ (auxIdx jj cc)).read = Γ.one ∧
        HoldsCodeTail tm x S (fun q i => (c'.work (walkReg i)).cells q)
          L.toWalkLayout.codeA a₀) ∧
      ((∀ p, p < kk + 3 → HoldsBits (fun q i => stepCellsF L 0 W₀ i q) 0
          (L.toWalkLayout.codeA p) (codeBlockScan tm x S a₀ p)) →
        ∀ b : Bool, (W₀ (auxIdx jj cc)).read = Γ.ofBool b →
          (c'.work (auxIdx jj cc)).read = Γ.ofBool b) := by
  obtain ⟨c', t, htle, hreach, hhalt, htapes', hinp', hreg, hacc, hkeep⟩ :=
    famStep_run x L (pinScanner tm x S L.toWalkLayout.codeA a₀) 0 (by omega) g s cc B hB1 hB
      Wa Wt inp₀ out₀ W₀ htapes
  have hcodeT : ∀ p, p < kk + 3 → ∀ q,
      stepCellsF L 0 W₀ (L.toWalkLayout.codeT p) q = Wt p q := by
    intro p hp q
    rw [codeT_eq_famIdx L p hp,
      congrFun (stepCellsF_fam L 0 2 (by omega) (by have := L.toWalkLayout.spares_pos; omega)
        (by omega) W₀ htapes.2.1 htapes.2.2.1 p hp) q, ← codeT_eq_famIdx L p hp]
    exact htapes.2.2.2.2.2.2.2.2.2.2 p hp q
  refine ⟨c', t, htle, hreach, hhalt, ?_, hinp', fun n hn p hp q => ?_, fun hone => ?_,
    fun hbits b hb => ?_⟩
  · exact ⟨htapes'.1, htapes'.2.1, htapes'.2.2.1, htapes'.2.2.2.1, htapes'.2.2.2.2.1,
      htapes'.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.2.1,
      htapes'.2.2.2.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.2.2.2.1,
      fun p hp q => (htapes'.2.2.2.2.2.2.2.2.2.2 p hp q).trans (hcodeT p hp q)⟩
  · rw [hreg (L.toWalkLayout.spareReg n p)]
    show stepCellsF L 0 W₀ (L.toWalkLayout.spareReg n p) q = _
    rw [congrFun (stepCellsF_spare L 0 (by omega) n hn (by omega) W₀ htapes.2.1 htapes.2.2.1 p hp)
      q]
  · obtain ⟨hold, hv⟩ := hacc hone
    refine ⟨hold, ?_⟩
    have hbits := (pinScanner_run tm x S L.toWalkLayout.codeA a₀
      (TM.scanCol (stepCellsF L 0 W₀)) (walkScanLen tm x.length S) le_rfl).mp hv
    refine holdsCodeTail_of_blocks tm x S (fun q i => (c'.work (walkReg i)).cells q)
      L.toWalkLayout.codeA a₀ (fun p hp q hq => ?_)
    show (c'.work (walkReg (L.toWalkLayout.codeA p))).cells (0 + q + 1) = _
    rw [hreg (L.toWalkLayout.codeA p)]
    exact hbits p hp q hq
  · exact hkeep ((pinScanner_run tm x S L.toWalkLayout.codeA a₀
      (TM.scanCol (stepCellsF L 0 W₀)) (walkScanLen tm x.length S) le_rfl).mpr hbits) b hb

/-- **The guess a pin stage wants**: the code's blocks, written into the tuple the stage
guesses. -/
noncomputable def pinCert {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ) {jj : ℕ}
    (L : WalkLayout kk jj) (a₀ : Code tm.Q kk x.length S) : ℕ → ℕ → Bool :=
  fun p q => if L.scratch ≤ p then (codeBlockScan tm x S a₀ (p - L.scratch)).getD q false
    else false

/-- **A guess that follows the certificate writes the code.** -/
theorem holdsBits_pin (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (a₀ : Code tm.Q kk x.length S) (bc : ℕ → ℕ → ℕ → Bool) (g : ℕ → Bool)
    (hs : TM.StageBlocks (stepWidth L) L.toWalkLayout.stepBlocks bc g) (s : ℕ)
    (hb : ∀ p q, bc s p q = pinCert tm x S L.toWalkLayout a₀ p q)
    (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.stepBlocks → (W (stepRegF L 0 p)).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks + q))
      (W (Fin.last (jj + 2 + r)))) :
    ∀ p, p < kk + 3 → HoldsBits (fun q i => stepCellsF L 0 W i q) 0
      (L.toWalkLayout.codeA p) (codeBlockScan tm x S a₀ p) := by
  intro p hp
  have hlen : (codeBlockScan tm x S a₀ p).length
      ≤ stepWidth L (L.toWalkLayout.scratch + p) + 1 := by
    rw [codeBlockScan_length tm x S a₀ p, stepWidth_code L p hp]
    exact blockLen_le_codeWidthScan tm x.length S p
  have h := holdsBits_blockF_of_step x L 0 (by omega) bc g hs s W hinv hh hr1 hgf
    (L.toWalkLayout.scratch + p) (by rw [WalkLayout.stepBlocks]; omega)
    (codeBlockScan tm x S a₀ p)
    (fun q hq => by
      rw [hb, pinCert, if_pos (by omega), Nat.add_sub_cancel_left,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
      rfl)
    hlen
  rw [show (stepRegF L 0 (L.toWalkLayout.scratch + p) : Fin (jj + 2 + r + 1))
    = walkReg (L.toWalkLayout.codeA p) by
      rw [stepRegF_fam, L.toWalkLayout.famIdx_codeA p hp]; rfl] at h
  exact h

end Complexity
