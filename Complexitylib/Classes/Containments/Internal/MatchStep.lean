/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.FamStep

/-!
# A stage that reads the input tape

⚠️ Unreviewed by Bolton

A walk step compares the guessed input symbol against the machine's own input tape, and then
moves that head along. A *successor certificate* needs the comparison but not the move: it names
the successor of the code the walk ended on, and the next certificate has to name the other
successor of the same code, so the head must stay where it is.

`Complexity.matchStepTM` is that stage — `Complexity.famStepTM` with an input match in front of
the scan — and `Complexity.matchScan_hoareTime` is the walk's own check phase with the scanner
made a parameter.

## Main definitions

- `matchScan_hoareTime` — input match, then any scan
- `matchStepTM` — guess a family, match the input symbol, and check

## Main results

- `matchStep_run` — what such a stage leaves on the tapes
-/

@[expose] public section

namespace Complexity

variable {kk jj r : ℕ} {tm : NTM kk} {nn S wc : ℕ}

/-- How long a matching stage runs. -/
noncomputable def matchTime (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (rr B : ℕ) : ℕ :=
  TM.guessBlocksTime (stepWidth L) L.toWalkLayout.stepBlocks + 1 +
    (1 + 1 + ((stepTargets jj rr).length * (B + 3) + 1)) + 1 +
    (2 + 1 + (2 * walkScanLen tm x.length S + 3) + 1 + 1)

/-- **A stage that matches the input symbol before checking.** Unlike a walk step it does not move
the input head, so two such stages in a row speak about the same configuration — which is what
naming both successors of a code needs. -/
noncomputable def matchStepTM {rr : ℕ} (L : WalkWidths kk jj tm nn S wc) (Sc : Scanner jj)
    (f : ℕ) (cc : Fin rr) : TM (jj + 2 + rr + 1) :=
  famStepTM L (TM.seqTM (TM.inMatchTM gammaBits L.toWalkLayout.par.castSucc
    L.toWalkLayout.res.castSucc) (TM.twoPassTM Sc)) f cc

/-- Its advancing states. -/
noncomputable def matchStepAdv {rr : ℕ} (L : WalkWidths kk jj tm nn S wc) (Sc : Scanner jj)
    (f : ℕ) (cc : Fin rr) : (matchStepTM L Sc f cc).Q → Bool :=
  famStepAdv L (TM.seqTM (TM.inMatchTM gammaBits L.toWalkLayout.par.castSucc
    L.toWalkLayout.res.castSucc) (TM.twoPassTM Sc)) f cc

/-- **It respects the guess protocol.** -/
theorem guessProtocol_matchStepTM {rr : ℕ} (L : WalkWidths kk jj tm nn S wc) (Sc : Scanner jj)
    (f : ℕ) (cc : Fin rr) :
    TM.GuessProtocol (matchStepTM L Sc f cc) (matchStepAdv L Sc f cc) :=
  guessProtocol_famStepTM L _ f cc

/-- **What such a stage does.** The registers it leaves are the guessed ones with the input
check's verdict written on the result register, and the accumulator keeps its bit exactly when the
scan accepts. -/
theorem matchStep_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc) (Sc : Scanner jj)
    (f : ℕ) (hf : f < 2 + L.toWalkLayout.spares) (g : ℕ → Bool) (s : ℕ) (cc : Fin r) (B : ℕ)
    (hB1 : 1 ≤ B) (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) (inp₀ out₀ : Tape)
    (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (htapes : WalkTapes (r := r) x L g s cc Wa Wt inp₀ W₀ out₀) :
    ∃ (c' : Cfg (jj + 2 + r + 1) (matchStepTM L Sc f cc).Q) (t : ℕ),
      t ≤ matchTime x L r B ∧
      (matchStepTM L Sc f cc).reachesIn t
        ⟨(matchStepTM L Sc f cc).qstart, inp₀, W₀, out₀⟩ c' ∧
      (matchStepTM L Sc f cc).halted c' ∧
      WalkTapes (r := r) x L g (s + 1) cc Wa
        (fun p q => checkedCells (stepCellsF L f W₀) L.toWalkLayout.par L.toWalkLayout.res
          (TM.parkTape inp₀).read (L.toWalkLayout.codeT p) q)
        c'.input c'.work c'.output ∧
      c'.input = TM.parkTape inp₀ ∧
      (∀ i : Fin (jj + 1), c'.work (walkReg i)
        = (⟨1, checkedCells (stepCellsF L f W₀) L.toWalkLayout.par L.toWalkLayout.res
            (TM.parkTape inp₀).read i⟩ : Tape)) ∧
      ((c'.work (auxIdx jj cc)).read = Γ.one →
        (W₀ (auxIdx jj cc)).read = Γ.one ∧
        Sc.emit (Sc.run (TM.scanCol (checkedCells (stepCellsF L f W₀) L.toWalkLayout.par
          L.toWalkLayout.res (TM.parkTape inp₀).read)) (walkScanLen tm x.length S)) = true) ∧
      (Sc.emit (Sc.run (TM.scanCol (checkedCells (stepCellsF L f W₀) L.toWalkLayout.par
          L.toWalkLayout.res (TM.parkTape inp₀).read)) (walkScanLen tm x.length S)) = true →
        ∀ b : Bool, (W₀ (auxIdx jj cc)).read = Γ.ofBool b →
          (c'.work (auxIdx jj cc)).read = Γ.ofBool b) := by
  have hr1 : ∀ p, p < L.toWalkLayout.stepBlocks → (W₀ (stepRegF L f p)).head = 1 :=
    fun p _ => htapes.2.2.2.1 (L.toWalkLayout.reg (L.toWalkLayout.stepIdxF f p)).castSucc
  have hscan := scanTapeF_of_step_any x L f hf g s W₀ htapes.2.1 htapes.2.2.1 hr1
    htapes.2.2.2.2.2.2.2.2.2.1 htapes.2.2.2.2.1
  have hchecked := scanTape_checked hscan L.toWalkLayout.par L.toWalkLayout.res
    L.toWalkLayout.res_ne_zero (TM.parkTape inp₀).read
  have hinpSI : inp₀.StartInvariant := by
    refine ⟨?_, fun q hq => ?_⟩
    · rw [show inp₀.cells 0 = (Tape.init (x.map Γ.ofBool)).cells 0 from
        congrFun htapes.2.2.2.2.2.1 0]
      exact Tape.init_cells_zero _
    · rw [show inp₀.cells q = (Tape.init (x.map Γ.ofBool)).cells q from
        congrFun htapes.2.2.2.2.2.1 q]
      exact Tape.init_ofBool_cells_ne_start x q hq
  have hresSI : (⟨1, (TM.guessBlocksTapes (stepRegF L f) (stepWidth L)
      L.toWalkLayout.stepBlocks W₀
      (Fin.castAdd r (Fin.last (jj + 1))).castSucc).cells⟩ : Tape).StartInvariant := by
    have h := (TM.guessBlocksTapes_spec (stepRegF (r := r) L f)
      (fun p => stepRegF_ne_last L f p) (stepWidth L) L.toWalkLayout.stepBlocks W₀
      htapes.2.1 htapes.2.2.1 (stepRegF_inj L f hf)).1
      (Fin.castAdd r (Fin.last (jj + 1))).castSucc
    exact ⟨h.1, fun q hq => h.2 q hq⟩
  exact famThenStep_run x L _ f hf g s cc B hB1 hB Wa Wt inp₀ out₀ W₀ htapes
    (checkedCells (stepCellsF L f W₀) L.toWalkLayout.par L.toWalkLayout.res
      (TM.parkTape inp₀).read)
    (Sc.emit (Sc.run (TM.scanCol (checkedCells (stepCellsF L f W₀) L.toWalkLayout.par
      L.toWalkLayout.res (TM.parkTape inp₀).read)) (walkScanLen tm x.length S)))
    (2 + 1 + (2 * walkScanLen tm x.length S + 3))
    (fun i => ⟨hchecked.start i, fun q hq => hchecked.ne_start i q hq⟩)
    (by rw [L.toWalkLayout.ruler_zero]; exact hchecked.blank)
    (matchScan_hoareTime Sc L.toWalkLayout.par L.toWalkLayout.res (stepCellsF L f W₀)
      (walkScanLen tm x.length S) (TM.parkTape inp₀) (TM.parkTape out₀) _
      (scanOkF_of_step L f hf W₀ htapes.2.1 htapes.2.2.1 inp₀ out₀ hinpSI
        htapes.2.2.2.2.2.2.2.1) hscan hresSI le_rfl L.toWalkLayout.par_ne_res hchecked)

/-- **A matching stage carries the frame too.** -/
theorem matchStep_tapes (x : List Bool) (L : WalkWidths kk jj tm x.length S wc) (Sc : Scanner jj)
    (f : ℕ) (hf : f < 2 + L.toWalkLayout.spares) (hf2 : f ≠ 2) (g : ℕ → Bool) (s : ℕ)
    (cc : Fin r) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) :
    (matchStepTM L Sc f cc).HoareTime
      (fun inp work out => WalkTapes (r := r) x L g s cc Wa Wt inp work out)
      (fun inp work out => WalkTapes (r := r) x L g (s + 1) cc Wa Wt inp work out)
      (matchTime x L r B) := by
  intro inp₀ W₀ out₀ htapes
  obtain ⟨c', t, htle, hreach, hhalt, htapes', -, -, -, -⟩ :=
    matchStep_run x L Sc f hf g s cc B hB1 hB Wa Wt inp₀ out₀ W₀ htapes
  refine ⟨c', t, htle, hreach, hhalt, ?_⟩
  refine ⟨htapes'.1, htapes'.2.1, htapes'.2.2.1, htapes'.2.2.2.1, htapes'.2.2.2.2.1,
    htapes'.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.2.1,
    htapes'.2.2.2.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.2.2.2.1, fun p hp q => ?_⟩
  refine (htapes'.2.2.2.2.2.2.2.2.2.2 p hp q).trans ?_
  show checkedCells (stepCellsF L f W₀) L.toWalkLayout.par L.toWalkLayout.res
    (TM.parkTape inp₀).read (L.toWalkLayout.codeT p) q = Wt p q
  rw [checked_cell _ _ _ _ _ (L.toWalkLayout.codeT_ne_res hp),
    congrFun (stepCellsF_codeT L f hf hf2 W₀ htapes.2.1 htapes.2.2.1 p hp) q]
  exact htapes.2.2.2.2.2.2.2.2.2.2 p hp q

/-- **A code another family holds survives a matching stage too.** The input check writes only the
verdict register, which no code family owns. -/
theorem holdsCodeTail_famReg_survives_checked (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (f f' : ℕ)
    (hf : f < 2 + L.toWalkLayout.spares) (hf' : f' < 2 + L.toWalkLayout.spares) (hne : f ≠ f')
    (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head) (gsym : Γ) (a : Code tm.Q kk x.length S)
    (ha : HoldsCodeTail tm x S (fun q i => (W (walkReg i)).cells q)
      (L.toWalkLayout.famReg f') a) :
    HoldsCodeTail tm x S
      (fun q i => checkedCells (stepCellsF L f W) L.toWalkLayout.par L.toWalkLayout.res gsym i q)
      (L.toWalkLayout.famReg f') a :=
  holdsCodeTail_congr tm x S _ _ (L.toWalkLayout.famReg f') a ha (fun p hp q => by
    rw [checked_cell _ _ _ _ _ (L.toWalkLayout.famReg_ne_res f' hf' p hp),
      congrFun (stepCellsF_famReg L f f' hf hf' hne W hinv hh p hp) q])

/-- **The blocks another family holds survive a matching stage.** -/
theorem holdsBlocks_survives_checked (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (f f' : ℕ)
    (hf : f < 2 + L.toWalkLayout.spares) (hf' : f' < 2 + L.toWalkLayout.spares) (hne : f ≠ f')
    (c : ℕ → Fin (jj + 1)) (hc : ∀ p, p < kk + 3 → c p = L.toWalkLayout.famReg f' p)
    (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head) (gsym : Γ) (a : Code tm.Q kk x.length S)
    (ha : ∀ p, p < kk + 3 → HoldsBits (fun q i => (W (walkReg i)).cells q) 0
      (c p) (codeBlockScan tm x S a p)) :
    ∀ p, p < kk + 3 → HoldsBits
      (fun q i => checkedCells (stepCellsF L f W) L.toWalkLayout.par L.toWalkLayout.res gsym i q)
      0 (c p) (codeBlockScan tm x S a p) := by
  intro p hp q hq
  rw [hc p hp]
  show checkedCells (stepCellsF L f W) L.toWalkLayout.par L.toWalkLayout.res gsym
    (L.toWalkLayout.famReg f' p) (0 + q + 1) = _
  rw [checked_cell _ _ _ _ _ (L.toWalkLayout.famReg_ne_res f' hf' p hp),
    congrFun (stepCellsF_famReg L f f' hf hf' hne W hinv hh p hp) (0 + q + 1)]
  have := ha p hp q hq
  rw [hc p hp] at this
  exact this

/-- **A code another family holds survives a matching stage**, under whatever name the caller
uses for that family's registers. -/
theorem holdsCodeTail_survives_checked (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (f f' : ℕ)
    (hf : f < 2 + L.toWalkLayout.spares) (hf' : f' < 2 + L.toWalkLayout.spares) (hne : f ≠ f')
    (c : ℕ → Fin (jj + 1)) (hc : ∀ p, p < kk + 3 → c p = L.toWalkLayout.famReg f' p)
    (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head) (gsym : Γ) (a : Code tm.Q kk x.length S)
    (ha : HoldsCodeTail tm x S (fun q i => (W (walkReg i)).cells q) c a) :
    HoldsCodeTail tm x S
      (fun q i => checkedCells (stepCellsF L f W) L.toWalkLayout.par L.toWalkLayout.res gsym i q)
      c a :=
  holdsCodeTail_congr tm x S _ _ c a ha (fun p hp q => by
    rw [hc p hp, checked_cell _ _ _ _ _ (L.toWalkLayout.famReg_ne_res f' hf' p hp),
      congrFun (stepCellsF_famReg L f f' hf hf' hne W hinv hh p hp) q])

end Complexity
