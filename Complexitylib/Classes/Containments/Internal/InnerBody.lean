/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.InnerCert
public import Complexitylib.Classes.Containments.Internal.MatchStep
public import Complexitylib.Classes.Containments.Internal.PinStep
public import Complexitylib.Classes.Containments.Internal.ResetStep
public import Complexitylib.Classes.Containments.Internal.BetaScan
public import Complexitylib.Classes.Containments.Internal.PadScan
public import Complexitylib.Classes.Containments.Internal.ResetStep

/-!
# One entry of the inner counting loop

⚠️ Unreviewed by Bolton

The inner loop lists the members of a round, one per iteration, and checks each against the code
under test. One iteration is eight stages:

1. rewind the machine's own input head, which the last walk left where that walk ended;
2. clear the walk's step counter;
3. pin the first tuple to the initial code (`Complexity.pinStepTM`);
4. walk (`Complexity.walkLoopTM`), which leaves a code of the round in the first tuple;
5. check that the code the loop remembered comes below it (`Complexity.ltScanner`) — this is what
   makes the listed codes distinct;
6. and 7. name the two successors of that code, one per choice bit
   (`Complexity.succCertScanner`), and check that neither is the code under test;
8. remember the code, by guessing the spare tuple and checking it agrees
   (`Complexity.eqScanner`).

Every check conjoins its verdict into the one accumulator, so a single failure is final and no
stage has to be undone.

## Main definitions

- `innerBodyTM` — the eight stages, in order
- `innerBodyAdv` — its advancing states

## Main results

- `guessProtocol_innerBodyTM` — the whole iteration consumes its guesses in order
-/

@[expose] public section

namespace Complexity

variable {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ}

/-- The check the ordering stage runs: the code the loop remembered comes below the one the walk
ended on, the code under test is not that one either, and the tuple the walk ended on has zero
padding — which is what makes the two comparisons comparisons of *codes*. -/
noncomputable def orderTestScanner (tm : NTM kk) (nn S : ℕ) (cP cA cT : ℕ → Fin (jj + 1)) :
    Scanner jj :=
  Scanner.all 3 (fun p => if p.val = 0 then ltScanner tm nn S cP cA
    else if p.val = 1 then Scanner.not (eqScanner tm nn S cT cA)
    else padZeroScanner tm cA)

/-- The check the ordering stage runs when there is no code under test: the code the loop
remembered comes below the one the walk ended on, and that one is canonical. -/
noncomputable def orderOnlyScanner (tm : NTM kk) (nn S : ℕ) (cP cA : ℕ → Fin (jj + 1)) :
    Scanner jj :=
  Scanner.all 2 (fun p => if p.val = 0 then ltScanner tm nn S cP cA
    else padZeroScanner tm cA)

/-- The check the successor stage for choice bit `β` runs: the code the walk ended on has this
successor, and the code under test is not it. -/
noncomputable def succTestScanner (tm : NTM kk) (nn S : ℕ) (par mv dr res : Fin (jj + 1))
    (dc : DirCodec) (cA cB cT : ℕ → Fin (jj + 1)) (β : Bool) : Scanner jj :=
  Scanner.all 3 (fun p => if p.val = 0 then succCertScanner tm nn S par mv dr res dc cA cB β
    else if p.val = 1 then Scanner.not (eqScanner tm nn S cT cB)
    else padZeroScanner tm cB)

/-! ## What each of the new stages contributes -/

/-- **The remembering stage.** It guesses the spare tuple and checks it agrees with the first one,
so if the accumulator survives, the spare holds the code the walk ended on — a copy, made by
guessing. -/
theorem copyStep_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (hsp : 1 < L.toWalkLayout.spares) (g : ℕ → Bool) (s : ℕ)
    (cc : Fin r) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) (inp₀ out₀ : Tape)
    (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (htapes : WalkTapes (r := r) x L g s cc Wa Wt inp₀ W₀ out₀)
    (v u : Code tm.Q kk x.length S)
    (hpre : (W₀ (auxIdx jj cc)).read = Γ.one →
      (∀ p, p < kk + 3 → HoldsBits (fun q i => (W₀ (walkReg i)).cells q) 0
        (L.toWalkLayout.codeA p) (codeBlockScan tm x S v p)) ∧
      ∀ p, p < kk + 3 → HoldsBits (fun q i => (W₀ (walkReg i)).cells q) 0
        (L.toWalkLayout.codeT p) (codeBlockScan tm x S u p)) :
    ∃ (c' : Cfg (jj + 2 + r + 1)
        (famStepTM L (TM.twoPassTM (eqScanner tm x.length S L.toWalkLayout.codeA
          (L.toWalkLayout.spareReg 1))) 3 cc).Q) (t : ℕ),
      t ≤ famTime x L r B ∧
      (famStepTM L (TM.twoPassTM (eqScanner tm x.length S L.toWalkLayout.codeA
          (L.toWalkLayout.spareReg 1))) 3 cc).reachesIn t
        ⟨(famStepTM L (TM.twoPassTM (eqScanner tm x.length S L.toWalkLayout.codeA
          (L.toWalkLayout.spareReg 1))) 3 cc).qstart, inp₀, W₀, out₀⟩ c' ∧
      (famStepTM L (TM.twoPassTM (eqScanner tm x.length S L.toWalkLayout.codeA
          (L.toWalkLayout.spareReg 1))) 3 cc).halted c' ∧
      WalkTapes (r := r) x L g (s + 1) cc Wa Wt c'.input c'.work c'.output ∧
      c'.input = TM.parkTape inp₀ ∧
      ((c'.work (auxIdx jj cc)).read = Γ.one →
        (W₀ (auxIdx jj cc)).read = Γ.one ∧
        (∀ p, p < kk + 3 → HoldsBits (fun q i => (c'.work (walkReg i)).cells q) 0
          (L.toWalkLayout.codeT p) (codeBlockScan tm x S u p)) ∧
        ∀ p, p < kk + 3 → HoldsBits (fun q i => (c'.work (walkReg i)).cells q) 0
          (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S v p)) ∧
      (∀ n, n < L.toWalkLayout.spares → 2 + n ≠ 3 → ∀ p, p < kk + 3 → ∀ q,
        (c'.work (walkReg (L.toWalkLayout.spareReg n p))).cells q
          = (W₀ (walkReg (L.toWalkLayout.spareReg n p))).cells q) := by
  have hspares : (2 : ℕ) < 2 + L.toWalkLayout.spares := by omega
  obtain ⟨c', t, htle, hreach, hhalt, htapes', hinp', hreg, hacc, -⟩ :=
    famStep_run x L (eqScanner tm x.length S L.toWalkLayout.codeA (L.toWalkLayout.spareReg 1))
      3 (by omega) g s cc B hB1 hB Wa Wt inp₀ out₀ W₀ htapes
  have hcells : ∀ i : Fin (jj + 1), ∀ q,
      (c'.work (walkReg i)).cells q = stepCellsF L 3 W₀ i q := by
    intro i q
    rw [hreg i]
  have hWt : WalkTapes (r := r) x L g (s + 1) cc Wa Wt c'.input c'.work c'.output := by
    refine ⟨htapes'.1, htapes'.2.1, htapes'.2.2.1, htapes'.2.2.2.1, htapes'.2.2.2.2.1,
      htapes'.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.2.1,
      htapes'.2.2.2.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.2.2.2.1, fun p hp q => ?_⟩
    refine (htapes'.2.2.2.2.2.2.2.2.2.2 p hp q).trans ?_
    show stepCellsF L 3 W₀ (L.toWalkLayout.codeT p) q = Wt p q
    rw [congrFun (stepCellsF_codeT L 3 (by omega) (by omega) W₀ htapes.2.1 htapes.2.2.1 p hp) q]
    exact htapes.2.2.2.2.2.2.2.2.2.2 p hp q
  have hspare : ∀ n, n < L.toWalkLayout.spares → 2 + n ≠ 3 → ∀ p, p < kk + 3 → ∀ q,
      (c'.work (walkReg (L.toWalkLayout.spareReg n p))).cells q
        = (W₀ (walkReg (L.toWalkLayout.spareReg n p))).cells q := by
    intro n hn hne p hp q
    rw [hcells]
    exact congrFun (stepCellsF_spare L 3 (by omega) n hn (Ne.symm hne) W₀
      htapes.2.1 htapes.2.2.1 p hp) q
  refine ⟨c', t, htle, hreach, hhalt, hWt, hinp', ⟨fun hone => ?_, hspare⟩⟩
  obtain ⟨hold, hverd⟩ := hacc hone
  obtain ⟨hv, hu⟩ := hpre hold
  have hA := holdsBlocks_survives x L 3 0 (by omega) (by omega) (by omega) L.toWalkLayout.codeA
    (fun p hp => (L.toWalkLayout.famReg_zero p hp).symm) W₀ htapes.2.1 htapes.2.2.1 v hv
  have hU := holdsBlocks_survives x L 3 2 (by omega) hspares (by omega) L.toWalkLayout.codeT
    (fun p hp => codeT_eq_famIdx L p hp) W₀ htapes.2.1 htapes.2.2.1 u hu
  refine ⟨hold, fun p hp q hq => ?_, fun p hp q hq => ?_⟩
  · show (c'.work (walkReg (L.toWalkLayout.codeT p))).cells (0 + q + 1) = _
    rw [hcells]
    exact hU p hp q hq
  · show (c'.work (walkReg (L.toWalkLayout.spareReg 1 p))).cells (0 + q + 1) = _
    rw [hcells]
    exact eqScanner_forces tm x S (TM.scanCol (stepCellsF L 3 W₀)) L.toWalkLayout.codeA
      (L.toWalkLayout.spareReg 1) v hA hverd p hp q hq

/-- **The ordering stage.** It guesses a family it does not compare, so all three tuples it reads
come through untouched. If the accumulator survives: the code the loop remembered comes below the
one the walk ended on, the code under test is not that one, and the walk's tuple is canonical — so
both comparisons are comparisons of codes. -/
theorem orderStep_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (hsp : 1 < L.toWalkLayout.spares) (g : ℕ → Bool) (s : ℕ)
    (cc : Fin r) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) (inp₀ out₀ : Tape)
    (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (htapes : WalkTapes (r := r) x L g s cc Wa Wt inp₀ W₀ out₀)
    (prev v u : Code tm.Q kk x.length S)
    (hpre : (W₀ (auxIdx jj cc)).read = Γ.one →
      (∀ p, p < kk + 3 → HoldsBits (fun q i => (W₀ (walkReg i)).cells q) 0
        (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S prev p)) ∧
      HoldsCodeTail tm x S (fun q i => (W₀ (walkReg i)).cells q) L.toWalkLayout.codeA v ∧
      ∀ p, p < kk + 3 → HoldsBits (fun q i => (W₀ (walkReg i)).cells q) 0
        (L.toWalkLayout.codeT p) (codeBlockScan tm x S u p)) :
    ∃ (c' : Cfg (jj + 2 + r + 1)
        (famStepTM L (TM.twoPassTM (orderTestScanner tm x.length S (L.toWalkLayout.spareReg 1)
          L.toWalkLayout.codeA L.toWalkLayout.codeT)) 1 cc).Q) (t : ℕ),
      t ≤ famTime x L r B ∧
      (famStepTM L (TM.twoPassTM (orderTestScanner tm x.length S (L.toWalkLayout.spareReg 1)
          L.toWalkLayout.codeA L.toWalkLayout.codeT)) 1 cc).reachesIn t
        ⟨(famStepTM L (TM.twoPassTM (orderTestScanner tm x.length S (L.toWalkLayout.spareReg 1)
          L.toWalkLayout.codeA L.toWalkLayout.codeT)) 1 cc).qstart, inp₀, W₀, out₀⟩ c' ∧
      (famStepTM L (TM.twoPassTM (orderTestScanner tm x.length S (L.toWalkLayout.spareReg 1)
          L.toWalkLayout.codeA L.toWalkLayout.codeT)) 1 cc).halted c' ∧
      WalkTapes (r := r) x L g (s + 1) cc Wa Wt c'.input c'.work c'.output ∧
      c'.input = TM.parkTape inp₀ ∧
      ((c'.work (auxIdx jj cc)).read = Γ.one →
        (W₀ (auxIdx jj cc)).read = Γ.one ∧ codeLt tm x S prev v ∧ u ≠ v ∧
        HoldsCodeTail tm x S (fun q i => (c'.work (walkReg i)).cells q) L.toWalkLayout.codeA v ∧
        (∀ p, p < kk + 3 → HoldsBits (fun q i => (c'.work (walkReg i)).cells q) 0
          (L.toWalkLayout.codeT p) (codeBlockScan tm x S u p)) ∧
        (∀ p, p < kk + 3 → HoldsBits (fun q i => (c'.work (walkReg i)).cells q) 0
          (L.toWalkLayout.codeA p) (codeBlockScan tm x S v p))) ∧
      (∀ n, n < L.toWalkLayout.spares → 2 + n ≠ 1 → ∀ p, p < kk + 3 → ∀ q,
        (c'.work (walkReg (L.toWalkLayout.spareReg n p))).cells q
          = (W₀ (walkReg (L.toWalkLayout.spareReg n p))).cells q) := by
  classical
  have hspares : (2 : ℕ) < 2 + L.toWalkLayout.spares := by omega
  have hsp3 : (3 : ℕ) < 2 + L.toWalkLayout.spares := by omega
  obtain ⟨c', t, htle, hreach, hhalt, htapes', hinp', hreg, hacc, -⟩ :=
    famStep_run x L (orderTestScanner tm x.length S (L.toWalkLayout.spareReg 1)
      L.toWalkLayout.codeA L.toWalkLayout.codeT) 1 (by omega) g s cc B hB1 hB Wa Wt inp₀ out₀
      W₀ htapes
  have hcells : ∀ i : Fin (jj + 1), ∀ q,
      (c'.work (walkReg i)).cells q = stepCellsF L 1 W₀ i q := by
    intro i q
    rw [hreg i]
  have hWt : WalkTapes (r := r) x L g (s + 1) cc Wa Wt c'.input c'.work c'.output := by
    refine ⟨htapes'.1, htapes'.2.1, htapes'.2.2.1, htapes'.2.2.2.1, htapes'.2.2.2.2.1,
      htapes'.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.2.1,
      htapes'.2.2.2.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.2.2.2.1, fun p hp q => ?_⟩
    refine (htapes'.2.2.2.2.2.2.2.2.2.2 p hp q).trans ?_
    show stepCellsF L 1 W₀ (L.toWalkLayout.codeT p) q = Wt p q
    rw [congrFun (stepCellsF_codeT L 1 (by omega) (by omega) W₀ htapes.2.1 htapes.2.2.1 p hp) q]
    exact htapes.2.2.2.2.2.2.2.2.2.2 p hp q
  have hspare : ∀ n, n < L.toWalkLayout.spares → 2 + n ≠ 1 → ∀ p, p < kk + 3 → ∀ q,
      (c'.work (walkReg (L.toWalkLayout.spareReg n p))).cells q
        = (W₀ (walkReg (L.toWalkLayout.spareReg n p))).cells q := by
    intro n hn hne p hp q
    rw [hcells]
    exact congrFun (stepCellsF_spare L 1 (by omega) n hn (Ne.symm hne) W₀
      htapes.2.1 htapes.2.2.1 p hp) q
  refine ⟨c', t, htle, hreach, hhalt, hWt, hinp', ⟨fun hone => ?_, hspare⟩⟩
  obtain ⟨hold, hverd⟩ := hacc hone
  obtain ⟨hprev, hvT, hu⟩ := hpre hold
  have hvT' := holdsCodeTail_famReg_survives x L 1 0 (by omega) (by omega) (by omega) W₀
    htapes.2.1 htapes.2.2.1 v
    (holdsCodeTail_reg_congr tm x S _ L.toWalkLayout.codeA (L.toWalkLayout.famReg 0) v hvT
      (fun p hp => (L.toWalkLayout.famReg_zero p hp).symm))
  have hvTA : HoldsCodeTail tm x S (fun q i => stepCellsF L 1 W₀ i q)
      L.toWalkLayout.codeA v :=
    holdsCodeTail_reg_congr tm x S _ (L.toWalkLayout.famReg 0) L.toWalkLayout.codeA v hvT'
      (fun p hp => L.toWalkLayout.famReg_zero p hp)
  have hu' := holdsBlocks_survives x L 1 2 (by omega) hspares (by omega) L.toWalkLayout.codeT
    (fun p hp => codeT_eq_famIdx L p hp) W₀ htapes.2.1 htapes.2.2.1 u hu
  have hprev' := holdsBlocks_survives x L 1 3 (by omega) hsp3 (by omega)
    (L.toWalkLayout.spareReg 1) (fun p hp => (L.toWalkLayout.famReg_spare 1 p hsp hp).symm) W₀
    htapes.2.1 htapes.2.2.1 prev hprev
  rw [orderTestScanner, Scanner.all_emit_run] at hverd
  have h0 := hverd ⟨0, by omega⟩
  have h1 := hverd ⟨1, by omega⟩
  have h2 := hverd ⟨2, by omega⟩
  rw [if_pos (rfl : (0 : ℕ) = 0)] at h0
  rw [if_neg (by exact (by omega : (1 : ℕ) ≠ 0)), if_pos (rfl : (1 : ℕ) = 1)] at h1
  rw [if_neg (by exact (by omega : (2 : ℕ) ≠ 0)),
    if_neg (by exact (by omega : (2 : ℕ) ≠ 1))] at h2
  have hvBlocks := holdsBlocks_of_holdsCodeTail tm x S _ L.toWalkLayout.codeA v hvTA
    ((padZeroScanner_decides tm x.length S L.toWalkLayout.codeA _).mp h2)
  refine ⟨hold, codeLt_of_ltScanner x _ (L.toWalkLayout.spareReg 1) L.toWalkLayout.codeA prev v
      hprev' hvBlocks h0,
    ne_of_notEqScanner x _ L.toWalkLayout.codeT L.toWalkLayout.codeA u v hu' hvBlocks h1,
    holdsCodeTail_congr tm x S _ _ L.toWalkLayout.codeA v hvTA (fun p hp q => hcells _ q),
    fun p hp q hq => ?_, fun p hp q hq => ?_⟩
  · show (c'.work (walkReg (L.toWalkLayout.codeT p))).cells (0 + q + 1) = _
    rw [hcells]
    exact hu' p hp q hq
  · show (c'.work (walkReg (L.toWalkLayout.codeA p))).cells (0 + q + 1) = _
    rw [hcells]
    exact hvBlocks p hp q hq

/-- **The successor stage.** It names one successor of the code the walk ended on — the choice bit
is pinned, so the two stages between them name both — and checks that the code under test is not
it. The padding check is what makes that inequality an inequality of *codes*. -/
theorem succTestStep_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (β : Bool) (g : ℕ → Bool) (s : ℕ) (cc : Fin r) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) (inp₀ out₀ : Tape)
    (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (htapes : WalkTapes (r := r) x L g s cc Wa Wt inp₀ W₀ out₀)
    (v u : Code tm.Q kk x.length S)
    (hpre : (W₀ (auxIdx jj cc)).read = Γ.one →
      (∀ p, p < kk + 3 → HoldsBits (fun q i => (W₀ (walkReg i)).cells q) 0
        (L.toWalkLayout.codeA p) (codeBlockScan tm x S v p)) ∧
      (∀ p, p < kk + 3 → HoldsBits (fun q i => (W₀ (walkReg i)).cells q) 0
        (L.toWalkLayout.codeT p) (codeBlockScan tm x S u p)) ∧
      inp₀ = ⟨max v.2.1.val 1, (Tape.init (x.map Γ.ofBool)).cells⟩ ∧
      ∀ P : SuccParams tm.Q kk, v.1 ≠ tm.qhalt → v.1 = P.q →
        P.inSym = inSymOf tm x S v →
        (∀ i, (v.2.2.1 i).2 (v.2.2.1 i).1 = P.wSym i) → v.2.2.2.2 v.2.2.2.1 = P.oSym →
        movedIdx (succTrans tm P).2.2.2.1 v.2.1.val ≤ x.length + S + 1) :
    ∃ (c' : Cfg (jj + 2 + r + 1)
        (matchStepTM L (succTestScanner tm x.length S L.toWalkLayout.par L.toWalkLayout.mv
          L.toWalkLayout.dr L.toWalkLayout.res dc L.toWalkLayout.codeA L.toWalkLayout.codeB
          L.toWalkLayout.codeT β) 1 cc).Q) (t : ℕ),
      t ≤ matchTime x L r B ∧
      (matchStepTM L (succTestScanner tm x.length S L.toWalkLayout.par L.toWalkLayout.mv
          L.toWalkLayout.dr L.toWalkLayout.res dc L.toWalkLayout.codeA L.toWalkLayout.codeB
          L.toWalkLayout.codeT β) 1 cc).reachesIn t
        ⟨(matchStepTM L (succTestScanner tm x.length S L.toWalkLayout.par L.toWalkLayout.mv
          L.toWalkLayout.dr L.toWalkLayout.res dc L.toWalkLayout.codeA L.toWalkLayout.codeB
          L.toWalkLayout.codeT β) 1 cc).qstart, inp₀, W₀, out₀⟩ c' ∧
      (matchStepTM L (succTestScanner tm x.length S L.toWalkLayout.par L.toWalkLayout.mv
          L.toWalkLayout.dr L.toWalkLayout.res dc L.toWalkLayout.codeA L.toWalkLayout.codeB
          L.toWalkLayout.codeT β) 1 cc).halted c' ∧
      WalkTapes (r := r) x L g (s + 1) cc Wa Wt c'.input c'.work c'.output ∧
      c'.input = TM.parkTape inp₀ ∧
      ((c'.work (auxIdx jj cc)).read = Γ.one →
        (W₀ (auxIdx jj cc)).read = Γ.one ∧
        v.1 ≠ tm.qhalt ∧ u ≠ succCode tm x S β v ∧
        (∀ p, p < kk + 3 → HoldsBits (fun q i => (c'.work (walkReg i)).cells q) 0
          (L.toWalkLayout.codeA p) (codeBlockScan tm x S v p)) ∧
        (∀ p, p < kk + 3 → HoldsBits (fun q i => (c'.work (walkReg i)).cells q) 0
          (L.toWalkLayout.codeT p) (codeBlockScan tm x S u p))) ∧
      (∀ n, n < L.toWalkLayout.spares → 2 + n ≠ 1 → ∀ p, p < kk + 3 → ∀ q,
        (c'.work (walkReg (L.toWalkLayout.spareReg n p))).cells q
          = (W₀ (walkReg (L.toWalkLayout.spareReg n p))).cells q) := by
  classical
  have hspares : (2 : ℕ) < 2 + L.toWalkLayout.spares := by
    have := L.toWalkLayout.spares_pos
    omega
  obtain ⟨c', t, htle, hreach, hhalt, htapes', hinp', hreg, hacc, -⟩ :=
    matchStep_run x L (succTestScanner tm x.length S L.toWalkLayout.par L.toWalkLayout.mv
      L.toWalkLayout.dr L.toWalkLayout.res dc L.toWalkLayout.codeA L.toWalkLayout.codeB
      L.toWalkLayout.codeT β) 1 (by omega) g s cc B hB1 hB Wa Wt inp₀ out₀ W₀ htapes
  have hcells : ∀ i : Fin (jj + 1), ∀ q,
      (c'.work (walkReg i)).cells q
        = checkedCells (stepCellsF L 1 W₀) L.toWalkLayout.par L.toWalkLayout.res
            (TM.parkTape inp₀).read i q := by
    intro i q
    rw [hreg i]
  have hWt : WalkTapes (r := r) x L g (s + 1) cc Wa Wt c'.input c'.work c'.output := by
    refine ⟨htapes'.1, htapes'.2.1, htapes'.2.2.1, htapes'.2.2.2.1, htapes'.2.2.2.2.1,
      htapes'.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.2.1,
      htapes'.2.2.2.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.2.2.2.1, fun p hp q => ?_⟩
    refine (htapes'.2.2.2.2.2.2.2.2.2.2 p hp q).trans ?_
    show checkedCells (stepCellsF L 1 W₀) L.toWalkLayout.par L.toWalkLayout.res
      (TM.parkTape inp₀).read (L.toWalkLayout.codeT p) q = Wt p q
    rw [checked_cell _ _ _ _ _ (L.toWalkLayout.codeT_ne_res hp),
      congrFun (stepCellsF_codeT L 1 (by omega) (by omega) W₀ htapes.2.1 htapes.2.2.1 p hp) q]
    exact htapes.2.2.2.2.2.2.2.2.2.2 p hp q
  have hspare : ∀ n, n < L.toWalkLayout.spares → 2 + n ≠ 1 → ∀ p, p < kk + 3 → ∀ q,
      (c'.work (walkReg (L.toWalkLayout.spareReg n p))).cells q
        = (W₀ (walkReg (L.toWalkLayout.spareReg n p))).cells q := by
    intro n hn hne p hp q
    rw [hcells, checked_cell _ _ _ _ _ (L.toWalkLayout.spareReg_ne_res n hn p hp)]
    exact congrFun (stepCellsF_spare L 1 (by omega) n hn (Ne.symm hne) W₀
      htapes.2.1 htapes.2.2.1 p hp) q
  refine ⟨c', t, htle, hreach, hhalt, hWt, hinp', ⟨fun hone => ?_, hspare⟩⟩
  obtain ⟨hold, hverd⟩ := hacc hone
  obtain ⟨hvB, hu, hinp, hclampIn⟩ := hpre hold
  have hvT : HoldsCodeTail tm x S (fun q i => (W₀ (walkReg i)).cells q)
      L.toWalkLayout.codeA v :=
    holdsCodeTail_of_blocks tm x S _ L.toWalkLayout.codeA v hvB
  have hvB' := holdsBlocks_survives_checked x L 1 0 (by omega) (by omega) (by omega)
    L.toWalkLayout.codeA (fun p hp => (L.toWalkLayout.famReg_zero p hp).symm) W₀
    htapes.2.1 htapes.2.2.1 (TM.parkTape inp₀).read v hvB
  have hvT' := holdsCodeTail_survives_checked x L 1 0 (by omega) (by omega) (by omega)
    L.toWalkLayout.codeA (fun p hp => (L.toWalkLayout.famReg_zero p hp).symm) W₀
    htapes.2.1 htapes.2.2.1 (TM.parkTape inp₀).read v hvT
  have hu' := holdsBlocks_survives_checked x L 1 2 (by omega) hspares (by omega)
    L.toWalkLayout.codeT (fun p hp => codeT_eq_famIdx L p hp) W₀ htapes.2.1 htapes.2.2.1
    (TM.parkTape inp₀).read u hu
  refine ⟨hold, ?_⟩
  rw [succTestScanner, Scanner.all_emit_run] at hverd
  have h0 := hverd ⟨0, by omega⟩
  have h1 := hverd ⟨1, by omega⟩
  have h2 := hverd ⟨2, by omega⟩
  rw [if_pos (rfl : (0 : ℕ) = 0)] at h0
  rw [if_neg (by exact (by omega : (1 : ℕ) ≠ 0)), if_pos (rfl : (1 : ℕ) = 1)] at h1
  rw [if_neg (by exact (by omega : (2 : ℕ) ≠ 0)),
    if_neg (by exact (by omega : (2 : ℕ) ≠ 1))] at h2
  have hr1 : ∀ p, p < L.toWalkLayout.stepBlocks → (W₀ (stepRegF L 1 p)).head = 1 :=
    fun p _ => htapes.2.2.2.1 (L.toWalkLayout.reg (L.toWalkLayout.stepIdxF 1 p)).castSucc
  obtain ⟨bitsPar, hlenPar, hparRaw⟩ := exists_bits_scratchF x L 1 (by omega) g s W₀
    htapes.2.1 htapes.2.2.1 hr1 htapes.2.2.2.2.2.2.2.2.2.1 L.toWalkLayout.parIdx
    L.toWalkLayout.par_scratch ((succParamsCodec tm.Q kk).width)
    (by
      rw [stepWidth_scratch L _ L.toWalkLayout.par_scratch, L.width_par]
      have := succParamsCodec_width_pos tm
      omega)
  have hpar := holdsBits_checked (par := L.toWalkLayout.par) (res := L.toWalkLayout.res)
    (g := (TM.parkTape inp₀).read) L.toWalkLayout.par_ne_res hparRaw
  obtain ⟨bits, hbitsLen, hbitsRaw⟩ := exists_bits_guessedF x L 1 (by omega) g s W₀
    htapes.2.1 htapes.2.2.1 hr1 htapes.2.2.2.2.2.2.2.2.2.1
  have hbits : ∀ p, p < kk + 3 → HoldsBits
      (fun q i => checkedCells (stepCellsF L 1 W₀) L.toWalkLayout.par L.toWalkLayout.res
        (TM.parkTape inp₀).read i q) 0 (L.toWalkLayout.codeB p) (bits p) := by
    intro p hp
    have h := hbitsRaw p hp
    rw [L.toWalkLayout.famReg_one p hp] at h
    exact holdsBits_checked (par := L.toWalkLayout.par) (res := L.toWalkLayout.res)
      (g := (TM.parkTape inp₀).read) (L.toWalkLayout.codeB_ne_res hp) h
  have hg : v.2.1.val ≠ 0 → (TM.parkTape inp₀).read = inSymOf tm x S v := by
    intro hne0
    rw [hinp]
    show (Tape.init (x.map Γ.ofBool)).cells (max (max v.2.1.val 1) 1) = _
    rw [show max (max v.2.1.val 1) 1 = v.2.1.val by omega]
    rfl
  have hres : TM.scanCol (checkedCells (stepCellsF L 1 W₀) L.toWalkLayout.par
        L.toWalkLayout.res (TM.parkTape inp₀).read) 1 L.toWalkLayout.res
      = Γ.ofBool (TM.inMatchVerdict gammaBits (TM.parkTape inp₀).read
        (TM.scanCol (checkedCells (stepCellsF L 1 W₀) L.toWalkLayout.par L.toWalkLayout.res
          (TM.parkTape inp₀).read) 1 L.toWalkLayout.par)
        (TM.scanCol (checkedCells (stepCellsF L 1 W₀) L.toWalkLayout.par L.toWalkLayout.res
          (TM.parkTape inp₀).read) 2 L.toWalkLayout.par)) := by
    show checkedCells (stepCellsF L 1 W₀) L.toWalkLayout.par L.toWalkLayout.res
      (TM.parkTape inp₀).read L.toWalkLayout.res 1 = _
    rw [checkedCells_res]
    show _ = Γ.ofBool (TM.inMatchVerdict gammaBits (TM.parkTape inp₀).read
      (checkedCells (stepCellsF L 1 W₀) L.toWalkLayout.par L.toWalkLayout.res
        (TM.parkTape inp₀).read L.toWalkLayout.par 1)
      (checkedCells (stepCellsF L 1 W₀) L.toWalkLayout.par L.toWalkLayout.res
        (TM.parkTape inp₀).read L.toWalkLayout.par 2))
    rw [checked_cell _ _ _ _ _ L.toWalkLayout.par_ne_res,
      checked_cell _ _ _ _ _ L.toWalkLayout.par_ne_res]
  obtain ⟨b, hbTail, hqhalt, hbSucc⟩ := succCertScanner_sound tm x S
    (TM.scanCol (checkedCells (stepCellsF L 1 W₀) L.toWalkLayout.par L.toWalkLayout.res
      (TM.parkTape inp₀).read)) L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
    L.toWalkLayout.res dc L.toWalkLayout.codeA L.toWalkLayout.codeB v _ (TM.parkTape inp₀).read
    bitsPar hlenPar hpar rfl hvT' bits hbitsLen hbits (hclampIn _) hres hg β h0
  have hbBlocks := holdsBlocks_of_holdsCodeTail tm x S _ L.toWalkLayout.codeB b hbTail
    ((padZeroScanner_decides tm x.length S L.toWalkLayout.codeB _).mp h2)
  refine ⟨hqhalt, ?_, fun p hp q hq => ?_, fun p hp q hq => ?_⟩
  · rw [← hbSucc]
    exact ne_of_notEqScanner x _ L.toWalkLayout.codeT L.toWalkLayout.codeB u b hu' hbBlocks h1
  · show (c'.work (walkReg (L.toWalkLayout.codeA p))).cells (0 + q + 1) = _
    rw [hcells]
    exact hvB' p hp q hq
  · show (c'.work (walkReg (L.toWalkLayout.codeT p))).cells (0 + q + 1) = _
    rw [hcells]
    exact hu' p hp q hq

/-- **The ordering stage without a code under test.** Used by the loop that lists members of a
round for their own sake — the P-half of the counting — where there is nothing to compare them
against but each other. -/
theorem orderOnlyStep_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (hsp : 1 < L.toWalkLayout.spares) (g : ℕ → Bool) (s : ℕ)
    (cc : Fin r) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) (inp₀ out₀ : Tape)
    (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (htapes : WalkTapes (r := r) x L g s cc Wa Wt inp₀ W₀ out₀)
    (prev v : Code tm.Q kk x.length S)
    (hpre : (W₀ (auxIdx jj cc)).read = Γ.one →
      (∀ p, p < kk + 3 → HoldsBits (fun q i => (W₀ (walkReg i)).cells q) 0
        (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S prev p)) ∧
      HoldsCodeTail tm x S (fun q i => (W₀ (walkReg i)).cells q) L.toWalkLayout.codeA v) :
    ∃ (c' : Cfg (jj + 2 + r + 1)
        (famStepTM L (TM.twoPassTM (orderOnlyScanner tm x.length S (L.toWalkLayout.spareReg 1)
          L.toWalkLayout.codeA)) 1 cc).Q) (t : ℕ),
      t ≤ famTime x L r B ∧
      (famStepTM L (TM.twoPassTM (orderOnlyScanner tm x.length S (L.toWalkLayout.spareReg 1)
          L.toWalkLayout.codeA)) 1 cc).reachesIn t
        ⟨(famStepTM L (TM.twoPassTM (orderOnlyScanner tm x.length S (L.toWalkLayout.spareReg 1)
          L.toWalkLayout.codeA)) 1 cc).qstart, inp₀, W₀, out₀⟩ c' ∧
      (famStepTM L (TM.twoPassTM (orderOnlyScanner tm x.length S (L.toWalkLayout.spareReg 1)
          L.toWalkLayout.codeA)) 1 cc).halted c' ∧
      WalkTapes (r := r) x L g (s + 1) cc Wa Wt c'.input c'.work c'.output ∧
      c'.input = TM.parkTape inp₀ ∧
      ((c'.work (auxIdx jj cc)).read = Γ.one →
        (W₀ (auxIdx jj cc)).read = Γ.one ∧ codeLt tm x S prev v ∧
        ∀ p, p < kk + 3 → HoldsBits (fun q i => (c'.work (walkReg i)).cells q) 0
          (L.toWalkLayout.codeA p) (codeBlockScan tm x S v p)) := by
  classical
  have hsp3 : (3 : ℕ) < 2 + L.toWalkLayout.spares := by omega
  obtain ⟨c', t, htle, hreach, hhalt, htapes', hinp', hreg, hacc, -⟩ :=
    famStep_run x L (orderOnlyScanner tm x.length S (L.toWalkLayout.spareReg 1)
      L.toWalkLayout.codeA) 1 (by omega) g s cc B hB1 hB Wa Wt inp₀ out₀ W₀ htapes
  have hcells : ∀ i : Fin (jj + 1), ∀ q,
      (c'.work (walkReg i)).cells q = stepCellsF L 1 W₀ i q := by
    intro i q
    rw [hreg i]
  have hWt : WalkTapes (r := r) x L g (s + 1) cc Wa Wt c'.input c'.work c'.output := by
    refine ⟨htapes'.1, htapes'.2.1, htapes'.2.2.1, htapes'.2.2.2.1, htapes'.2.2.2.2.1,
      htapes'.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.2.1,
      htapes'.2.2.2.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.2.2.2.1, fun p hp q => ?_⟩
    refine (htapes'.2.2.2.2.2.2.2.2.2.2 p hp q).trans ?_
    show stepCellsF L 1 W₀ (L.toWalkLayout.codeT p) q = Wt p q
    rw [congrFun (stepCellsF_codeT L 1 (by omega) (by omega) W₀ htapes.2.1 htapes.2.2.1 p hp) q]
    exact htapes.2.2.2.2.2.2.2.2.2.2 p hp q
  refine ⟨c', t, htle, hreach, hhalt, hWt, hinp', fun hone => ?_⟩
  obtain ⟨hold, hverd⟩ := hacc hone
  obtain ⟨hprev, hvT⟩ := hpre hold
  have hvT' := holdsCodeTail_famReg_survives x L 1 0 (by omega) (by omega) (by omega) W₀
    htapes.2.1 htapes.2.2.1 v
    (holdsCodeTail_reg_congr tm x S _ L.toWalkLayout.codeA (L.toWalkLayout.famReg 0) v hvT
      (fun p hp => (L.toWalkLayout.famReg_zero p hp).symm))
  have hvTA : HoldsCodeTail tm x S (fun q i => stepCellsF L 1 W₀ i q)
      L.toWalkLayout.codeA v :=
    holdsCodeTail_reg_congr tm x S _ (L.toWalkLayout.famReg 0) L.toWalkLayout.codeA v hvT'
      (fun p hp => L.toWalkLayout.famReg_zero p hp)
  have hprev' := holdsBlocks_survives x L 1 3 (by omega) hsp3 (by omega)
    (L.toWalkLayout.spareReg 1) (fun p hp => (L.toWalkLayout.famReg_spare 1 p hsp hp).symm) W₀
    htapes.2.1 htapes.2.2.1 prev hprev
  rw [orderOnlyScanner, Scanner.all_emit_run] at hverd
  have h0 := hverd ⟨0, by omega⟩
  have h1 := hverd ⟨1, by omega⟩
  rw [if_pos (rfl : (0 : ℕ) = 0)] at h0
  rw [if_neg (by exact (by omega : (1 : ℕ) ≠ 0))] at h1
  have hvBlocks := holdsBlocks_of_holdsCodeTail tm x S _ L.toWalkLayout.codeA v hvTA
    ((padZeroScanner_decides tm x.length S L.toWalkLayout.codeA _).mp h1)
  refine ⟨hold, codeLt_of_ltScanner x _ (L.toWalkLayout.spareReg 1) L.toWalkLayout.codeA prev v
      hprev' hvBlocks h0, fun p hp q hq => ?_⟩
  show (c'.work (walkReg (L.toWalkLayout.codeA p))).cells (0 + q + 1) = _
  rw [hcells]
  exact hvBlocks p hp q hq

/-- **The remembering stage, with no code under test.** -/
theorem copyOnlyStep_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (hsp : 1 < L.toWalkLayout.spares) (g : ℕ → Bool) (s : ℕ)
    (cc : Fin r) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) (inp₀ out₀ : Tape)
    (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (htapes : WalkTapes (r := r) x L g s cc Wa Wt inp₀ W₀ out₀)
    (v : Code tm.Q kk x.length S)
    (hpre : (W₀ (auxIdx jj cc)).read = Γ.one →
      ∀ p, p < kk + 3 → HoldsBits (fun q i => (W₀ (walkReg i)).cells q) 0
        (L.toWalkLayout.codeA p) (codeBlockScan tm x S v p)) :
    ∃ (c' : Cfg (jj + 2 + r + 1)
        (famStepTM L (TM.twoPassTM (eqScanner tm x.length S L.toWalkLayout.codeA
          (L.toWalkLayout.spareReg 1))) 3 cc).Q) (t : ℕ),
      t ≤ famTime x L r B ∧
      (famStepTM L (TM.twoPassTM (eqScanner tm x.length S L.toWalkLayout.codeA
          (L.toWalkLayout.spareReg 1))) 3 cc).reachesIn t
        ⟨(famStepTM L (TM.twoPassTM (eqScanner tm x.length S L.toWalkLayout.codeA
          (L.toWalkLayout.spareReg 1))) 3 cc).qstart, inp₀, W₀, out₀⟩ c' ∧
      (famStepTM L (TM.twoPassTM (eqScanner tm x.length S L.toWalkLayout.codeA
          (L.toWalkLayout.spareReg 1))) 3 cc).halted c' ∧
      WalkTapes (r := r) x L g (s + 1) cc Wa Wt c'.input c'.work c'.output ∧
      c'.input = TM.parkTape inp₀ ∧
      ((c'.work (auxIdx jj cc)).read = Γ.one →
        (W₀ (auxIdx jj cc)).read = Γ.one ∧
        ∀ p, p < kk + 3 → HoldsBits (fun q i => (c'.work (walkReg i)).cells q) 0
          (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S v p)) := by
  obtain ⟨c', t, htle, hreach, hhalt, htapes', hinp', hreg, hacc, -⟩ :=
    famStep_run x L (eqScanner tm x.length S L.toWalkLayout.codeA (L.toWalkLayout.spareReg 1))
      3 (by omega) g s cc B hB1 hB Wa Wt inp₀ out₀ W₀ htapes
  have hcells : ∀ i : Fin (jj + 1), ∀ q,
      (c'.work (walkReg i)).cells q = stepCellsF L 3 W₀ i q := by
    intro i q
    rw [hreg i]
  have hWt : WalkTapes (r := r) x L g (s + 1) cc Wa Wt c'.input c'.work c'.output := by
    refine ⟨htapes'.1, htapes'.2.1, htapes'.2.2.1, htapes'.2.2.2.1, htapes'.2.2.2.2.1,
      htapes'.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.2.1,
      htapes'.2.2.2.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.2.2.2.1, fun p hp q => ?_⟩
    refine (htapes'.2.2.2.2.2.2.2.2.2.2 p hp q).trans ?_
    show stepCellsF L 3 W₀ (L.toWalkLayout.codeT p) q = Wt p q
    rw [congrFun (stepCellsF_codeT L 3 (by omega) (by omega) W₀ htapes.2.1 htapes.2.2.1 p hp) q]
    exact htapes.2.2.2.2.2.2.2.2.2.2 p hp q
  refine ⟨c', t, htle, hreach, hhalt, hWt, hinp', fun hone => ?_⟩
  obtain ⟨hold, hverd⟩ := hacc hone
  have hA := holdsBlocks_survives x L 3 0 (by omega) (by omega) (by omega) L.toWalkLayout.codeA
    (fun p hp => (L.toWalkLayout.famReg_zero p hp).symm) W₀ htapes.2.1 htapes.2.2.1 v
    (hpre hold)
  refine ⟨hold, fun p hp q hq => ?_⟩
  show (c'.work (walkReg (L.toWalkLayout.spareReg 1 p))).cells (0 + q + 1) = _
  rw [hcells]
  exact eqScanner_forces tm x S (TM.scanCol (stepCellsF L 3 W₀)) L.toWalkLayout.codeA
    (L.toWalkLayout.spareReg 1) v hA hverd p hp q hq

/-! ## The four checking stages, in sequence -/

/-- The four stages that follow the walk: order, the two successors, and remember. -/
noncomputable def innerTailTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (cc : Fin rr) :
    TM (jj + 2 + rr + 1) :=
  TM.seqTM
    (famStepTM L (TM.twoPassTM (orderTestScanner tm x.length S (L.toWalkLayout.spareReg 1)
      L.toWalkLayout.codeA L.toWalkLayout.codeT)) 1 cc)
    (TM.seqTM
      (matchStepTM L (succTestScanner tm x.length S L.toWalkLayout.par L.toWalkLayout.mv
        L.toWalkLayout.dr L.toWalkLayout.res dc L.toWalkLayout.codeA L.toWalkLayout.codeB
        L.toWalkLayout.codeT false) 1 cc)
      (TM.seqTM
        (matchStepTM L (succTestScanner tm x.length S L.toWalkLayout.par L.toWalkLayout.mv
          L.toWalkLayout.dr L.toWalkLayout.res dc L.toWalkLayout.codeA L.toWalkLayout.codeB
          L.toWalkLayout.codeT true) 1 cc)
        (famStepTM L (TM.twoPassTM (eqScanner tm x.length S L.toWalkLayout.codeA
          (L.toWalkLayout.spareReg 1))) 3 cc)))

/-- The tail's advancing states. -/
noncomputable def innerTailAdv {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (cc : Fin rr) :
    (innerTailTM x L dc cc).Q → Bool :=
  TM.seqAdv
    (famStepAdv L (TM.twoPassTM (orderTestScanner tm x.length S (L.toWalkLayout.spareReg 1)
      L.toWalkLayout.codeA L.toWalkLayout.codeT)) 1 cc)
    (TM.seqAdv
      (matchStepAdv L (succTestScanner tm x.length S L.toWalkLayout.par L.toWalkLayout.mv
        L.toWalkLayout.dr L.toWalkLayout.res dc L.toWalkLayout.codeA L.toWalkLayout.codeB
        L.toWalkLayout.codeT false) 1 cc)
      (TM.seqAdv
        (matchStepAdv L (succTestScanner tm x.length S L.toWalkLayout.par L.toWalkLayout.mv
          L.toWalkLayout.dr L.toWalkLayout.res dc L.toWalkLayout.codeA L.toWalkLayout.codeB
          L.toWalkLayout.codeT true) 1 cc)
        (famStepAdv L (TM.twoPassTM (eqScanner tm x.length S L.toWalkLayout.codeA
          (L.toWalkLayout.spareReg 1))) 3 cc)))

/-- **The tail respects the guess protocol.** -/
theorem guessProtocol_innerTailTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (cc : Fin rr) :
    TM.GuessProtocol (innerTailTM x L dc cc) (innerTailAdv x L dc cc) :=
  TM.guessProtocol_seqTM (guessProtocol_famStepTM L _ 1 cc)
    (TM.guessProtocol_seqTM (guessProtocol_matchStepTM L _ 1 cc)
      (TM.guessProtocol_seqTM (guessProtocol_matchStepTM L _ 1 cc)
        (guessProtocol_famStepTM L _ 3 cc)))

/-- **What the four stages establish.** If the accumulator survives all four, the code the walk
ended on is above the one the loop remembered, is not the code under test and does not step to it
under either choice, and the loop now remembers it instead. -/
theorem innerTail_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (hsp : 1 < L.toWalkLayout.spares) (g : ℕ → Bool) (s : ℕ)
    (cc : Fin r) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) (inp₀ out₀ : Tape)
    (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (htapes : WalkTapes (r := r) x L g s cc Wa Wt inp₀ W₀ out₀)
    (prev v u : Code tm.Q kk x.length S)
    (hpre : (W₀ (auxIdx jj cc)).read = Γ.one →
      (∀ p, p < kk + 3 → HoldsBits (fun q i => (W₀ (walkReg i)).cells q) 0
        (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S prev p)) ∧
      HoldsCodeTail tm x S (fun q i => (W₀ (walkReg i)).cells q) L.toWalkLayout.codeA v ∧
      (∀ p, p < kk + 3 → HoldsBits (fun q i => (W₀ (walkReg i)).cells q) 0
        (L.toWalkLayout.codeT p) (codeBlockScan tm x S u p)) ∧
      inp₀ = ⟨max v.2.1.val 1, (Tape.init (x.map Γ.ofBool)).cells⟩ ∧
      ∀ P : SuccParams tm.Q kk, v.1 ≠ tm.qhalt → v.1 = P.q →
        P.inSym = inSymOf tm x S v →
        (∀ i, (v.2.2.1 i).2 (v.2.2.1 i).1 = P.wSym i) → v.2.2.2.2 v.2.2.2.1 = P.oSym →
        movedIdx (succTrans tm P).2.2.2.1 v.2.1.val ≤ x.length + S + 1) :
    ∃ (c : Cfg (jj + 2 + r + 1) (innerTailTM x L dc cc).Q) (t : ℕ),
      t ≤ famTime x L r B + 1 + (matchTime x L r B + 1 +
        (matchTime x L r B + 1 + famTime x L r B)) ∧
      (innerTailTM x L dc cc).reachesIn t
        ⟨(innerTailTM x L dc cc).qstart, inp₀, W₀, out₀⟩ c ∧
      (innerTailTM x L dc cc).halted c ∧
      WalkTapes (r := r) x L g (s + 1 + 1 + 1 + 1) cc Wa Wt c.input c.work c.output ∧
      ((c.work (auxIdx jj cc)).read = Γ.one →
        (W₀ (auxIdx jj cc)).read = Γ.one ∧ codeLt tm x S prev v ∧ u ≠ v ∧
        u ≠ succCode tm x S false v ∧ u ≠ succCode tm x S true v ∧
        (∀ p, p < kk + 3 → HoldsBits (fun q i => (c.work (walkReg i)).cells q) 0
          (L.toWalkLayout.codeT p) (codeBlockScan tm x S u p)) ∧
        ∀ p, p < kk + 3 → HoldsBits (fun q i => (c.work (walkReg i)).cells q) 0
          (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S v p)) ∧
      (∀ n, n < L.toWalkLayout.spares → n ≠ 1 → ∀ p, p < kk + 3 → ∀ q,
        (c.work (walkReg (L.toWalkLayout.spareReg n p))).cells q
          = (W₀ (walkReg (L.toWalkLayout.spareReg n p))).cells q) := by
  classical
  -- stage one: the order check
  obtain ⟨c₁, t₁, ht₁, hreach₁, hhalt₁, htapes₁, hinp₁, hacc₁, hsp₁⟩ :=
    orderStep_run x L hsp g s cc B hB1 hB Wa Wt inp₀ out₀ W₀ htapes prev v u
      (fun h => ⟨(hpre h).1, (hpre h).2.1, (hpre h).2.2.1⟩)
  obtain ⟨hfix₁i, hfix₁w, hfix₁o⟩ :=
    walkTapes_transition_eq x L g (s + 1) cc Wa Wt c₁.input c₁.work c₁.output htapes₁
  have hinpv : (W₀ (auxIdx jj cc)).read = Γ.one →
      c₁.input = ⟨max v.2.1.val 1, (Tape.init (x.map Γ.ofBool)).cells⟩ := by
    intro h
    rw [hinp₁, (hpre h).2.2.2.1]
    exact Tape.ext (by
      show max (max v.2.1.val 1) 1 = max v.2.1.val 1
      omega) rfl
  -- stage two: the successor for choice `false`
  obtain ⟨c₂, t₂, ht₂, hreach₂, hhalt₂, htapes₂, hinp₂, hacc₂, hsp₂⟩ :=
    succTestStep_run x L dc false g (s + 1) cc B hB1 hB Wa Wt c₁.input c₁.output c₁.work
      htapes₁ v u (fun h => by
        obtain ⟨hold, -, -, -, hu, hvB⟩ := hacc₁ h
        exact ⟨hvB, hu, hinpv hold, (hpre hold).2.2.2.2⟩)
  obtain ⟨hfix₂i, hfix₂w, hfix₂o⟩ :=
    walkTapes_transition_eq x L g (s + 1 + 1) cc Wa Wt c₂.input c₂.work c₂.output htapes₂
  have hinpv₂ : (c₁.work (auxIdx jj cc)).read = Γ.one →
      c₂.input = ⟨max v.2.1.val 1, (Tape.init (x.map Γ.ofBool)).cells⟩ := by
    intro h
    rw [hinp₂, hinpv (hacc₁ h).1]
    exact Tape.ext (by
      show max (max v.2.1.val 1) 1 = max v.2.1.val 1
      omega) rfl
  -- stage three: the successor for choice `true`
  obtain ⟨c₃, t₃, ht₃, hreach₃, hhalt₃, htapes₃, hinp₃, hacc₃, hsp₃⟩ :=
    succTestStep_run x L dc true g (s + 1 + 1) cc B hB1 hB Wa Wt c₂.input c₂.output c₂.work
      htapes₂ v u (fun h => by
        obtain ⟨hold, -, -, hvB, hu⟩ := hacc₂ h
        obtain ⟨hold₁, -, -, -, -, -⟩ := hacc₁ hold
        exact ⟨hvB, hu, hinpv₂ hold, (hpre hold₁).2.2.2.2⟩)
  obtain ⟨hfix₃i, hfix₃w, hfix₃o⟩ :=
    walkTapes_transition_eq x L g (s + 1 + 1 + 1) cc Wa Wt c₃.input c₃.work c₃.output htapes₃
  -- stage four: remember the code
  obtain ⟨c₄, t₄, ht₄, hreach₄, hhalt₄, htapes₄, hinp₄, hacc₄, hsp₄⟩ :=
    copyStep_run x L hsp g (s + 1 + 1 + 1) cc B hB1 hB Wa Wt c₃.input c₃.output c₃.work
      htapes₃ v u (fun h => by
        obtain ⟨-, -, -, hvBlocks, hu⟩ := hacc₃ h
        exact ⟨hvBlocks, hu⟩)
  -- chain the four runs
  obtain ⟨c₃₄, hreach₃₄, hhalt₃₄, hin₃₄, hwork₃₄, hout₃₄⟩ :=
    seqTM_run_of_runs _ _ c₂.input c₂.output c₂.work hreach₃ hhalt₃
      (by rw [hfix₃i, hfix₃w, hfix₃o]; exact hreach₄) hhalt₄
  obtain ⟨c₂₄, hreach₂₄, hhalt₂₄, hin₂₄, hwork₂₄, hout₂₄⟩ :=
    seqTM_run_of_runs _ _ c₁.input c₁.output c₁.work hreach₂ hhalt₂
      (by rw [hfix₂i, hfix₂w, hfix₂o]; exact hreach₃₄) hhalt₃₄
  obtain ⟨c, hreach, hhalt, hin, hwork, hout⟩ :=
    seqTM_run_of_runs _ _ inp₀ out₀ W₀ hreach₁ hhalt₁
      (by rw [hfix₁i, hfix₁w, hfix₁o]; exact hreach₂₄) hhalt₂₄
  have hworkc : c.work = c₄.work := by rw [hwork, hwork₂₄, hwork₃₄]
  have hinc : c.input = c₄.input := by rw [hin, hin₂₄, hin₃₄]
  have houtc : c.output = c₄.output := by rw [hout, hout₂₄, hout₃₄]
  have hspare : ∀ n, n < L.toWalkLayout.spares → n ≠ 1 → ∀ p, p < kk + 3 → ∀ q,
      (c.work (walkReg (L.toWalkLayout.spareReg n p))).cells q
        = (W₀ (walkReg (L.toWalkLayout.spareReg n p))).cells q := by
    intro n hn hne p hp q
    rw [hworkc, hsp₄ n hn (by omega) p hp q, hsp₃ n hn (by omega) p hp q,
      hsp₂ n hn (by omega) p hp q, hsp₁ n hn (by omega) p hp q]
  refine ⟨c, t₁ + 1 + (t₂ + 1 + (t₃ + 1 + t₄)), by omega, hreach, hhalt, ?_,
    ⟨fun hone => ?_, hspare⟩⟩
  · rw [hinc, hworkc, houtc]
    exact htapes₄
  · rw [hworkc] at hone ⊢
    obtain ⟨hold₃, hu₄, hv₄⟩ := hacc₄ hone
    obtain ⟨hold₂, -, hne₃, -, -⟩ := hacc₃ hold₃
    obtain ⟨hold₁, -, hne₂, -, -⟩ := hacc₂ hold₂
    obtain ⟨hold₀, hlt, hnev, -, -, -⟩ := hacc₁ hold₁
    exact ⟨hold₀, hlt, hnev, hne₂, hne₃, hu₄, hv₄⟩

/-! ## The four stages that produce a member of the round -/

/-- Rewind, clear the counter, pin the first tuple, and walk. -/
noncomputable def innerHeadTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (a₀ : Code tm.Q kk x.length S)
    (cc wcnt wlim : Fin rr) : TM (jj + 2 + rr + 1) :=
  TM.seqTM TM.rewindInputTM
    (TM.seqTM (TM.resetBinaryWorkTM (auxIdx jj wcnt))
      (TM.seqTM (pinStepTM x L a₀ cc)
        (walkLoopTM rr tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
          L.toWalkLayout.res L.toWalkLayout.cnt L.toWalkLayout.cnt' dc
          L.toWalkLayout.codeA L.toWalkLayout.codeB (stepReg (r := rr) L false)
          (stepReg (r := rr) L true) (stepWidth L) L.toWalkLayout.stepBlocks wc
          (stepTargets jj rr) (auxIdx jj cc) (auxIdx jj wcnt) (auxIdx jj wlim))))

/-- The head's advancing states. -/
noncomputable def innerHeadAdv {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (a₀ : Code tm.Q kk x.length S)
    (cc wcnt wlim : Fin rr) : (innerHeadTM x L dc a₀ cc wcnt wlim).Q → Bool :=
  TM.seqAdv (fun _ => false)
    (TM.seqAdv (TM.seqAdv (fun _ => false) (TM.seqAdv (fun _ => false) (fun _ => false)))
      (TM.seqAdv (pinStepAdv x L a₀ cc)
        (TM.binaryForAdv
          (walkPairAdv rr tm x.length S L.toWalkLayout.par L.toWalkLayout.mv
            L.toWalkLayout.dr L.toWalkLayout.res L.toWalkLayout.cnt L.toWalkLayout.cnt' wc dc
            L.toWalkLayout.codeA L.toWalkLayout.codeB (stepReg (r := rr) L false)
            (stepReg (r := rr) L true) (stepWidth L) L.toWalkLayout.stepBlocks
            (stepTargets jj rr) (auxIdx jj cc))
          (auxIdx jj wcnt) (auxIdx jj wlim))))

/-- **The head respects the guess protocol.** -/
theorem guessProtocol_innerHeadTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (a₀ : Code tm.Q kk x.length S)
    (cc wcnt wlim : Fin rr) :
    TM.GuessProtocol (innerHeadTM x L dc a₀ cc wcnt wlim)
      (innerHeadAdv x L dc a₀ cc wcnt wlim) :=
  TM.guessProtocol_seqTM TM.guessProtocol_rewindInputTM
    (TM.guessProtocol_seqTM (TM.guessProtocol_resetBinaryWorkTM _ (auxIdx_ne_last wcnt))
      (TM.guessProtocol_seqTM (guessProtocol_pinStepTM x L a₀ cc)
        (guessProtocol_walkLoopTM rr tm x.length S L.toWalkLayout.par L.toWalkLayout.mv
          L.toWalkLayout.dr L.toWalkLayout.res L.toWalkLayout.cnt L.toWalkLayout.cnt' dc
          L.toWalkLayout.codeA L.toWalkLayout.codeB (stepReg (r := rr) L false)
          (stepReg (r := rr) L true) (stepWidth L) L.toWalkLayout.stepBlocks wc
          (stepTargets jj rr) (auxIdx jj cc) (auxIdx jj wcnt) (auxIdx jj wlim)
          (auxIdx_ne_last cc) (auxIdx_ne_last wcnt) (auxIdx_ne_last wlim))))

/-- **What those four stages establish.** If the accumulator survives, the first tuple holds a
code the search reaches in `2 * N` rounds, and the machine's own input head is where that code
says the simulated one is. -/
theorem innerHead_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (g : ℕ → Bool) (s : ℕ) (cc wcnt wlim : Fin r)
    (hcnt : wcnt ≠ cc) (hlim : wlim ≠ cc) (hcl : wcnt ≠ wlim) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hspace : ∀ c, tm.ReachesCfg (tm.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hwin : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x S c)
    (hwc : wc ≤ walkScanLen tm x.length S) (N : ℕ)
    (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) (inp₀ out₀ : Tape)
    (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (htapes : WalkTapes (r := r) x L g s cc Wa Wt inp₀ W₀ out₀)
    (Binp : ℕ) (hbnd : inp₀.head ≤ Binp) (bits : List Bool) (headBound : ℕ)
    (hbits : (W₀ (auxIdx jj wcnt)).HasBinaryContent bits)
    (hhead : (W₀ (auxIdx jj wcnt)).head ≤ headBound)
    (hlimN : (Wa wlim).HasBinaryNat N) :
    ∃ (c : Cfg (jj + 2 + r + 1)
        (innerHeadTM x L dc (cfgCode x.length S (tm.initCfg x)) cc wcnt wlim).Q) (t : ℕ),
      (innerHeadTM x L dc (cfgCode x.length S (tm.initCfg x)) cc wcnt wlim).reachesIn t
        ⟨(innerHeadTM x L dc (cfgCode x.length S (tm.initCfg x)) cc wcnt wlim).qstart,
          inp₀, W₀, out₀⟩ c ∧
      (innerHeadTM x L dc (cfgCode x.length S (tm.initCfg x)) cc wcnt wlim).halted c ∧
      WalkTapes (r := r) x L g (s + 1 + 2 * N) cc (fun c' => c.work (auxIdx jj c'))
        (fun p q => (c.work (walkReg (L.toWalkLayout.codeT p))).cells q)
        c.input c.work c.output ∧
      WalkKept x L cc wcnt (Function.update Wa wcnt ((Tape.init ([] : List Γ)).move Dir3.right))
        (W₀ (auxIdx jj cc)).read
        (fun n p q => (W₀ (walkReg (L.toWalkLayout.spareReg n p))).cells q)
        c.input c.work c.output ∧
      (c.work (auxIdx jj wcnt)).HasBinaryNat N ∧
      ((c.work (auxIdx jj cc)).read = Γ.one →
        ∃ v : Code tm.Q kk x.length S,
          v ∈ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N) ∧
          HoldsCodeTail tm x S (fun q i => (c.work (walkReg i)).cells q)
            L.toWalkLayout.codeA v ∧
          c.input = ⟨max v.2.1.val 1, (Tape.init (x.map Γ.ofBool)).cells⟩) := by
  classical
  set a₀ := cfgCode x.length S (tm.initCfg x) with ha₀
  -- rewind
  have hinpSI : inp₀.StartInvariant := by
    refine ⟨?_, fun q hq => ?_⟩
    · rw [show inp₀.cells 0 = (Tape.init (x.map Γ.ofBool)).cells 0 from
        congrFun htapes.2.2.2.2.2.1 0]
      exact Tape.init_cells_zero _
    · rw [show inp₀.cells q = (Tape.init (x.map Γ.ofBool)).cells q from
        congrFun htapes.2.2.2.2.2.1 q]
      exact Tape.init_ofBool_cells_ne_start x q hq
  obtain ⟨c₁, t₁, -, hreach₁, hhalt₁, hhead₁, hcells₁, hwork₁, hout₁⟩ :=
    rewind_tapes_eq Binp inp₀ out₀ W₀ hinpSI.1 (fun q hq => hinpSI.2 q hq) hbnd
      (htapes.2.2.2.2.2.2.2.1.read_ne_start htapes.2.2.2.2.2.2.2.2.1)
      htapes.2.2.2.2.2.2.2.2.1
      (fun i => ⟨(htapes.2.1 i).read_ne_start (htapes.2.2.1 i), htapes.2.2.1 i⟩)
  have htapes₁ : WalkTapes (r := r) x L g s cc Wa Wt c₁.input c₁.work c₁.output := by
    rw [hwork₁, hout₁]
    exact ⟨htapes.1, htapes.2.1, htapes.2.2.1, htapes.2.2.2.1, htapes.2.2.2.2.1,
      by rw [hcells₁]; exact htapes.2.2.2.2.2.1, by rw [hhead₁],
      htapes.2.2.2.2.2.2.2.1, htapes.2.2.2.2.2.2.2.2.1, htapes.2.2.2.2.2.2.2.2.2.1,
      htapes.2.2.2.2.2.2.2.2.2.2⟩
  obtain ⟨hfix₁i, hfix₁w, hfix₁o⟩ :=
    walkTapes_transition_eq x L g s cc Wa Wt c₁.input c₁.work c₁.output htapes₁
  -- clear the walk's counter
  have hbits₁ : (c₁.work (auxIdx jj wcnt)).HasBinaryContent bits := by
    rw [htapes₁.1 wcnt hcnt, ← htapes.1 wcnt hcnt]
    exact hbits
  have hhead₁' : (c₁.work (auxIdx jj wcnt)).head ≤ headBound := by
    rw [htapes₁.1 wcnt hcnt, ← htapes.1 wcnt hcnt]
    exact hhead
  obtain ⟨c₂, t₂, -, hreach₂, hhalt₂, htapes₂, hinp₂, hout₂, hwork₂⟩ :=
    walkTapes_reset x L g s cc wcnt hcnt Wa Wt bits headBound c₁.input c₁.output c₁.work
      htapes₁ hbits₁ hhead₁' c₁.input c₁.work c₁.output ⟨rfl, rfl, rfl⟩
  obtain ⟨hfix₂i, hfix₂w, hfix₂o⟩ :=
    walkTapes_transition_eq x L g s cc _ Wt c₂.input c₂.work c₂.output htapes₂
  -- pin the first tuple
  obtain ⟨c₃, t₃, -, hreach₃, hhalt₃, htapes₃, hinp₃, hspare₃, hacc₃⟩ :=
    pinStep_run x L a₀ g s cc B hB1 hB _ Wt c₂.input c₂.output c₂.work htapes₂
  obtain ⟨hfix₃i, hfix₃w, hfix₃o⟩ :=
    walkTapes_transition_eq x L g (s + 1) cc _ Wt c₃.input c₃.work c₃.output htapes₃
  -- the walk, run against the tail of the guess stream
  set off := TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks with hoff
  set g' : ℕ → Bool := fun q => g ((s + 1) * off + q) with hg'
  have hshift : (fun q => g' (0 * off + q)) = fun q => g ((s + 1) * off + q) := by
    funext q
    show g ((s + 1) * off + (0 * off + q)) = _
    congr 1
    omega
  have htapes₃₀ : WalkTapes (r := r) x L g' 0 cc (fun c => c₃.work (auxIdx jj c))
      (fun p q => (c₃.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      c₃.input c₃.work c₃.output := by
    refine ⟨fun c _ => rfl, htapes₃.2.1, htapes₃.2.2.1, htapes₃.2.2.2.1, htapes₃.2.2.2.2.1,
      htapes₃.2.2.2.2.2.1, htapes₃.2.2.2.2.2.2.1, htapes₃.2.2.2.2.2.2.2.1,
      htapes₃.2.2.2.2.2.2.2.2.1, ?_, fun p hp q => rfl⟩
    rw [hshift]
    exact htapes₃.2.2.2.2.2.2.2.2.2.1
  have hcnt0 : (c₃.work (auxIdx jj wcnt)).HasBinaryNat 0 := by
    rw [htapes₃.1 wcnt hcnt, Function.update_self]
    simpa using Tape.init_move_right_hasBinaryNat 0
  have hlim0 : (c₃.work (auxIdx jj wlim)).HasBinaryNat N := by
    rw [htapes₃.1 wlim hlim, Function.update_of_ne (fun h => hcl h.symm)]
    exact hlimN
  have hframe0 := binaryForFrame_walkChainP_init x L g' cc wcnt wlim N c₃.input c₃.work
    c₃.output htapes₃₀ (fun hone => (hacc₃.1 hone).2)
    (fun hone => by
      rw [hinp₃, hinp₂]
      show max c₁.input.head 1 = max (cfgCode x.length S (tm.initCfg x)).2.1.val 1
      rw [hhead₁]
      rfl)
    hcnt0 hlim0
  have hkept₃ : WalkKept x L cc wcnt
      (Function.update Wa wcnt ((Tape.init ([] : List Γ)).move Dir3.right))
      (W₀ (auxIdx jj cc)).read
      (fun n p q => (W₀ (walkReg (L.toWalkLayout.spareReg n p))).cells q)
      c₃.input c₃.work c₃.output := by
    refine ⟨fun c hc _ => htapes₃.1 c hc, fun hone => ?_, fun n hn p hp q => ?_⟩
    · have h₂ := (hacc₃.1 hone).1
      rw [hwork₂, Function.update_of_ne (auxIdx_injective (fun h => hcnt h.symm)), hwork₁] at h₂
      exact h₂
    · rw [hspare₃ n hn p hp q, hwork₂,
        Function.update_of_ne (walkReg_ne_auxIdx _ wcnt), hwork₁]
  obtain ⟨c₄, t₄, -, hreach₄, hhalt₄, hframeN⟩ :=
    walkLoop_kept x L dc g' cc wcnt wlim hcnt hlim hcl B hspace hwin hB1 hB hwc
      (fun p q => (c₃.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      (Function.update Wa wcnt ((Tape.init ([] : List Γ)).move Dir3.right))
      (W₀ (auxIdx jj cc)).read
      (fun n p q => (W₀ (walkReg (L.toWalkLayout.spareReg n p))).cells q)
      N c₃.input c₃.work c₃.output ⟨⟨hframe0.1, hkept₃⟩, hframe0.2⟩
  -- chain the four runs
  obtain ⟨c₃₄, hreach₃₄, hhalt₃₄, hin₃₄, hwork₃₄, hout₃₄⟩ :=
    seqTM_run_of_runs _ _ c₂.input c₂.output c₂.work hreach₃ hhalt₃
      (by rw [hfix₃i, hfix₃w, hfix₃o]; exact hreach₄) hhalt₄
  obtain ⟨c₂₄, hreach₂₄, hhalt₂₄, hin₂₄, hwork₂₄, hout₂₄⟩ :=
    seqTM_run_of_runs _ _ c₁.input c₁.output c₁.work hreach₂ hhalt₂
      (by rw [hfix₂i, hfix₂w, hfix₂o]; exact hreach₃₄) hhalt₃₄
  obtain ⟨c, hreach, hhalt, hin, hwork, hout⟩ :=
    seqTM_run_of_runs _ _ inp₀ out₀ W₀ hreach₁ hhalt₁
      (by rw [hfix₁i, hfix₁w, hfix₁o]; exact hreach₂₄) hhalt₂₄
  have hworkc : c.work = c₄.work := by rw [hwork, hwork₂₄, hwork₃₄]
  have hinc : c.input = c₄.input := by rw [hin, hin₂₄, hin₃₄]
  have houtc : c.output = c₄.output := by rw [hout, hout₂₄, hout₃₄]
  refine ⟨c, t₁ + 1 + (t₂ + 1 + (t₃ + 1 + t₄)), hreach, hhalt, ?_, ?_, ?_, fun hone => ?_⟩
  · rw [hinc, hworkc, houtc]
    have h := hframeN.1.1.1
    refine ⟨fun c' _ => rfl, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
      h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, ?_, fun p hp q => rfl⟩
    · have hg := h.2.2.2.2.2.2.2.2.2.1
      have hfun : (fun q => g' (2 * N * off + q))
          = fun q => g ((s + 1 + 2 * N) * off + q) := by
        funext q
        show g ((s + 1) * off + (2 * N * off + q)) = _
        congr 1
        ring
      rw [hfun] at hg
      exact hg
  · rw [hinc, hworkc, houtc]
    exact hframeN.1.2
  · rw [hworkc]
    exact hframeN.2.1
  · rw [hworkc] at hone ⊢
    obtain ⟨a, ha, hinv⟩ := hframeN.1.1.2 hone
    refine ⟨a, ha, hinv.2.2.2.2.1, ?_⟩
    rw [hinc]
    exact hinv.2.2.2.2.2.1

/-! ## The whole iteration -/

/-- **One entry of the inner counting loop**: produce a member of the round, then check it. -/
noncomputable def innerBodyTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (a₀ : Code tm.Q kk x.length S)
    (cc wcnt wlim : Fin rr) : TM (jj + 2 + rr + 1) :=
  TM.seqTM (innerHeadTM x L dc a₀ cc wcnt wlim) (innerTailTM x L dc cc)

/-- Its advancing states. -/
noncomputable def innerBodyAdv {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (a₀ : Code tm.Q kk x.length S)
    (cc wcnt wlim : Fin rr) : (innerBodyTM x L dc a₀ cc wcnt wlim).Q → Bool :=
  TM.seqAdv (innerHeadAdv x L dc a₀ cc wcnt wlim) (innerTailAdv x L dc cc)

/-- **The whole iteration respects the guess protocol**, so it may sit inside a nondeterministic
assembly. -/
theorem guessProtocol_innerBodyTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (a₀ : Code tm.Q kk x.length S)
    (cc wcnt wlim : Fin rr) :
    TM.GuessProtocol (innerBodyTM x L dc a₀ cc wcnt wlim)
      (innerBodyAdv x L dc a₀ cc wcnt wlim) :=
  TM.guessProtocol_seqTM (guessProtocol_innerHeadTM x L dc a₀ cc wcnt wlim)
    (guessProtocol_innerTailTM x L dc cc)


/-- **What one iteration of the inner loop establishes.** If the accumulator survives it, the
machine has met a member of the round that is above the one it remembered, is not the code under
test, and does not step to it under either choice — and it now remembers that member instead. -/
theorem innerBody_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (hsp : 1 < L.toWalkLayout.spares) (g : ℕ → Bool) (s : ℕ)
    (cc wcnt wlim : Fin r) (hcnt : wcnt ≠ cc) (hlim : wlim ≠ cc) (hcl : wcnt ≠ wlim)
    (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hspace : ∀ c, tm.ReachesCfg (tm.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hwin : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x S c)
    (hwc : wc ≤ walkScanLen tm x.length S) (N : ℕ)
    (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) (inp₀ out₀ : Tape)
    (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (htapes : WalkTapes (r := r) x L g s cc Wa Wt inp₀ W₀ out₀)
    (Binp : ℕ) (hbnd : inp₀.head ≤ Binp) (bits : List Bool) (headBound : ℕ)
    (hbits : (W₀ (auxIdx jj wcnt)).HasBinaryContent bits)
    (hhead : (W₀ (auxIdx jj wcnt)).head ≤ headBound)
    (hlimN : (Wa wlim).HasBinaryNat N)
    (prev u : Code tm.Q kk x.length S)
    (hpre : (W₀ (auxIdx jj cc)).read = Γ.one →
      (∀ p, p < kk + 3 → HoldsBits (fun q i => (W₀ (walkReg i)).cells q) 0
        (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S prev p)) ∧
      ∀ p, p < kk + 3 → HoldsBits (fun q i => (W₀ (walkReg i)).cells q) 0
        (L.toWalkLayout.codeT p) (codeBlockScan tm x S u p)) :
    ∃ (c : Cfg (jj + 2 + r + 1)
        (innerBodyTM x L dc (cfgCode x.length S (tm.initCfg x)) cc wcnt wlim).Q) (t : ℕ),
      (innerBodyTM x L dc (cfgCode x.length S (tm.initCfg x)) cc wcnt wlim).reachesIn t
        ⟨(innerBodyTM x L dc (cfgCode x.length S (tm.initCfg x)) cc wcnt wlim).qstart,
          inp₀, W₀, out₀⟩ c ∧
      (innerBodyTM x L dc (cfgCode x.length S (tm.initCfg x)) cc wcnt wlim).halted c ∧
      WalkTapes (r := r) x L g (s + 1 + 2 * N + 1 + 1 + 1 + 1) cc
        (fun c' => c.work (auxIdx jj c'))
        (fun p q => (c.work (walkReg (L.toWalkLayout.codeT p))).cells q)
        c.input c.work c.output ∧
      (∀ c' , c' ≠ cc → c' ≠ wcnt →
        c.work (auxIdx jj c')
          = Function.update Wa wcnt ((Tape.init ([] : List Γ)).move Dir3.right) c') ∧
      (c.work (auxIdx jj wcnt)).HasBinaryNat N ∧
      ((c.work (auxIdx jj cc)).read = Γ.one →
        (W₀ (auxIdx jj cc)).read = Γ.one ∧
        ∃ v : Code tm.Q kk x.length S,
          v ∈ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N) ∧
          codeLt tm x S prev v ∧ u ≠ v ∧
          u ≠ succCode tm x S false v ∧ u ≠ succCode tm x S true v ∧
          (∀ p, p < kk + 3 → HoldsBits (fun q i => (c.work (walkReg i)).cells q) 0
            (L.toWalkLayout.codeT p) (codeBlockScan tm x S u p)) ∧
          ∀ p, p < kk + 3 → HoldsBits (fun q i => (c.work (walkReg i)).cells q) 0
            (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S v p)) ∧
      (∀ n, n < L.toWalkLayout.spares → n ≠ 1 → ∀ p, p < kk + 3 → ∀ q,
        (c.work (walkReg (L.toWalkLayout.spareReg n p))).cells q
          = (W₀ (walkReg (L.toWalkLayout.spareReg n p))).cells q) := by
  classical
  obtain ⟨cH, tH, hreachH, hhaltH, htapesH, hkeptH, hwcntH, haccH⟩ :=
    innerHead_run x L dc g s cc wcnt wlim hcnt hlim hcl B hB1 hB hspace hwin hwc N Wa Wt
      inp₀ out₀ W₀ htapes Binp hbnd bits headBound hbits hhead hlimN
  obtain ⟨hfixI, hfixW, hfixO⟩ :=
    walkTapes_transition_eq x L g (s + 1 + 2 * N) cc (fun c' => cH.work (auxIdx jj c'))
      (fun p q => (cH.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      cH.input cH.work cH.output htapesH
  set v₀ : Code tm.Q kk x.length S :=
    if h : (cH.work (auxIdx jj cc)).read = Γ.one then (haccH h).choose
    else cfgCode x.length S (tm.initCfg x) with hv₀def
  have hv₀spec : ∀ h : (cH.work (auxIdx jj cc)).read = Γ.one,
      v₀ ∈ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N) ∧
      HoldsCodeTail tm x S (fun q i => (cH.work (walkReg i)).cells q) L.toWalkLayout.codeA v₀ ∧
      cH.input = ⟨max v₀.2.1.val 1, (Tape.init (x.map Γ.ofBool)).cells⟩ := by
    intro h
    rw [hv₀def, dif_pos h]
    exact (haccH h).choose_spec
  obtain ⟨cT, tT, -, hreachT, hhaltT, htapesT, haccT, hspT⟩ :=
    innerTail_run x L dc hsp g (s + 1 + 2 * N) cc B hB1 hB (fun c' => cH.work (auxIdx jj c'))
      (fun p q => (cH.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      cH.input cH.output cH.work htapesH prev v₀ u (fun h => by
        obtain ⟨hvmem, hvT, hvinp⟩ := hv₀spec h
        obtain ⟨hprevB, huB⟩ := hpre (hkeptH.2.1 h)
        refine ⟨fun p hp q hq => ?_, hvT, fun p hp q hq => ?_, hvinp, fun P => ?_⟩
        · show (cH.work (walkReg (L.toWalkLayout.spareReg 1 p))).cells (0 + q + 1) = _
          rw [hkeptH.2.2 1 hsp p hp (0 + q + 1)]
          exact hprevB p hp q hq
        · have hk := hkeptH.2.2 0 (by have := L.toWalkLayout.spares_pos; omega) p hp
            (0 + q + 1)
          rw [L.toWalkLayout.spareReg_zero] at hk
          show (cH.work (walkReg (L.toWalkLayout.codeT p))).cells (0 + q + 1) = _
          rw [hk]
          exact huB p hp q hq
        · exact clampIn_deferred x S hspace hwin v₀ (2 * N) hvmem P)
  obtain ⟨c, hreach, hhalt, hin, hwork, hout⟩ :=
    seqTM_run_of_runs _ _ inp₀ out₀ W₀ hreachH hhaltH
      (by rw [hfixI, hfixW, hfixO]; exact hreachT) hhaltT
  have hspare : ∀ n, n < L.toWalkLayout.spares → n ≠ 1 → ∀ p, p < kk + 3 → ∀ q,
      (c.work (walkReg (L.toWalkLayout.spareReg n p))).cells q
        = (W₀ (walkReg (L.toWalkLayout.spareReg n p))).cells q := by
    intro n hn hne p hp q
    rw [hwork, hspT n hn hne p hp q]
    exact hkeptH.2.2 n hn p hp q
  refine ⟨c, tH + 1 + tT, hreach, hhalt, ?_, ?_, ?_, ⟨fun hone => ?_, hspare⟩⟩
  · rw [hin, hwork, hout]
    exact ⟨fun c' _ => rfl, htapesT.2.1, htapesT.2.2.1, htapesT.2.2.2.1, htapesT.2.2.2.2.1,
      htapesT.2.2.2.2.2.1, htapesT.2.2.2.2.2.2.1, htapesT.2.2.2.2.2.2.2.1,
      htapesT.2.2.2.2.2.2.2.2.1, htapesT.2.2.2.2.2.2.2.2.2.1, fun p hp q => rfl⟩
  · intro c' hc' hcn
    rw [hwork]
    rw [show cT.work (auxIdx jj c') = cH.work (auxIdx jj c') from htapesT.1 c' hc']
    exact hkeptH.1 c' hc' hcn
  · rw [hwork, show cT.work (auxIdx jj wcnt) = cH.work (auxIdx jj wcnt) from
      htapesT.1 wcnt hcnt]
    exact hwcntH
  · rw [hwork] at hone ⊢
    obtain ⟨holdH, hlt, hnev, hne0, hne1, huT, hvS⟩ := haccT hone
    obtain ⟨hvmem, -, -⟩ := hv₀spec holdH
    exact ⟨hkeptH.2.1 holdH, v₀, hvmem, hlt, hnev, hne0, hne1, huT, hvS⟩

end Complexity
