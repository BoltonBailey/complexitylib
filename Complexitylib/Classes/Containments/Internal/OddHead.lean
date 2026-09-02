/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.MemberLoop

/-!
# Walking an odd number of steps

⚠️ Unreviewed by Bolton

A walk runs in pairs, so it reaches the codes of an *even* round. The counting recursion needs
both parities: the round after an even one is odd. This file adds the one extra step —
`Complexity.walkStep_chain` once more — and copies its result back into the first tuple, so that
what follows sees the same shape it would after an even walk.

## Main definitions

- `codeBackScanner` — the check that copies the second tuple into the first
- `oddHeadTM` — walk, one more step, copy back

## Main results

- `codeBackStep_run` — what the copy establishes
- `oddHead_run` — the endpoint is a code of the odd round
-/

@[expose] public section

namespace Complexity

variable {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ}

/-- The check that copies the second tuple back into the first: the two agree, and the second is
canonical, so the first ends up holding the code cell for cell. -/
noncomputable def codeBackScanner (tm : NTM kk) (nn S : ℕ) {jj : ℕ}
    (cA cB : ℕ → Fin (jj + 1)) : Scanner jj :=
  Scanner.all 2 (fun p => if p.val = 0 then eqScanner tm nn S cB cA
    else padZeroScanner tm cB)

/-- **The copy-back stage.** -/
theorem codeBackStep_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (g : ℕ → Bool) (s : ℕ) (cc : Fin r) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) (inp₀ out₀ : Tape)
    (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (htapes : WalkTapes (r := r) x L g s cc Wa Wt inp₀ W₀ out₀)
    (v : Code tm.Q kk x.length S)
    (hpre : (W₀ (auxIdx jj cc)).read = Γ.one →
      HoldsCodeTail tm x S (fun q i => (W₀ (walkReg i)).cells q) L.toWalkLayout.codeB v) :
    ∃ (c' : Cfg (jj + 2 + r + 1)
        (famStepTM L (TM.twoPassTM (codeBackScanner tm x.length S L.toWalkLayout.codeA
          L.toWalkLayout.codeB)) 0 cc).Q) (t : ℕ),
      (famStepTM L (TM.twoPassTM (codeBackScanner tm x.length S L.toWalkLayout.codeA
          L.toWalkLayout.codeB)) 0 cc).reachesIn t
        ⟨(famStepTM L (TM.twoPassTM (codeBackScanner tm x.length S L.toWalkLayout.codeA
          L.toWalkLayout.codeB)) 0 cc).qstart, inp₀, W₀, out₀⟩ c' ∧
      (famStepTM L (TM.twoPassTM (codeBackScanner tm x.length S L.toWalkLayout.codeA
          L.toWalkLayout.codeB)) 0 cc).halted c' ∧
      WalkTapes (r := r) x L g (s + 1) cc Wa Wt c'.input c'.work c'.output ∧
      (∀ n, n < L.toWalkLayout.spares → ∀ p, p < kk + 3 → ∀ q,
        (c'.work (walkReg (L.toWalkLayout.spareReg n p))).cells q
          = (W₀ (walkReg (L.toWalkLayout.spareReg n p))).cells q) ∧
      c'.input = TM.parkTape inp₀ ∧
      ((c'.work (auxIdx jj cc)).read = Γ.one →
        (W₀ (auxIdx jj cc)).read = Γ.one ∧
        HoldsCodeTail tm x S (fun q i => (c'.work (walkReg i)).cells q)
          L.toWalkLayout.codeA v ∧
        ∀ p, p < kk + 3 → HoldsBits (fun q i => (c'.work (walkReg i)).cells q) 0
          (L.toWalkLayout.codeA p) (codeBlockScan tm x S v p)) := by
  classical
  have hspares : (2 : ℕ) < 2 + L.toWalkLayout.spares := by
    have := L.toWalkLayout.spares_pos
    omega
  obtain ⟨c', t, -, hreach, hhalt, htapes', hinp', hreg, hacc, -⟩ :=
    famStep_run x L (codeBackScanner tm x.length S L.toWalkLayout.codeA L.toWalkLayout.codeB)
      0 (by omega) g s cc B hB1 hB Wa Wt inp₀ out₀ W₀ htapes
  have hcells : ∀ i : Fin (jj + 1), ∀ q,
      (c'.work (walkReg i)).cells q = stepCellsF L 0 W₀ i q := by
    intro i q
    rw [hreg i]
  have hWt : WalkTapes (r := r) x L g (s + 1) cc Wa Wt c'.input c'.work c'.output := by
    refine ⟨htapes'.1, htapes'.2.1, htapes'.2.2.1, htapes'.2.2.2.1, htapes'.2.2.2.2.1,
      htapes'.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.2.1,
      htapes'.2.2.2.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.2.2.2.1, fun p hp q => ?_⟩
    refine (htapes'.2.2.2.2.2.2.2.2.2.2 p hp q).trans ?_
    show stepCellsF L 0 W₀ (L.toWalkLayout.codeT p) q = Wt p q
    rw [congrFun (stepCellsF_codeT L 0 (by omega) (by omega) W₀ htapes.2.1 htapes.2.2.1 p hp) q]
    exact htapes.2.2.2.2.2.2.2.2.2.2 p hp q
  refine ⟨c', t, hreach, hhalt, hWt, fun n hn p hp q => ?_, hinp', fun hone => ?_⟩
  · rw [hcells,
      congrFun (stepCellsF_spare L 0 (by omega) n hn (by omega) W₀ htapes.2.1 htapes.2.2.1 p hp)
        q]
  obtain ⟨hold, hverd⟩ := hacc hone
  have hvB := holdsCodeTail_famReg_survives x L 0 1 (by omega) (by omega) (by omega) W₀
    htapes.2.1 htapes.2.2.1 v
    (holdsCodeTail_reg_congr tm x S _ L.toWalkLayout.codeB (L.toWalkLayout.famReg 1) v
      (hpre hold) (fun p hp => (L.toWalkLayout.famReg_one p hp).symm))
  have hvBA : HoldsCodeTail tm x S (fun q i => stepCellsF L 0 W₀ i q)
      L.toWalkLayout.codeB v :=
    holdsCodeTail_reg_congr tm x S _ (L.toWalkLayout.famReg 1) L.toWalkLayout.codeB v hvB
      (fun p hp => L.toWalkLayout.famReg_one p hp)
  rw [codeBackScanner, Scanner.all_emit_run] at hverd
  have h0 := hverd ⟨0, by omega⟩
  have h1 := hverd ⟨1, by omega⟩
  rw [if_pos (rfl : (0 : ℕ) = 0)] at h0
  rw [if_neg (by exact (by omega : (1 : ℕ) ≠ 0))] at h1
  have hvBlocks := holdsBlocks_of_holdsCodeTail tm x S _ L.toWalkLayout.codeB v hvBA
    ((padZeroScanner_decides tm x.length S L.toWalkLayout.codeB _).mp h1)
  have hAblocks : ∀ p, p < kk + 3 → HoldsBits (fun q i => stepCellsF L 0 W₀ i q) 0
      (L.toWalkLayout.codeA p) (codeBlockScan tm x S v p) :=
    eqScanner_forces tm x S (TM.scanCol (stepCellsF L 0 W₀)) L.toWalkLayout.codeB
      L.toWalkLayout.codeA v hvBlocks h0
  refine ⟨hold, ?_, fun p hp q hq => ?_⟩
  · refine holdsCodeTail_congr tm x S _ _ L.toWalkLayout.codeA v
      (holdsCodeTail_of_blocks tm x S _ L.toWalkLayout.codeA v hAblocks) (fun p hp q => ?_)
    rw [hcells]
  · show (c'.work (walkReg (L.toWalkLayout.codeA p))).cells (0 + q + 1) = _
    rw [hcells]
    exact hAblocks p hp q hq

/-- **Walk, take one more step, and copy back.** What follows sees the first tuple holding a code
of the *odd* round. -/
noncomputable def oddHeadTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (cc wcnt wlim : Fin rr) :
    TM (jj + 2 + rr + 1) :=
  TM.seqTM (innerHeadTM x L dc (cfgCode x.length S (tm.initCfg x)) cc wcnt wlim)
    (TM.seqTM
      (stepMachine x L dc false false L.toWalkLayout.codeA L.toWalkLayout.codeB
        L.toWalkLayout.cnt L.toWalkLayout.cnt cc)
      (famStepTM L (TM.twoPassTM (codeBackScanner tm x.length S L.toWalkLayout.codeA
        L.toWalkLayout.codeB)) 0 cc))

/-- Its advancing states. -/
noncomputable def oddHeadAdv {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (cc wcnt wlim : Fin rr) :
    (oddHeadTM x L dc cc wcnt wlim).Q → Bool :=
  TM.seqAdv (innerHeadAdv x L dc (cfgCode x.length S (tm.initCfg x)) cc wcnt wlim)
    (TM.seqAdv
      (walkStepAdv rr tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
        L.toWalkLayout.res L.toWalkLayout.cnt L.toWalkLayout.cnt wc false dc
        L.toWalkLayout.codeA L.toWalkLayout.codeB (stepReg (r := rr) L false) (stepWidth L)
        L.toWalkLayout.stepBlocks (stepTargets jj rr) (auxIdx jj cc))
      (famStepAdv L (TM.twoPassTM (codeBackScanner tm x.length S L.toWalkLayout.codeA
        L.toWalkLayout.codeB)) 0 cc))

/-- **It respects the guess protocol.** -/
theorem guessProtocol_oddHeadTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (cc wcnt wlim : Fin rr) :
    TM.GuessProtocol (oddHeadTM x L dc cc wcnt wlim) (oddHeadAdv x L dc cc wcnt wlim) :=
  TM.guessProtocol_seqTM
    (guessProtocol_innerHeadTM x L dc (cfgCode x.length S (tm.initCfg x)) cc wcnt wlim)
    (TM.guessProtocol_seqTM
      (guessProtocol_walkStepTM rr tm x.length S L.toWalkLayout.par L.toWalkLayout.mv
        L.toWalkLayout.dr L.toWalkLayout.res L.toWalkLayout.cnt L.toWalkLayout.cnt wc false dc
        L.toWalkLayout.codeA L.toWalkLayout.codeB (stepReg (r := rr) L false) (stepWidth L)
        L.toWalkLayout.stepBlocks (stepTargets jj rr) (auxIdx jj cc) (auxIdx_ne_last cc))
      (guessProtocol_famStepTM L _ 0 cc))

/-- **What the odd head establishes.** If the accumulator survives, the first tuple holds a code
the search reaches in `2 * N + 1` rounds, and the machine's own input head is where that code says
the simulated one is. -/
theorem oddHead_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (g : ℕ → Bool) (s : ℕ) (cc wcnt wlim : Fin r)
    (hcnt : wcnt ≠ cc) (hlim : wlim ≠ cc) (hcl : wcnt ≠ wlim) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hspace : ∀ c, tm.ReachesCfg (tm.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hwin : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x S c)
    (hwc : wc ≤ walkScanLen tm x.length S) (N : ℕ)
    (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) (inp₀ out₀ : Tape)
    (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (htapes : WalkTapes (r := r) x L g s cc Wa Wt inp₀ W₀ out₀)
    (bits : List Bool) (hbits : (W₀ (auxIdx jj wcnt)).HasBinaryContent bits)
    (hlimN : (Wa wlim).HasBinaryNat N) :
    ∃ (c : Cfg (jj + 2 + r + 1) (oddHeadTM x L dc cc wcnt wlim).Q) (t : ℕ),
      (oddHeadTM x L dc cc wcnt wlim).reachesIn t
        ⟨(oddHeadTM x L dc cc wcnt wlim).qstart, inp₀, W₀, out₀⟩ c ∧
      (oddHeadTM x L dc cc wcnt wlim).halted c ∧
      WalkTapes (r := r) x L g (s + 1 + 2 * N + 1 + 1) cc (fun c' => c.work (auxIdx jj c'))
        (fun p q => (c.work (walkReg (L.toWalkLayout.codeT p))).cells q)
        c.input c.work c.output ∧
      (∀ c' , c' ≠ cc → c' ≠ wcnt →
        c.work (auxIdx jj c')
          = Function.update Wa wcnt ((Tape.init ([] : List Γ)).move Dir3.right) c') ∧
      (∀ n, n < L.toWalkLayout.spares → ∀ p, p < kk + 3 → ∀ q,
        (c.work (walkReg (L.toWalkLayout.spareReg n p))).cells q
          = (W₀ (walkReg (L.toWalkLayout.spareReg n p))).cells q) ∧
      (c.work (auxIdx jj wcnt)).HasBinaryNat N ∧
      ((c.work (auxIdx jj cc)).read = Γ.one →
        (W₀ (auxIdx jj cc)).read = Γ.one ∧
        ∃ b : Code tm.Q kk x.length S,
          b ∈ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 1) ∧
          (∀ p, p < kk + 3 → HoldsBits (fun q i => (c.work (walkReg i)).cells q) 0
            (L.toWalkLayout.codeA p) (codeBlockScan tm x S b p)) ∧
          c.input = ⟨max b.2.1.val 1, (Tape.init (x.map Γ.ofBool)).cells⟩) := by
  classical
  have hcntW : wc ≤ stepWidth L L.toWalkLayout.cntIdx + 1 := by
    rw [stepWidth_scratch L _ L.toWalkLayout.cnt_scratch, L.width_cnt]
    omega
  obtain ⟨cH, tH, hreachH, hhaltH, htapesH, hkeptH, hwcntH, haccH⟩ :=
    innerHead_run x L dc g s cc wcnt wlim hcnt hlim hcl B hB1 hB hspace hwin hwc N Wa Wt
      inp₀ out₀ W₀ htapes inp₀.head le_rfl bits (W₀ (auxIdx jj wcnt)).head hbits le_rfl hlimN
  obtain ⟨hfixI, hfixW, hfixO⟩ :=
    walkTapes_transition_eq x L g (s + 1 + 2 * N) cc (fun c' => cH.work (auxIdx jj c'))
      (fun p q => (cH.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      cH.input cH.work cH.output htapesH
  set off := TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks with hoff
  set g' : ℕ → Bool := fun q => g ((s + 1) * off + q) with hg'
  have hshift : WalkTapes (r := r) x L g' (2 * N) cc (fun c' => cH.work (auxIdx jj c'))
      (fun p q => (cH.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      cH.input cH.work cH.output := by
    refine (walkTapes_shift x L g (s + 1) (2 * N) cc _ _ cH.input cH.work cH.output).mpr ?_
    rw [show s + 1 + 2 * N = s + 1 + 2 * N from rfl] at htapesH
    exact htapesH
  have hchain : WalkChain (r := r) x L L.toWalkLayout.codeA g' (2 * N) cc
      (fun c' => cH.work (auxIdx jj c'))
      (fun p q => (cH.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      cH.input cH.work cH.output := by
    refine ⟨hshift, fun hone => ?_⟩
    obtain ⟨v, hvmem, hvT, hvinp⟩ := haccH hone
    exact ⟨v, hvmem, hshift.2.1, hshift.2.2.1, hshift.2.2.2.1, hshift.2.2.2.2.1, hvT, hvinp,
      hshift.2.2.2.2.2.2.2.1, hshift.2.2.2.2.2.2.2.2.1, hshift.2.2.2.2.2.2.2.2.2.1⟩
  obtain ⟨cS, tS, -, hreachS, hhaltS, hchainS⟩ :=
    walkStep_chain x L dc g' false false L.toWalkLayout.codeA L.toWalkLayout.codeB
      L.toWalkLayout.cnt L.toWalkLayout.cnt L.toWalkLayout.cntIdx L.toWalkLayout.cntIdx
      (2 * N) cc B hspace hwin hB1 hB (fun p hp => L.toWalkLayout.codeA_ne_res hp)
      (fun p hp => L.toWalkLayout.codeB_ne_res hp) L.toWalkLayout.cnt_ne_res
      L.toWalkLayout.cnt_ne_res L.toWalkLayout.cnt_scratch L.toWalkLayout.cnt_scratch rfl rfl
      hcntW hcntW
      (fun p hp => by rw [stepReg, L.toWalkLayout.stepIdx_codeB p hp]; rfl)
      (fun p hp p' hp' hc => L.toWalkLayout.stepIdx_ne_codeA p' p hp' hp
        (L.toWalkLayout.reg_inj _ _ (L.toWalkLayout.stepIdx_lt false p' hp')
          (L.toWalkLayout.codeA_lt p hp) (walkReg_inj hc).symm)) hwc _ _
      cH.input cH.work cH.output hchain
  obtain ⟨cS', tS', -, hreachS', hhaltS', -, hspareS, hmonoS⟩ :=
    walkStep_tapes x L dc g' false false L.toWalkLayout.codeA L.toWalkLayout.codeB
      L.toWalkLayout.cnt L.toWalkLayout.cnt (2 * N) cc B hB1 hB
      (fun c' => cH.work (auxIdx jj c'))
      (fun p q => (cH.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      cH.input cH.output cH.work hshift
  have heqS : cS' = cS := TM.reachesIn_halted_unique hreachS' hreachS hhaltS' hhaltS
  rw [heqS] at hspareS hmonoS
  have htapesS : WalkTapes (r := r) x L g (s + 1 + 2 * N + 1) cc
      (fun c' => cH.work (auxIdx jj c'))
      (fun p q => (cH.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      cS.input cS.work cS.output := by
    refine (walkTapes_shift x L g (s + 1) (2 * N + 1) cc _ _ cS.input cS.work cS.output).mp ?_
    exact hchainS.1
  obtain ⟨hfixI', hfixW', hfixO'⟩ :=
    walkTapes_transition_eq x L g (s + 1 + 2 * N + 1) cc (fun c' => cH.work (auxIdx jj c'))
      (fun p q => (cH.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      cS.input cS.work cS.output htapesS
  set b₀ : Code tm.Q kk x.length S :=
    if h : (cS.work (auxIdx jj cc)).read = Γ.one then (hchainS.2 h).choose
    else cfgCode x.length S (tm.initCfg x) with hb₀def
  have hb₀spec : ∀ h : (cS.work (auxIdx jj cc)).read = Γ.one,
      b₀ ∈ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 1) ∧
      WalkSoundInv (r := r) x L L.toWalkLayout.codeB b₀ g' (2 * N + 1)
        cS.input cS.work cS.output := by
    intro h
    rw [hb₀def, dif_pos h]
    exact (hchainS.2 h).choose_spec
  obtain ⟨cC, tC, hreachC, hhaltC, htapesC, hspareC, hinpC, haccC⟩ :=
    codeBackStep_run x L g (s + 1 + 2 * N + 1) cc B hB1 hB (fun c' => cH.work (auxIdx jj c'))
      (fun p q => (cH.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      cS.input cS.output cS.work htapesS b₀ (fun h => (hb₀spec h).2.2.2.2.2.1)
  obtain ⟨cSC, hreachSC, hhaltSC, hinSC, hworkSC, houtSC⟩ :=
    seqTM_run_of_runs _ _ cH.input cH.output cH.work hreachS hhaltS
      (by rw [hfixI', hfixW', hfixO']; exact hreachC) hhaltC
  obtain ⟨c, hreach, hhalt, hin, hwork, hout⟩ :=
    seqTM_run_of_runs _ _ inp₀ out₀ W₀ hreachH hhaltH
      (by rw [hfixI, hfixW, hfixO]; exact hreachSC) hhaltSC
  have hworkc : c.work = cC.work := by rw [hwork, hworkSC]
  have hinc : c.input = cC.input := by rw [hin, hinSC]
  have houtc : c.output = cC.output := by rw [hout, houtSC]
  refine ⟨c, tH + 1 + (tS + 1 + tC), hreach, hhalt, ?_, ?_, ?_, ?_, fun hone => ?_⟩
  · rw [hinc, hworkc, houtc]
    exact ⟨fun c' _ => rfl, htapesC.2.1, htapesC.2.2.1, htapesC.2.2.2.1, htapesC.2.2.2.2.1,
      htapesC.2.2.2.2.2.1, htapesC.2.2.2.2.2.2.1, htapesC.2.2.2.2.2.2.2.1,
      htapesC.2.2.2.2.2.2.2.2.1, htapesC.2.2.2.2.2.2.2.2.2.1, fun p hp q => rfl⟩
  · intro c' hc' hcn
    rw [hworkc, show cC.work (auxIdx jj c') = cH.work (auxIdx jj c') from htapesC.1 c' hc']
    exact hkeptH.1 c' hc' hcn
  · intro n hn p hp q
    rw [hworkc, hspareC n hn p hp q]
    rw [hspareS n hn p hp q]
    exact hkeptH.2.2 n hn p hp q
  · rw [hworkc, show cC.work (auxIdx jj wcnt) = cH.work (auxIdx jj wcnt) from
      htapesC.1 wcnt hcnt]
    exact hwcntH
  · rw [hworkc] at hone ⊢
    obtain ⟨holdS, -, hAblocks⟩ := haccC hone
    obtain ⟨hbmem, hbinv⟩ := hb₀spec holdS
    refine ⟨hkeptH.2.1 (hmonoS holdS), b₀, hbmem, ⟨hAblocks, ?_⟩⟩
    rw [hinc, hinpC, hbinv.2.2.2.2.2.1]
    exact Tape.ext (by
      show max (max b₀.2.1.val 1) 1 = max b₀.2.1.val 1
      omega) rfl

end Complexity
