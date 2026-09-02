/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.CanonScan

/-!
# Listing the non-members of a round

⚠️ Unreviewed by Bolton

The upper half of the counting split lists codes *outside* a round: guess a candidate and check
it spells out a code (`Complexity.canonScanner`), check it is above the last non-member, remember
it in the second spare tuple, and then certify the non-membership itself by running the whole
inner counting loop against it. The list of non-members lives only in the loop's invariant, like
every other list here.

## Main definitions

- `nonOrderStep_run`, `nonCopyStep_run` — the order and remember stages, on the second spare
- `nonMemberBodyTM` — one non-member: guess, order, remember, then the inner loop

## Main results

- `seqTM_run_of_reaches` — untimed sequential glue, for bodies containing untimed loops
-/

@[expose] public section

namespace Complexity

variable {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ}

/-! ## Untimed sequential glue -/

/-- A reachability has some length. -/
theorem exists_reachesIn_of_reaches' {n : ℕ} {tm : TM n} {c c' : Cfg n tm.Q}
    (h : tm.reaches c c') : ∃ t, tm.reachesIn t c c' := by
  induction h with
  | refl => exact ⟨0, TM.reachesIn.zero⟩
  | tail _ hstep ih =>
      obtain ⟨t, ht⟩ := ih
      exact ⟨t + 1, TM.reachesIn_snoc ht hstep⟩

/-- **Sequential runs compose without time bounds** — the shape a body needs when one of its
stages is a loop whose contract is untimed. -/
theorem seqTM_run_of_reaches {n : ℕ} (M₁ M₂ : TM n) (inp₀ out₀ : Tape) (W₀ : Fin n → Tape)
    {c₁ : Cfg n M₁.Q} (hreach₁ : M₁.reaches ⟨M₁.qstart, inp₀, W₀, out₀⟩ c₁)
    (hhalt₁ : M₁.halted c₁)
    {c₂ : Cfg n M₂.Q}
    (hreach₂ : M₂.reaches ⟨M₂.qstart, TM.transitionInput c₁.input,
      (fun i => TM.transitionTape (c₁.work i)), TM.transitionTape c₁.output⟩ c₂)
    (hhalt₂ : M₂.halted c₂) :
    ∃ c : Cfg n (TM.seqTM M₁ M₂).Q,
      (TM.seqTM M₁ M₂).reaches ⟨(TM.seqTM M₁ M₂).qstart, inp₀, W₀, out₀⟩ c ∧
      (TM.seqTM M₁ M₂).halted c ∧
      c.input = c₂.input ∧ c.work = c₂.work ∧ c.output = c₂.output := by
  obtain ⟨t₁, hr₁⟩ := exists_reachesIn_of_reaches' hreach₁
  obtain ⟨t₂, hr₂⟩ := exists_reachesIn_of_reaches' hreach₂
  obtain ⟨c, hreach, hhalt, hin, hwork, hout⟩ :=
    seqTM_run_of_runs M₁ M₂ inp₀ out₀ W₀ hr₁ hhalt₁ hr₂ hhalt₂
  exact ⟨c, TM.reaches_of_reachesIn hreach, hhalt, hin, hwork, hout⟩

/-! ## The order and remember stages, on the second spare -/

/-- **The non-member ordering stage.** The last non-member, remembered in the second spare
tuple, comes below the candidate. -/
theorem nonOrderStep_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (hsp2 : 2 < L.toWalkLayout.spares) (g : ℕ → Bool) (s : ℕ)
    (cc : Fin r) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) (inp₀ out₀ : Tape)
    (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (htapes : WalkTapes (r := r) x L g s cc Wa Wt inp₀ W₀ out₀)
    (prev u : Code tm.Q kk x.length S)
    (hpre : (W₀ (auxIdx jj cc)).read = Γ.one →
      (∀ p, p < kk + 3 → HoldsBits (fun q i => (W₀ (walkReg i)).cells q) 0
        (L.toWalkLayout.spareReg 2 p) (codeBlockScan tm x S prev p)) ∧
      ∀ p, p < kk + 3 → HoldsBits (fun q i => (W₀ (walkReg i)).cells q) 0
        (L.toWalkLayout.codeT p) (codeBlockScan tm x S u p)) :
    ∃ (c' : Cfg (jj + 2 + r + 1)
        (famStepTM L (TM.twoPassTM (orderOnlyScanner tm x.length S (L.toWalkLayout.spareReg 2)
          L.toWalkLayout.codeT)) 1 cc).Q) (t : ℕ),
      t ≤ famTime x L r B ∧
      (famStepTM L (TM.twoPassTM (orderOnlyScanner tm x.length S (L.toWalkLayout.spareReg 2)
          L.toWalkLayout.codeT)) 1 cc).reachesIn t
        ⟨(famStepTM L (TM.twoPassTM (orderOnlyScanner tm x.length S (L.toWalkLayout.spareReg 2)
          L.toWalkLayout.codeT)) 1 cc).qstart, inp₀, W₀, out₀⟩ c' ∧
      (famStepTM L (TM.twoPassTM (orderOnlyScanner tm x.length S (L.toWalkLayout.spareReg 2)
          L.toWalkLayout.codeT)) 1 cc).halted c' ∧
      WalkTapes (r := r) x L g (s + 1) cc Wa Wt c'.input c'.work c'.output ∧
      c'.input = TM.parkTape inp₀ ∧
      ((c'.work (auxIdx jj cc)).read = Γ.one →
        (W₀ (auxIdx jj cc)).read = Γ.one ∧ codeLt tm x S prev u ∧
        ∀ p, p < kk + 3 → HoldsBits (fun q i => (c'.work (walkReg i)).cells q) 0
          (L.toWalkLayout.codeT p) (codeBlockScan tm x S u p)) ∧
      (∀ n, n < L.toWalkLayout.spares → 2 + n ≠ 1 → ∀ p, p < kk + 3 → ∀ q,
        (c'.work (walkReg (L.toWalkLayout.spareReg n p))).cells q
          = (W₀ (walkReg (L.toWalkLayout.spareReg n p))).cells q) := by
  classical
  have hsp4 : (4 : ℕ) < 2 + L.toWalkLayout.spares := by omega
  have hspares : (2 : ℕ) < 2 + L.toWalkLayout.spares := by omega
  obtain ⟨c', t, htle, hreach, hhalt, htapes', hinp', hreg, hacc, -⟩ :=
    famStep_run x L (orderOnlyScanner tm x.length S (L.toWalkLayout.spareReg 2)
      L.toWalkLayout.codeT) 1 (by omega) g s cc B hB1 hB Wa Wt inp₀ out₀ W₀ htapes
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
  obtain ⟨hprev, hu⟩ := hpre hold
  have hu' := holdsBlocks_survives x L 1 2 (by omega) hspares (by omega) L.toWalkLayout.codeT
    (fun p hp => codeT_eq_famIdx L p hp) W₀ htapes.2.1 htapes.2.2.1 u hu
  have hprev' := holdsBlocks_survives x L 1 4 (by omega) hsp4 (by omega)
    (L.toWalkLayout.spareReg 2) (fun p hp => (L.toWalkLayout.famReg_spare 2 p hsp2 hp).symm) W₀
    htapes.2.1 htapes.2.2.1 prev hprev
  rw [orderOnlyScanner, Scanner.all_emit_run] at hverd
  have h0 := hverd ⟨0, by omega⟩
  rw [if_pos (rfl : (0 : ℕ) = 0)] at h0
  refine ⟨hold, codeLt_of_ltScanner x _ (L.toWalkLayout.spareReg 2) L.toWalkLayout.codeT prev u
      hprev' hu' h0, fun p hp q hq => ?_⟩
  show (c'.work (walkReg (L.toWalkLayout.codeT p))).cells (0 + q + 1) = _
  rw [hcells]
  exact hu' p hp q hq

/-- **The non-member remembering stage.** The candidate is copied into the second spare tuple,
by guessing it there and checking the two tuples agree. -/
theorem nonCopyStep_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (hsp2 : 2 < L.toWalkLayout.spares) (g : ℕ → Bool) (s : ℕ)
    (cc : Fin r) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) (inp₀ out₀ : Tape)
    (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (htapes : WalkTapes (r := r) x L g s cc Wa Wt inp₀ W₀ out₀)
    (u : Code tm.Q kk x.length S)
    (hpre : (W₀ (auxIdx jj cc)).read = Γ.one →
      ∀ p, p < kk + 3 → HoldsBits (fun q i => (W₀ (walkReg i)).cells q) 0
        (L.toWalkLayout.codeT p) (codeBlockScan tm x S u p)) :
    ∃ (c' : Cfg (jj + 2 + r + 1)
        (famStepTM L (TM.twoPassTM (eqScanner tm x.length S L.toWalkLayout.codeT
          (L.toWalkLayout.spareReg 2))) 4 cc).Q) (t : ℕ),
      t ≤ famTime x L r B ∧
      (famStepTM L (TM.twoPassTM (eqScanner tm x.length S L.toWalkLayout.codeT
          (L.toWalkLayout.spareReg 2))) 4 cc).reachesIn t
        ⟨(famStepTM L (TM.twoPassTM (eqScanner tm x.length S L.toWalkLayout.codeT
          (L.toWalkLayout.spareReg 2))) 4 cc).qstart, inp₀, W₀, out₀⟩ c' ∧
      (famStepTM L (TM.twoPassTM (eqScanner tm x.length S L.toWalkLayout.codeT
          (L.toWalkLayout.spareReg 2))) 4 cc).halted c' ∧
      WalkTapes (r := r) x L g (s + 1) cc Wa Wt c'.input c'.work c'.output ∧
      c'.input = TM.parkTape inp₀ ∧
      ((c'.work (auxIdx jj cc)).read = Γ.one →
        (W₀ (auxIdx jj cc)).read = Γ.one ∧
        (∀ p, p < kk + 3 → HoldsBits (fun q i => (c'.work (walkReg i)).cells q) 0
          (L.toWalkLayout.codeT p) (codeBlockScan tm x S u p)) ∧
        ∀ p, p < kk + 3 → HoldsBits (fun q i => (c'.work (walkReg i)).cells q) 0
          (L.toWalkLayout.spareReg 2 p) (codeBlockScan tm x S u p)) ∧
      (∀ n, n < L.toWalkLayout.spares → 2 + n ≠ 4 → ∀ p, p < kk + 3 → ∀ q,
        (c'.work (walkReg (L.toWalkLayout.spareReg n p))).cells q
          = (W₀ (walkReg (L.toWalkLayout.spareReg n p))).cells q) := by
  classical
  have hspares : (2 : ℕ) < 2 + L.toWalkLayout.spares := by omega
  have hf : (4 : ℕ) < 2 + L.toWalkLayout.spares := by omega
  obtain ⟨c', t, htle, hreach, hhalt, htapes', hinp', hreg, hacc, -⟩ :=
    famStep_run x L (eqScanner tm x.length S L.toWalkLayout.codeT (L.toWalkLayout.spareReg 2))
      4 hf g s cc B hB1 hB Wa Wt inp₀ out₀ W₀ htapes
  have hcells : ∀ i : Fin (jj + 1), ∀ q,
      (c'.work (walkReg i)).cells q = stepCellsF L 4 W₀ i q := by
    intro i q
    rw [hreg i]
  have hWt : WalkTapes (r := r) x L g (s + 1) cc Wa Wt c'.input c'.work c'.output := by
    refine ⟨htapes'.1, htapes'.2.1, htapes'.2.2.1, htapes'.2.2.2.1, htapes'.2.2.2.2.1,
      htapes'.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.2.1,
      htapes'.2.2.2.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.2.2.2.1, fun p hp q => ?_⟩
    refine (htapes'.2.2.2.2.2.2.2.2.2.2 p hp q).trans ?_
    show stepCellsF L 4 W₀ (L.toWalkLayout.codeT p) q = Wt p q
    rw [congrFun (stepCellsF_codeT L 4 hf (by omega) W₀ htapes.2.1 htapes.2.2.1 p hp) q]
    exact htapes.2.2.2.2.2.2.2.2.2.2 p hp q
  have hspare : ∀ n, n < L.toWalkLayout.spares → 2 + n ≠ 4 → ∀ p, p < kk + 3 → ∀ q,
      (c'.work (walkReg (L.toWalkLayout.spareReg n p))).cells q
        = (W₀ (walkReg (L.toWalkLayout.spareReg n p))).cells q := by
    intro n hn hne p hp q
    rw [hcells]
    exact congrFun (stepCellsF_spare L 4 hf n hn (Ne.symm hne) W₀
      htapes.2.1 htapes.2.2.1 p hp) q
  refine ⟨c', t, htle, hreach, hhalt, hWt, hinp', ⟨fun hone => ?_, hspare⟩⟩
  obtain ⟨hold, hverd⟩ := hacc hone
  have hu := hpre hold
  have hU := holdsBlocks_survives x L 4 2 hf hspares (by omega) L.toWalkLayout.codeT
    (fun p hp => codeT_eq_famIdx L p hp) W₀ htapes.2.1 htapes.2.2.1 u hu
  refine ⟨hold, fun p hp q hq => ?_, fun p hp q hq => ?_⟩
  · show (c'.work (walkReg (L.toWalkLayout.codeT p))).cells (0 + q + 1) = _
    rw [hcells]
    exact hU p hp q hq
  · show (c'.work (walkReg (L.toWalkLayout.spareReg 2 p))).cells (0 + q + 1) = _
    rw [hcells]
    exact eqScanner_forces tm x S (TM.scanCol (stepCellsF L 4 W₀)) L.toWalkLayout.codeT
      (L.toWalkLayout.spareReg 2) u hU hverd p hp q hq

/-! ## One non-member -/

/-- How many stages one iteration of the non-member loop consumes: the candidate guess, the
order check, the remember, and a whole inner counting loop. -/
def nonBodyStages (N cmax : ℕ) : ℕ := 1 + 1 + 1 + cmax * innerBodyStages N

/-- **One non-member of the odd round**: guess a candidate and check it spells out a code, check
it is above the last non-member, remember it in the second spare, clear the inner counter, and
run the inner counting loop against it. -/
noncomputable def nonMemberBodyTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (cc wcnt wlim icnt ilim : Fin rr) : TM (jj + 2 + rr + 1) :=
  TM.seqTM
    (famStepTM L (TM.twoPassTM (canonScanner tm x.length S (L.toWalkLayout.famReg 2))) 2 cc)
    (TM.seqTM
      (famStepTM L (TM.twoPassTM (orderOnlyScanner tm x.length S (L.toWalkLayout.spareReg 2)
        L.toWalkLayout.codeT)) 1 cc)
      (TM.seqTM
        (famStepTM L (TM.twoPassTM (eqScanner tm x.length S L.toWalkLayout.codeT
          (L.toWalkLayout.spareReg 2))) 4 cc)
        (TM.seqTM (TM.resetBinaryWorkTM (auxIdx jj icnt))
          (innerLoopTM x L dc cc wcnt wlim icnt ilim))))

/-- The advancing states of one non-member iteration. -/
noncomputable def nonMemberBodyAdv {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (cc wcnt wlim icnt ilim : Fin rr) :
    (nonMemberBodyTM x L dc cc wcnt wlim icnt ilim).Q → Bool :=
  TM.seqAdv
    (famStepAdv L (TM.twoPassTM (canonScanner tm x.length S (L.toWalkLayout.famReg 2))) 2 cc)
    (TM.seqAdv
      (famStepAdv L (TM.twoPassTM (orderOnlyScanner tm x.length S (L.toWalkLayout.spareReg 2)
        L.toWalkLayout.codeT)) 1 cc)
      (TM.seqAdv
        (famStepAdv L (TM.twoPassTM (eqScanner tm x.length S L.toWalkLayout.codeT
          (L.toWalkLayout.spareReg 2))) 4 cc)
        (TM.seqAdv (TM.seqAdv (fun _ => false) (TM.seqAdv (fun _ => false) (fun _ => false)))
          (TM.binaryForAdv
            (innerBodyAdv x L dc (cfgCode x.length S (tm.initCfg x)) cc wcnt wlim)
            (auxIdx jj icnt) (auxIdx jj ilim)))))

/-- **The whole iteration respects the guess protocol.** -/
theorem guessProtocol_nonMemberBodyTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (cc wcnt wlim icnt ilim : Fin rr) :
    TM.GuessProtocol (nonMemberBodyTM x L dc cc wcnt wlim icnt ilim)
      (nonMemberBodyAdv x L dc cc wcnt wlim icnt ilim) :=
  TM.guessProtocol_seqTM (guessProtocol_famStepTM L _ 2 cc)
    (TM.guessProtocol_seqTM (guessProtocol_famStepTM L _ 1 cc)
      (TM.guessProtocol_seqTM (guessProtocol_famStepTM L _ 4 cc)
        (TM.guessProtocol_seqTM
          (TM.guessProtocol_resetBinaryWorkTM (auxIdx jj icnt) (auxIdx_ne_last icnt))
          (TM.guessProtocol_binaryForTM
            (guessProtocol_innerBodyTM x L dc (cfgCode x.length S (tm.initCfg x)) cc wcnt wlim)
            (auxIdx jj icnt) (auxIdx jj ilim) (auxIdx_ne_last icnt) (auxIdx_ne_last ilim)))))

/-- **What one non-member costs and establishes.** The candidate the stage guessed is a code
outside the round, above the last one, and now remembered in the second spare tuple. -/
theorem nonMemberBody_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (hsp2 : 2 < L.toWalkLayout.spares) (g : ℕ → Bool) (s : ℕ)
    (cc wcnt wlim icnt ilim : Fin r) (hcnt : wcnt ≠ cc) (hlim : wlim ≠ cc) (hcl : wcnt ≠ wlim)
    (hic : icnt ≠ cc) (hiw : icnt ≠ wcnt) (hil : wlim ≠ icnt) (hlc : ilim ≠ cc)
    (hlw : ilim ≠ wcnt) (hli : icnt ≠ ilim) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hspace : ∀ c, tm.ReachesCfg (tm.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hwin : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x S c)
    (hwc : wc ≤ walkScanLen tm x.length S) (N cmax : ℕ)
    (hcard : (NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N)).card ≤ cmax)
    (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) (inp₀ out₀ : Tape)
    (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (htapes : WalkTapes (r := r) x L g s cc Wa Wt inp₀ W₀ out₀)
    (hbitsW : ∃ bw, (Wa wcnt).HasBinaryContent bw)
    (hbitsI : ∃ bi, (Wa icnt).HasBinaryContent bi)
    (hWaN : (Wa wlim).HasBinaryNat N) (hWaC : (Wa ilim).HasBinaryNat cmax)
    (prev : Code tm.Q kk x.length S)
    (hprev : (W₀ (auxIdx jj cc)).read = Γ.one →
      ∀ p, p < kk + 3 → HoldsBits (fun q i => (W₀ (walkReg i)).cells q) 0
        (L.toWalkLayout.spareReg 2 p) (codeBlockScan tm x S prev p))
    (hw1 : (W₀ (auxIdx jj cc)).read = Γ.one →
      ∃ w1 : Code tm.Q kk x.length S,
        ∀ p, p < kk + 3 → HoldsBits (fun q i => (W₀ (walkReg i)).cells q) 0
          (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S w1 p)) :
    ∃ c : Cfg (jj + 2 + r + 1) (nonMemberBodyTM x L dc cc wcnt wlim icnt ilim).Q,
      (nonMemberBodyTM x L dc cc wcnt wlim icnt ilim).reaches
        ⟨(nonMemberBodyTM x L dc cc wcnt wlim icnt ilim).qstart, inp₀, W₀, out₀⟩ c ∧
      (nonMemberBodyTM x L dc cc wcnt wlim icnt ilim).halted c ∧
      WalkTapes (r := r) x L g (s + nonBodyStages N cmax) cc
        (fun c' => c.work (auxIdx jj c'))
        (fun p q => (c.work (walkReg (L.toWalkLayout.codeT p))).cells q)
        c.input c.work c.output ∧
      (∀ c', c' ≠ cc → c' ≠ wcnt → c' ≠ icnt → c.work (auxIdx jj c') = Wa c') ∧
      (c.work (auxIdx jj icnt)).HasBinaryNat cmax ∧
      (∃ bw, (c.work (auxIdx jj wcnt)).HasBinaryContent bw) ∧
      ((c.work (auxIdx jj cc)).read = Γ.one →
        (W₀ (auxIdx jj cc)).read = Γ.one ∧
        ∃ u : Code tm.Q kk x.length S,
          u ∉ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 1) ∧
          codeLt tm x S prev u ∧
          (∀ p, p < kk + 3 → HoldsBits (fun q i => (c.work (walkReg i)).cells q) 0
            (L.toWalkLayout.spareReg 2 p) (codeBlockScan tm x S u p)) ∧
          ∃ w1' : Code tm.Q kk x.length S,
            ∀ p, p < kk + 3 → HoldsBits (fun q i => (c.work (walkReg i)).cells q) 0
              (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S w1' p)) := by
  classical
  have hsp : 1 < L.toWalkLayout.spares := by omega
  -- stage one: the candidate
  obtain ⟨c₀, t₀, -, hreach₀, hhalt₀, htapes₀, hinp₀, hacc₀, hsp₀⟩ :=
    canonStep_run x L (by omega) g s cc B hB1 hB Wa Wt inp₀ out₀ W₀ htapes
  obtain ⟨hfix₀i, hfix₀w, hfix₀o⟩ :=
    walkTapes_transition_eq x L g (s + 1) cc Wa
      (fun p q => (c₀.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      c₀.input c₀.work c₀.output htapes₀
  -- the candidate, under the accumulator
  set u₀ : Code tm.Q kk x.length S :=
    if h : (c₀.work (auxIdx jj cc)).read = Γ.one then (hacc₀ h).2.choose
    else cfgCode x.length S (tm.initCfg x) with hu₀def
  have hu₀spec : ∀ h : (c₀.work (auxIdx jj cc)).read = Γ.one,
      ∀ p, p < kk + 3 → HoldsBits (fun q i => (c₀.work (walkReg i)).cells q) 0
        (L.toWalkLayout.codeT p) (codeBlockScan tm x S u₀ p) := by
    intro h
    rw [hu₀def, dif_pos h]
    exact (hacc₀ h).2.choose_spec
  -- stage two: the order check
  obtain ⟨c₁, t₁, -, hreach₁, hhalt₁, htapes₁, hinp₁, hacc₁, hsp₁⟩ :=
    nonOrderStep_run x L hsp2 g (s + 1) cc B hB1 hB Wa
      (fun p q => (c₀.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      c₀.input c₀.output c₀.work htapes₀ prev u₀ (fun h => by
        refine ⟨fun p hp q hq => ?_, hu₀spec h⟩
        show (c₀.work (walkReg (L.toWalkLayout.spareReg 2 p))).cells (0 + q + 1) = _
        rw [hsp₀ 2 hsp2 (by omega) p hp (0 + q + 1)]
        exact hprev (hacc₀ h).1 p hp q hq)
  obtain ⟨hfix₁i, hfix₁w, hfix₁o⟩ :=
    walkTapes_transition_eq x L g (s + 1 + 1) cc Wa
      (fun p q => (c₀.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      c₁.input c₁.work c₁.output htapes₁
  -- stage three: remember the candidate
  obtain ⟨c₂, t₂, -, hreach₂, hhalt₂, htapes₂, hinp₂, hacc₂, hsp₂'⟩ :=
    nonCopyStep_run x L hsp2 g (s + 1 + 1) cc B hB1 hB Wa
      (fun p q => (c₀.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      c₁.input c₁.output c₁.work htapes₁ u₀ (fun h => (hacc₁ h).2.2)
  obtain ⟨hfix₂i, hfix₂w, hfix₂o⟩ :=
    walkTapes_transition_eq x L g (s + 1 + 1 + 1) cc Wa
      (fun p q => (c₀.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      c₂.input c₂.work c₂.output htapes₂
  -- stage four: clear the inner counter
  obtain ⟨bitsI, hbitsI'⟩ := hbitsI
  have hbitsI₂ : (c₂.work (auxIdx jj icnt)).HasBinaryContent bitsI := by
    rw [htapes₂.1 icnt hic]
    exact hbitsI'
  obtain ⟨c₃, t₃, -, hreach₃, hhalt₃, htapes₃r, hinp₃, hout₃, hwork₃⟩ :=
    walkTapes_reset x L g (s + 1 + 1 + 1) cc icnt hic Wa
      (fun p q => (c₀.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      bitsI (c₂.work (auxIdx jj icnt)).head c₂.input c₂.output c₂.work htapes₂ hbitsI₂ le_rfl
      c₂.input c₂.work c₂.output ⟨rfl, rfl, rfl⟩
  obtain ⟨hfix₃i, hfix₃w, hfix₃o⟩ :=
    walkTapes_transition_eq x L g (s + 1 + 1 + 1) cc
      (Function.update Wa icnt ((Tape.init []).move Dir3.right))
      (fun p q => (c₀.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      c₃.input c₃.work c₃.output htapes₃r
  -- what the tapes look like at the loop's entry
  have hwork₃w : ∀ i : Fin (jj + 1), c₃.work (walkReg i) = c₂.work (walkReg i) := by
    intro i
    rw [hwork₃, Function.update_of_ne (walkReg_ne_auxIdx i icnt)]
  have hwork₃a : ∀ c' : Fin r, c' ≠ icnt → c₃.work (auxIdx jj c') = c₂.work (auxIdx jj c') := by
    intro c' hc'
    rw [hwork₃, Function.update_of_ne (auxIdx_injective hc')]
  -- the inner loop, from its own frame
  set Wai : Fin r → Tape := fun c' => c₃.work (auxIdx jj c') with hWai
  set a₃ : Γ := (c₃.work (auxIdx jj cc)).read with ha₃
  set Wsp : ℕ → ℕ → ℕ → Γ :=
    fun n p q => (c₃.work (walkReg (L.toWalkLayout.spareReg n p))).cells q with hWsp
  have htapes₃ : WalkTapes (r := r) x L g (s + 1 + 1 + 1) cc Wai
      (fun p q => (c₃.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      c₃.input c₃.work c₃.output := by
    refine ⟨fun c' _ => rfl, htapes₃r.2.1, htapes₃r.2.2.1, htapes₃r.2.2.2.1,
      htapes₃r.2.2.2.2.1, htapes₃r.2.2.2.2.2.1, htapes₃r.2.2.2.2.2.2.1,
      htapes₃r.2.2.2.2.2.2.2.1, htapes₃r.2.2.2.2.2.2.2.2.1, htapes₃r.2.2.2.2.2.2.2.2.2.1,
      fun p hp q => rfl⟩
  have hframe0 : TM.BinaryForFrame (auxIdx jj icnt) (auxIdx jj ilim) cmax
      (InnerInv x L g (s + 1 + 1 + 1) cc wcnt icnt Wai a₃ Wsp u₀ N) 0
      c₃.input c₃.work c₃.output := by
    refine ⟨⟨?_, fun c' _ _ _ => rfl, ?_, fun hone => ?_, fun n hn hne p hp q => rfl⟩,
      ?_, ?_, ?_, ?_, ?_⟩
    · simpa using htapes₃
    · obtain ⟨bw, hbw⟩ := hbitsW
      refine ⟨bw, ?_⟩
      show (c₃.work (auxIdx jj wcnt)).HasBinaryContent bw
      rw [hwork₃a wcnt (fun h => hiw h.symm), htapes₂.1 wcnt hcnt]
      exact hbw
    · refine ⟨hone.symm ▸ rfl, ?_⟩
      have hone₂ : (c₂.work (auxIdx jj cc)).read = Γ.one := by
        rw [← hwork₃a cc (fun h => hic h.symm)]
        exact hone
      obtain ⟨hone₁, huT₂, hu2⟩ := hacc₂ hone₂
      obtain ⟨hone₀, -, -⟩ := hacc₁ hone₁
      obtain ⟨w1, hw1'⟩ := hw1 (hacc₀ hone₀).1
      refine ⟨[], w1, by omega, List.Pairwise.nil, by simp, by simp, by simp,
        fun p hp q hq => ?_, fun p hp q hq => ?_⟩
      · show (c₃.work (walkReg (L.toWalkLayout.spareReg 1 p))).cells (0 + q + 1) = _
        rw [hwork₃w, hsp₂' 1 hsp (by omega) p hp (0 + q + 1),
          hsp₁ 1 hsp (by omega) p hp (0 + q + 1), hsp₀ 1 hsp (by omega) p hp (0 + q + 1)]
        exact hw1' p hp q hq
      · show (c₃.work (walkReg (L.toWalkLayout.codeT p))).cells (0 + q + 1) = _
        rw [hwork₃w]
        exact huT₂ p hp q hq
    · rw [hwork₃, Function.update_self]
      simpa using Tape.init_move_right_hasBinaryNat 0
    · rw [hwork₃a ilim hli.symm, htapes₂.1 ilim hlc]
      exact hWaC
    · exact Tape.StartInvariant.read_ne_start ⟨by
        rw [show c₃.input.cells 0 = (Tape.init (x.map Γ.ofBool)).cells 0 from
          congrFun htapes₃r.2.2.2.2.2.1 0]
        exact Tape.init_cells_zero _, fun q hq => by
        rw [show c₃.input.cells q = (Tape.init (x.map Γ.ofBool)).cells q from
          congrFun htapes₃r.2.2.2.2.2.1 q]
        exact Tape.init_ofBool_cells_ne_start x q hq⟩ htapes₃r.2.2.2.2.2.2.1
    · exact fun i => (htapes₃r.2.1 i).read_ne_start (htapes₃r.2.2.1 i)
    · exact htapes₃r.2.2.2.2.2.2.2.1.read_ne_start htapes₃r.2.2.2.2.2.2.2.2.1
  obtain ⟨c₄, hreach₄, hhalt₄, hframe₄⟩ :=
    innerLoop_run x L dc hsp g (s + 1 + 1 + 1) cc wcnt wlim icnt ilim hcnt hlim hcl hic hiw
      hil hlc hlw hli B hB1 hB hspace hwin hwc Wai a₃ N
      (by
        show (c₃.work (auxIdx jj wlim)).HasBinaryNat N
        rw [hwork₃a wlim hil, htapes₂.1 wlim hlim]
        exact hWaN) Wsp u₀ cmax
      c₃.input c₃.work c₃.output hframe0
  obtain ⟨⟨htapes₄, haux₄, hbw₄, hsem₄, hspv₄⟩, hcnt₄, hlim₄, -, -, -⟩ := hframe₄
  -- chain the five runs
  obtain ⟨c₃₄, hreach₃₄, hhalt₃₄, hin₃₄, hwork₃₄, hout₃₄⟩ :=
    seqTM_run_of_reaches _ _ c₂.input c₂.output c₂.work
      (TM.reaches_of_reachesIn hreach₃) hhalt₃
      (by rw [hfix₃i, hfix₃w, hfix₃o]; exact hreach₄) hhalt₄
  obtain ⟨c₂₄, hreach₂₄, hhalt₂₄, hin₂₄, hwork₂₄, hout₂₄⟩ :=
    seqTM_run_of_reaches _ _ c₁.input c₁.output c₁.work
      (TM.reaches_of_reachesIn hreach₂) hhalt₂
      (by rw [hfix₂i, hfix₂w, hfix₂o]; exact hreach₃₄) hhalt₃₄
  obtain ⟨c₁₄, hreach₁₄, hhalt₁₄, hin₁₄, hwork₁₄, hout₁₄⟩ :=
    seqTM_run_of_reaches _ _ c₀.input c₀.output c₀.work
      (TM.reaches_of_reachesIn hreach₁) hhalt₁
      (by rw [hfix₁i, hfix₁w, hfix₁o]; exact hreach₂₄) hhalt₂₄
  obtain ⟨c, hreach, hhalt, hin, hwork, hout⟩ :=
    seqTM_run_of_reaches _ _ inp₀ out₀ W₀
      (TM.reaches_of_reachesIn hreach₀) hhalt₀
      (by rw [hfix₀i, hfix₀w, hfix₀o]; exact hreach₁₄) hhalt₁₄
  have hworkc : c.work = c₄.work := by rw [hwork, hwork₁₄, hwork₂₄, hwork₃₄]
  have hinc : c.input = c₄.input := by rw [hin, hin₁₄, hin₂₄, hin₃₄]
  have houtc : c.output = c₄.output := by rw [hout, hout₁₄, hout₂₄, hout₃₄]
  refine ⟨c, hreach, hhalt, ?_, ?_, ?_, ?_, fun hone => ?_⟩
  · rw [hinc, hworkc, houtc]
    have hg := htapes₄
    rw [show s + 1 + 1 + 1 + cmax * innerBodyStages N = s + nonBodyStages N cmax by
      rw [nonBodyStages]; ring] at hg
    exact ⟨fun c' _ => rfl, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2.1,
      hg.2.2.2.2.2.2.1, hg.2.2.2.2.2.2.2.1, hg.2.2.2.2.2.2.2.2.1, hg.2.2.2.2.2.2.2.2.2.1,
      fun p hp q => rfl⟩
  · intro c' hc' hcw hci
    rw [hworkc, haux₄ c' hc' hcw hci, show Wai c' = c₃.work (auxIdx jj c') from rfl,
      hwork₃a c' hci, htapes₂.1 c' hc']
  · rw [hworkc]
    exact hcnt₄
  · rw [hworkc]
    exact hbw₄
  · rw [hworkc] at hone ⊢
    obtain ⟨ha₃one, l, prevM, hlen, hpw, hmem, hne, -, hprevM, huT⟩ := hsem₄ hone
    have hnotmem := not_mem_round_succ_of_innerLoop x L g (s + 1 + 1 + 1) cc wcnt icnt Wai a₃
      Wsp u₀ N cmax hcard c₄.input c₄.work c₄.output
      ⟨htapes₄, haux₄, hbw₄, hsem₄, hspv₄⟩ hone
    have hone₃ : (c₃.work (auxIdx jj cc)).read = Γ.one := ha₃one
    have hone₂ : (c₂.work (auxIdx jj cc)).read = Γ.one := by
      rw [← hwork₃a cc (fun h => hic h.symm)]
      exact hone₃
    obtain ⟨hone₁, -, hu2⟩ := hacc₂ hone₂
    obtain ⟨hone₀, hlt, -⟩ := hacc₁ hone₁
    refine ⟨(hacc₀ hone₀).1, u₀, hnotmem, hlt, fun p hp q hq => ?_, prevM,
      fun p hp q hq => ?_⟩
    · show (c₄.work (walkReg (L.toWalkLayout.spareReg 2 p))).cells (0 + q + 1) = _
      rw [hspv₄ 2 hsp2 (by omega) p hp (0 + q + 1)]
      show (c₃.work (walkReg (L.toWalkLayout.spareReg 2 p))).cells (0 + q + 1) = _
      rw [hwork₃w]
      exact hu2 p hp q hq
    · exact hprevM p hp q hq

/-! ## The non-member loop -/

/-- **What the non-member loop carries.** An increasing list of codes outside the round, with
only the last of them on a tape — in the second spare tuple. -/
def NonMemberInv (x : List Bool) (L : WalkWidths kk jj tm x.length S wc) (g : ℕ → Bool)
    (s₀ : ℕ) (cc wcnt icnt jcnt : Fin r) (Wa : Fin r → Tape) (a₀ : Γ) (N cmax : ℕ) (j : ℕ) :
    TM.TapePred (jj + 2 + r + 1) :=
  fun inp work out =>
    WalkTapes (r := r) x L g (s₀ + j * nonBodyStages N cmax) cc
      (fun c => work (auxIdx jj c))
      (fun p q => (work (walkReg (L.toWalkLayout.codeT p))).cells q) inp work out ∧
    (∀ c, c ≠ cc → c ≠ wcnt → c ≠ icnt → c ≠ jcnt → work (auxIdx jj c) = Wa c) ∧
    (∃ bw, (work (auxIdx jj wcnt)).HasBinaryContent bw) ∧
    (∃ bi, (work (auxIdx jj icnt)).HasBinaryContent bi) ∧
    ((work (auxIdx jj cc)).read = Γ.one →
      a₀ = Γ.one ∧
      ∃ (l : List (Code tm.Q kk x.length S)) (prev : Code tm.Q kk x.length S),
        j ≤ l.length ∧ l.Pairwise (codeLt tm x S) ∧
        (∀ v ∈ l, v ∉ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 1)) ∧
        (∀ w ∈ l, codeLt tm x S w prev ∨ w = prev) ∧
        (∀ p, p < kk + 3 → HoldsBits (fun q i => (work (walkReg i)).cells q) 0
          (L.toWalkLayout.spareReg 2 p) (codeBlockScan tm x S prev p)) ∧
        ∃ w1 : Code tm.Q kk x.length S,
          ∀ p, p < kk + 3 → HoldsBits (fun q i => (work (walkReg i)).cells q) 0
            (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S w1 p))

/-- **The loop.** -/
noncomputable def nonMemberLoopTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (cc wcnt wlim icnt ilim jcnt jlim : Fin rr) : TM (jj + 2 + rr + 1) :=
  TM.binaryForTM (nonMemberBodyTM x L dc cc wcnt wlim icnt ilim)
    (auxIdx jj jcnt) (auxIdx jj jlim)

/-- **One iteration carries the invariant.** -/
theorem nonMemberLoop_body (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (hsp2 : 2 < L.toWalkLayout.spares) (g : ℕ → Bool) (s₀ : ℕ)
    (cc wcnt wlim icnt ilim jcnt jlim : Fin r)
    (hcnt : wcnt ≠ cc) (hlim : wlim ≠ cc) (hcl : wcnt ≠ wlim)
    (hic : icnt ≠ cc) (hiw : icnt ≠ wcnt) (hil : wlim ≠ icnt) (hlc : ilim ≠ cc)
    (hlw : ilim ≠ wcnt) (hli : icnt ≠ ilim)
    (hjc : jcnt ≠ cc) (hjw : jcnt ≠ wcnt) (hji : jcnt ≠ icnt) (hjwl : wlim ≠ jcnt)
    (hjil : ilim ≠ jcnt)
    (hkc : jlim ≠ cc) (hkw : jlim ≠ wcnt) (hki : jlim ≠ icnt)
    (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hspace : ∀ c, tm.ReachesCfg (tm.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hwin : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x S c)
    (hwc : wc ≤ walkScanLen tm x.length S)
    (Wa : Fin r → Tape) (a₀ : Γ) (N cmax : ℕ)
    (hcard : (NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N)).card ≤ cmax)
    (hWaN : (Wa wlim).HasBinaryNat N) (hWaC : (Wa ilim).HasBinaryNat cmax)
    (nmax value : ℕ) :
    (nonMemberBodyTM x L dc cc wcnt wlim icnt ilim).Hoare
      (TM.BinaryForFrame (auxIdx jj jcnt) (auxIdx jj jlim) nmax
        (NonMemberInv x L g s₀ cc wcnt icnt jcnt Wa a₀ N cmax) value)
      (TM.BinaryForBodyPost (auxIdx jj jcnt) (auxIdx jj jlim) nmax
        (NonMemberInv x L g s₀ cc wcnt icnt jcnt Wa a₀ N cmax) value) := by
  classical
  intro inp work out hpre
  obtain ⟨⟨htapes, haux, hbw, hbi, hsem⟩, hcnt0, hlim0, hin, hw, hout⟩ := hpre
  set prev₀ : Code tm.Q kk x.length S :=
    if h : (work (auxIdx jj cc)).read = Γ.one then ((hsem h).2).choose_spec.choose
    else cfgCode x.length S (tm.initCfg x) with hprev₀def
  have hprev₀spec : ∀ h : (work (auxIdx jj cc)).read = Γ.one,
      value ≤ ((hsem h).2).choose.length ∧
      ((hsem h).2).choose.Pairwise (codeLt tm x S) ∧
      (∀ v ∈ ((hsem h).2).choose,
        v ∉ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 1)) ∧
      (∀ w ∈ ((hsem h).2).choose, codeLt tm x S w prev₀ ∨ w = prev₀) ∧
      (∀ p, p < kk + 3 → HoldsBits (fun q i => (work (walkReg i)).cells q) 0
        (L.toWalkLayout.spareReg 2 p) (codeBlockScan tm x S prev₀ p)) ∧
      ∃ w1 : Code tm.Q kk x.length S,
        ∀ p, p < kk + 3 → HoldsBits (fun q i => (work (walkReg i)).cells q) 0
          (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S w1 p) := by
    intro h
    rw [hprev₀def, dif_pos h]
    exact ((hsem h).2).choose_spec.choose_spec
  obtain ⟨c', hreach, hhalt, htapes', hkept', hicnt', hbw', hacc'⟩ :=
    nonMemberBody_run x L dc hsp2 g (s₀ + value * nonBodyStages N cmax) cc wcnt wlim icnt ilim
      hcnt hlim hcl hic hiw hil hlc hlw hli B hB1 hB hspace hwin hwc N cmax hcard
      (fun c => work (auxIdx jj c))
      (fun p q => (work (walkReg (L.toWalkLayout.codeT p))).cells q) inp out work htapes
      hbw hbi
      (by
        show (work (auxIdx jj wlim)).HasBinaryNat N
        rw [haux wlim hlim (fun h => hcl h.symm) hil hjwl]
        exact hWaN)
      (by
        show (work (auxIdx jj ilim)).HasBinaryNat cmax
        rw [haux ilim hlc hlw (fun h => hli h.symm) hjil]
        exact hWaC)
      prev₀ (fun h => (hprev₀spec h).2.2.2.2.1) (fun h => (hprev₀spec h).2.2.2.2.2)
  have hjcnt : c'.work (auxIdx jj jcnt) = work (auxIdx jj jcnt) := by
    rw [hkept' jcnt hjc hjw hji]
  have hjlim : c'.work (auxIdx jj jlim) = work (auxIdx jj jlim) := by
    rw [hkept' jlim hkc hkw hki]
  refine ⟨c', hreach, hhalt, ?_, ?_, ?_, ?_, ?_, fun tc htc => ?_⟩
  · rw [hjcnt]
    exact hcnt0
  · rw [hjlim]
    exact hlim0
  · exact Tape.StartInvariant.read_ne_start ⟨by
      rw [show c'.input.cells 0 = (Tape.init (x.map Γ.ofBool)).cells 0 from
        congrFun htapes'.2.2.2.2.2.1 0]
      exact Tape.init_cells_zero _, fun q hq => by
      rw [show c'.input.cells q = (Tape.init (x.map Γ.ofBool)).cells q from
        congrFun htapes'.2.2.2.2.2.1 q]
      exact Tape.init_ofBool_cells_ne_start x q hq⟩ htapes'.2.2.2.2.2.2.1
  · exact fun i => (htapes'.2.1 i).read_ne_start (htapes'.2.2.1 i)
  · exact htapes'.2.2.2.2.2.2.2.1.read_ne_start htapes'.2.2.2.2.2.2.2.2.1
  obtain ⟨htSI, hth⟩ := startInvariant_of_hasBinaryNat htc
  have hupdcc : Function.update c'.work (auxIdx jj jcnt) tc (auxIdx jj cc)
      = c'.work (auxIdx jj cc) :=
    Function.update_of_ne (auxIdx_injective (fun h => hjc h.symm)) _ _
  have hstage : s₀ + value * nonBodyStages N cmax + nonBodyStages N cmax
      = s₀ + (value + 1) * nonBodyStages N cmax := by
    ring
  refine ⟨?_, fun c hc hcw hci hcj => ?_, ?_, ?_, fun hone => ?_⟩
  · rw [← hstage,
      show (fun p q => (Function.update c'.work (auxIdx jj jcnt) tc
          (walkReg (L.toWalkLayout.codeT p))).cells q)
        = (fun p q => (c'.work (walkReg (L.toWalkLayout.codeT p))).cells q) from by
          funext p q
          rw [Function.update_of_ne (walkReg_ne_auxIdx _ jcnt)]]
    exact walkTapes_update_aux x L g _ cc _ _ jcnt tc htSI (by omega)
      c'.input c'.work c'.output htapes'
  · rw [Function.update_of_ne (auxIdx_injective hcj), hkept' c hc hcw hci]
    exact haux c hc hcw hci hcj
  · obtain ⟨bw', hbw''⟩ := hbw'
    refine ⟨bw', ?_⟩
    rw [Function.update_of_ne (auxIdx_injective (fun h => hjw h.symm))]
    exact hbw''
  · refine ⟨cmax.bits, ?_⟩
    rw [Function.update_of_ne (auxIdx_injective (fun h => hji h.symm))]
    exact hicnt'.2.2
  · rw [hupdcc] at hone
    obtain ⟨holdacc, u, humem, hult, huS, w1', hw1'⟩ := hacc' hone
    obtain ⟨hlen, hpw, hmem, hbelow, -, -⟩ := hprev₀spec holdacc
    refine ⟨(hsem holdacc).1, ((hsem holdacc).2).choose ++ [u], u, ?_, ?_, ?_, ?_, ?_, w1',
      ?_⟩
    · rw [List.length_append]
      simp only [List.length_cons, List.length_nil]
      omega
    · exact pairwise_codeLt_concat hpw hbelow hult
    · intro w hw
      rcases List.mem_append.mp hw with h | h
      · exact hmem w h
      · rw [List.mem_singleton.mp h]
        exact humem
    · intro w hw
      rcases List.mem_append.mp hw with h | h
      · refine Or.inl ?_
        rcases hbelow w h with h' | h'
        · exact codeLt_trans h' hult
        · rw [h']
          exact hult
      · exact Or.inr (List.mem_singleton.mp h)
    · intro p hp q hq
      show (Function.update c'.work (auxIdx jj jcnt) tc
        (walkReg (L.toWalkLayout.spareReg 2 p))).cells (0 + q + 1) = _
      rw [Function.update_of_ne (walkReg_ne_auxIdx _ jcnt)]
      exact huS p hp q hq
    · intro p hp q hq
      show (Function.update c'.work (auxIdx jj jcnt) tc
        (walkReg (L.toWalkLayout.spareReg 1 p))).cells (0 + q + 1) = _
      rw [Function.update_of_ne (walkReg_ne_auxIdx _ jcnt)]
      exact hw1' p hp q hq

/-- **The non-member loop.** -/
theorem nonMemberLoop_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (hsp2 : 2 < L.toWalkLayout.spares) (g : ℕ → Bool) (s₀ : ℕ)
    (cc wcnt wlim icnt ilim jcnt jlim : Fin r)
    (hcnt : wcnt ≠ cc) (hlim : wlim ≠ cc) (hcl : wcnt ≠ wlim)
    (hic : icnt ≠ cc) (hiw : icnt ≠ wcnt) (hil : wlim ≠ icnt) (hlc : ilim ≠ cc)
    (hlw : ilim ≠ wcnt) (hli : icnt ≠ ilim)
    (hjc : jcnt ≠ cc) (hjw : jcnt ≠ wcnt) (hji : jcnt ≠ icnt) (hjwl : wlim ≠ jcnt)
    (hjil : ilim ≠ jcnt)
    (hkc : jlim ≠ cc) (hkw : jlim ≠ wcnt) (hki : jlim ≠ icnt) (hjk : jcnt ≠ jlim)
    (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hspace : ∀ c, tm.ReachesCfg (tm.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hwin : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x S c)
    (hwc : wc ≤ walkScanLen tm x.length S)
    (Wa : Fin r → Tape) (a₀ : Γ) (N cmax : ℕ)
    (hcard : (NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N)).card ≤ cmax)
    (hWaN : (Wa wlim).HasBinaryNat N) (hWaC : (Wa ilim).HasBinaryNat cmax) (nmax : ℕ) :
    (nonMemberLoopTM x L dc cc wcnt wlim icnt ilim jcnt jlim).Hoare
      (TM.BinaryForFrame (auxIdx jj jcnt) (auxIdx jj jlim) nmax
        (NonMemberInv x L g s₀ cc wcnt icnt jcnt Wa a₀ N cmax) 0)
      (TM.BinaryForFrame (auxIdx jj jcnt) (auxIdx jj jlim) nmax
        (NonMemberInv x L g s₀ cc wcnt icnt jcnt Wa a₀ N cmax) nmax) :=
  TM.binaryForTM_hoare (auxIdx_injective hjk) nmax _ (fun value _ =>
    nonMemberLoop_body x L dc hsp2 g s₀ cc wcnt wlim icnt ilim jcnt jlim hcnt hlim hcl hic hiw
      hil hlc hlw hli hjc hjw hji hjwl hjil hkc hkw hki B hB1 hB hspace hwin hwc Wa a₀ N cmax
      hcard hWaN hWaC nmax value)

/-- **What the non-member loop proves.** A duplicate-free list of at least `nmax` codes outside
the round — the upper half of the counting split. -/
theorem nonMemberList_of_nonMemberLoop (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (g : ℕ → Bool) (s₀ : ℕ)
    (cc wcnt icnt jcnt : Fin r) (Wa : Fin r → Tape) (a₀ : Γ) (N cmax nmax : ℕ)
    (inp : Tape) (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (hInv : NonMemberInv x L g s₀ cc wcnt icnt jcnt Wa a₀ N cmax nmax inp work out)
    (hone : (work (auxIdx jj cc)).read = Γ.one) :
    ∃ l : List (Code tm.Q kk x.length S), l.Nodup ∧
      (∀ v ∈ l, v ∉ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 1)) ∧
      nmax ≤ l.length := by
  obtain ⟨l, prev, hlen, hpw, hmem, -, -, -⟩ := (hInv.2.2.2.2 hone).2
  exact ⟨l, nodup_of_pairwise_codeLt hpw, hmem, hlen⟩

end Complexity
