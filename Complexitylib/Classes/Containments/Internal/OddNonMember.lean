/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.NonMember

/-!
# Listing the non-members of an even round

⚠️ Unreviewed by Bolton

`Complexitylib.Classes.Containments.Internal.NonMember` lists the non-members of an odd round,
certifying each by the inner counting loop over the even round below it. The counting recursion
alternates parities, so this file is the same loop one round later: the candidate's
non-membership in round `2N + 2` is certified by `Complexity.oddInnerLoopTM`, which lists the
members of round `2N + 1`. Everything else — the candidate stage, the order check, the remember
stage, and the loop plumbing — is shared verbatim.

## Main definitions

- `oddNonBodyTM`, `oddNonMemberLoopTM` — the body and the loop

## Main results

- `oddNonBody_run`, `oddNonMemberLoop_run`, `nonMemberList_of_oddNonMemberLoop`
-/

@[expose] public section

namespace Complexity

variable {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ}

/-! ## One non-member of the even round -/

/-- How many stages one iteration of the non-member loop consumes: the candidate guess, the
order check, the remember, and a whole inner counting loop. -/
def oddNonBodyStages (N cmax : ℕ) : ℕ := 1 + 1 + 1 + cmax * oddInnerStages N

/-- **One non-member of the even round**: guess a candidate and check it spells out a code, check
it is above the last non-member, remember it in the second spare, clear the inner counter, and
run the inner counting loop against it. -/
noncomputable def oddNonBodyTM {rr : ℕ} (x : List Bool)
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
          (oddInnerLoopTM x L dc cc wcnt wlim icnt ilim))))

/-- The advancing states of one non-member iteration. -/
noncomputable def oddNonBodyAdv {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (cc wcnt wlim icnt ilim : Fin rr) :
    (oddNonBodyTM x L dc cc wcnt wlim icnt ilim).Q → Bool :=
  TM.seqAdv
    (famStepAdv L (TM.twoPassTM (canonScanner tm x.length S (L.toWalkLayout.famReg 2))) 2 cc)
    (TM.seqAdv
      (famStepAdv L (TM.twoPassTM (orderOnlyScanner tm x.length S (L.toWalkLayout.spareReg 2)
        L.toWalkLayout.codeT)) 1 cc)
      (TM.seqAdv
        (famStepAdv L (TM.twoPassTM (eqScanner tm x.length S L.toWalkLayout.codeT
          (L.toWalkLayout.spareReg 2))) 4 cc)
        (TM.seqAdv (TM.seqAdv (fun _ => false) (TM.seqAdv (fun _ => false) (fun _ => false)))
          (TM.binaryForAdv (oddInnerBodyAdv x L dc cc wcnt wlim)
            (auxIdx jj icnt) (auxIdx jj ilim)))))

/-- **The whole iteration respects the guess protocol.** -/
theorem guessProtocol_oddNonBodyTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (cc wcnt wlim icnt ilim : Fin rr) :
    TM.GuessProtocol (oddNonBodyTM x L dc cc wcnt wlim icnt ilim)
      (oddNonBodyAdv x L dc cc wcnt wlim icnt ilim) :=
  TM.guessProtocol_seqTM (guessProtocol_famStepTM L _ 2 cc)
    (TM.guessProtocol_seqTM (guessProtocol_famStepTM L _ 1 cc)
      (TM.guessProtocol_seqTM (guessProtocol_famStepTM L _ 4 cc)
        (TM.guessProtocol_seqTM
          (TM.guessProtocol_resetBinaryWorkTM (auxIdx jj icnt) (auxIdx_ne_last icnt))
          (TM.guessProtocol_binaryForTM
            (guessProtocol_oddInnerBodyTM x L dc cc wcnt wlim)
            (auxIdx jj icnt) (auxIdx jj ilim) (auxIdx_ne_last icnt) (auxIdx_ne_last ilim)))))

/-- **What one non-member costs and establishes.** The candidate the stage guessed is a code
outside the round, above the last one, and now remembered in the second spare tuple. -/
theorem oddNonBody_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (hsp2 : 2 < L.toWalkLayout.spares) (g : ℕ → Bool) (s : ℕ)
    (cc wcnt wlim icnt ilim : Fin r) (hcnt : wcnt ≠ cc) (hlim : wlim ≠ cc) (hcl : wcnt ≠ wlim)
    (hic : icnt ≠ cc) (hiw : icnt ≠ wcnt) (hil : wlim ≠ icnt) (hlc : ilim ≠ cc)
    (hlw : ilim ≠ wcnt) (hli : icnt ≠ ilim) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hspace : ∀ c, tm.ReachesCfg (tm.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hwin : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x S c)
    (hwc : wc ≤ walkScanLen tm x.length S) (N cmax : ℕ)
    (hcard : (NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 1)).card ≤ cmax)
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
    ∃ c : Cfg (jj + 2 + r + 1) (oddNonBodyTM x L dc cc wcnt wlim icnt ilim).Q,
      (oddNonBodyTM x L dc cc wcnt wlim icnt ilim).reaches
        ⟨(oddNonBodyTM x L dc cc wcnt wlim icnt ilim).qstart, inp₀, W₀, out₀⟩ c ∧
      (oddNonBodyTM x L dc cc wcnt wlim icnt ilim).halted c ∧
      WalkTapes (r := r) x L g (s + oddNonBodyStages N cmax) cc
        (fun c' => c.work (auxIdx jj c'))
        (fun p q => (c.work (walkReg (L.toWalkLayout.codeT p))).cells q)
        c.input c.work c.output ∧
      (∀ c', c' ≠ cc → c' ≠ wcnt → c' ≠ icnt → c.work (auxIdx jj c') = Wa c') ∧
      (c.work (auxIdx jj icnt)).HasBinaryNat cmax ∧
      (∃ bw, (c.work (auxIdx jj wcnt)).HasBinaryContent bw) ∧
      ((c.work (auxIdx jj cc)).read = Γ.one →
        (W₀ (auxIdx jj cc)).read = Γ.one ∧
        ∃ u : Code tm.Q kk x.length S,
          u ∉ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 2) ∧
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
      (OddInnerInv x L g (s + 1 + 1 + 1) cc wcnt icnt Wai a₃ Wsp u₀ N) 0
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
    oddInnerLoop_run x L dc hsp g (s + 1 + 1 + 1) cc wcnt wlim icnt ilim hcnt hlim hcl hic hiw
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
    rw [show s + 1 + 1 + 1 + cmax * oddInnerStages N = s + oddNonBodyStages N cmax by
      rw [oddNonBodyStages]; ring] at hg
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
    have hnotmem := not_mem_round_succ_of_oddInnerLoop x L g (s + 1 + 1 + 1) cc wcnt icnt Wai a₃
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
def OddNonMemberInv (x : List Bool) (L : WalkWidths kk jj tm x.length S wc) (g : ℕ → Bool)
    (s₀ : ℕ) (cc wcnt icnt jcnt : Fin r) (Wa : Fin r → Tape) (a₀ : Γ) (N cmax : ℕ) (j : ℕ) :
    TM.TapePred (jj + 2 + r + 1) :=
  fun inp work out =>
    WalkTapes (r := r) x L g (s₀ + j * oddNonBodyStages N cmax) cc
      (fun c => work (auxIdx jj c))
      (fun p q => (work (walkReg (L.toWalkLayout.codeT p))).cells q) inp work out ∧
    (∀ c, c ≠ cc → c ≠ wcnt → c ≠ icnt → c ≠ jcnt → work (auxIdx jj c) = Wa c) ∧
    (∃ bw, (work (auxIdx jj wcnt)).HasBinaryContent bw) ∧
    (∃ bi, (work (auxIdx jj icnt)).HasBinaryContent bi) ∧
    ((work (auxIdx jj cc)).read = Γ.one →
      a₀ = Γ.one ∧
      ∃ (l : List (Code tm.Q kk x.length S)) (prev : Code tm.Q kk x.length S),
        j ≤ l.length ∧ l.Pairwise (codeLt tm x S) ∧
        (∀ v ∈ l, v ∉ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 2)) ∧
        (∀ w ∈ l, codeLt tm x S w prev ∨ w = prev) ∧
        (∀ p, p < kk + 3 → HoldsBits (fun q i => (work (walkReg i)).cells q) 0
          (L.toWalkLayout.spareReg 2 p) (codeBlockScan tm x S prev p)) ∧
        ∃ w1 : Code tm.Q kk x.length S,
          ∀ p, p < kk + 3 → HoldsBits (fun q i => (work (walkReg i)).cells q) 0
            (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S w1 p))

/-- **The loop.** -/
noncomputable def oddNonMemberLoopTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (cc wcnt wlim icnt ilim jcnt jlim : Fin rr) : TM (jj + 2 + rr + 1) :=
  TM.binaryForTM (oddNonBodyTM x L dc cc wcnt wlim icnt ilim)
    (auxIdx jj jcnt) (auxIdx jj jlim)

/-- **One iteration carries the invariant.** -/
theorem oddNonMemberLoop_body (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
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
    (hcard : (NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 1)).card ≤ cmax)
    (hWaN : (Wa wlim).HasBinaryNat N) (hWaC : (Wa ilim).HasBinaryNat cmax)
    (nmax value : ℕ) :
    (oddNonBodyTM x L dc cc wcnt wlim icnt ilim).Hoare
      (TM.BinaryForFrame (auxIdx jj jcnt) (auxIdx jj jlim) nmax
        (OddNonMemberInv x L g s₀ cc wcnt icnt jcnt Wa a₀ N cmax) value)
      (TM.BinaryForBodyPost (auxIdx jj jcnt) (auxIdx jj jlim) nmax
        (OddNonMemberInv x L g s₀ cc wcnt icnt jcnt Wa a₀ N cmax) value) := by
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
        v ∉ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 2)) ∧
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
    oddNonBody_run x L dc hsp2 g (s₀ + value * oddNonBodyStages N cmax) cc wcnt wlim icnt ilim
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
  have hstage : s₀ + value * oddNonBodyStages N cmax + oddNonBodyStages N cmax
      = s₀ + (value + 1) * oddNonBodyStages N cmax := by
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
theorem oddNonMemberLoop_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
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
    (hcard : (NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 1)).card ≤ cmax)
    (hWaN : (Wa wlim).HasBinaryNat N) (hWaC : (Wa ilim).HasBinaryNat cmax) (nmax : ℕ) :
    (oddNonMemberLoopTM x L dc cc wcnt wlim icnt ilim jcnt jlim).Hoare
      (TM.BinaryForFrame (auxIdx jj jcnt) (auxIdx jj jlim) nmax
        (OddNonMemberInv x L g s₀ cc wcnt icnt jcnt Wa a₀ N cmax) 0)
      (TM.BinaryForFrame (auxIdx jj jcnt) (auxIdx jj jlim) nmax
        (OddNonMemberInv x L g s₀ cc wcnt icnt jcnt Wa a₀ N cmax) nmax) :=
  TM.binaryForTM_hoare (auxIdx_injective hjk) nmax _ (fun value _ =>
    oddNonMemberLoop_body x L dc hsp2 g s₀ cc wcnt wlim icnt ilim jcnt jlim hcnt hlim hcl hic hiw
      hil hlc hlw hli hjc hjw hji hjwl hjil hkc hkw hki B hB1 hB hspace hwin hwc Wa a₀ N cmax
      hcard hWaN hWaC nmax value)

/-- **What the non-member loop proves.** A duplicate-free list of at least `nmax` codes outside
the round — the upper half of the counting split. -/
theorem nonMemberList_of_oddNonMemberLoop (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (g : ℕ → Bool) (s₀ : ℕ)
    (cc wcnt icnt jcnt : Fin r) (Wa : Fin r → Tape) (a₀ : Γ) (N cmax nmax : ℕ)
    (inp : Tape) (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (hInv : OddNonMemberInv x L g s₀ cc wcnt icnt jcnt Wa a₀ N cmax nmax inp work out)
    (hone : (work (auxIdx jj cc)).read = Γ.one) :
    ∃ l : List (Code tm.Q kk x.length S), l.Nodup ∧
      (∀ v ∈ l, v ∉ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 2)) ∧
      nmax ≤ l.length := by
  obtain ⟨l, prev, hlen, hpw, hmem, -, -, -⟩ := (hInv.2.2.2.2 hone).2
  exact ⟨l, nodup_of_pairwise_codeLt hpw, hmem, hlen⟩

end Complexity
