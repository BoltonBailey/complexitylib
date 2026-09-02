/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.OddHead

/-!
# Listing the members of an odd round

⚠️ Unreviewed by Bolton

`Complexity.memberLoopTM` lists the members of an even round; the counting recursion also needs
the odd ones. This is the same body — produce a member, check it is above the last, remember
it — with `Complexity.oddHeadTM` producing the member: a walk plus one more step, its result
copied back into the first tuple, so the order and remember stages are reused verbatim.

## Main definitions

- `oddBodyTM` — one member of an odd round: walk one step further, order, remember
- `OddMemberInv` — the loop's invariant: an increasing list of odd-round members
- `oddMemberLoopTM` — the loop

## Main results

- `oddBody_run`, `oddMemberLoop_body`, `oddMemberLoop_run`, `roundList_of_oddMemberLoop`
-/

@[expose] public section

namespace Complexity

variable {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ}

/-- How many stages one iteration of the odd member-listing loop consumes. -/
def oddBodyStages (N : ℕ) : ℕ := 1 + 2 * N + 1 + 1 + 1 + 1

/-- **One member of the odd round**: walk to it (one step past the even round, the result copied
back into the first tuple), check it is above the last, remember it. -/
noncomputable def oddBodyTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (cc wcnt wlim : Fin rr) :
    TM (jj + 2 + rr + 1) :=
  TM.seqTM (oddHeadTM x L dc cc wcnt wlim)
    (TM.seqTM
      (famStepTM L (TM.twoPassTM (orderOnlyScanner tm x.length S (L.toWalkLayout.spareReg 1)
        L.toWalkLayout.codeA)) 1 cc)
      (famStepTM L (TM.twoPassTM (eqScanner tm x.length S L.toWalkLayout.codeA
        (L.toWalkLayout.spareReg 1))) 3 cc))

/-- Its advancing states. -/
noncomputable def oddBodyAdv {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (cc wcnt wlim : Fin rr) :
    (oddBodyTM x L dc cc wcnt wlim).Q → Bool :=
  TM.seqAdv (oddHeadAdv x L dc cc wcnt wlim)
    (TM.seqAdv
      (famStepAdv L (TM.twoPassTM (orderOnlyScanner tm x.length S (L.toWalkLayout.spareReg 1)
        L.toWalkLayout.codeA)) 1 cc)
      (famStepAdv L (TM.twoPassTM (eqScanner tm x.length S L.toWalkLayout.codeA
        (L.toWalkLayout.spareReg 1))) 3 cc))

/-- **It respects the guess protocol.** -/
theorem guessProtocol_oddBodyTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (cc wcnt wlim : Fin rr) :
    TM.GuessProtocol (oddBodyTM x L dc cc wcnt wlim) (oddBodyAdv x L dc cc wcnt wlim) :=
  TM.guessProtocol_seqTM (guessProtocol_oddHeadTM x L dc cc wcnt wlim)
    (TM.guessProtocol_seqTM (guessProtocol_famStepTM L _ 1 cc)
      (guessProtocol_famStepTM L _ 3 cc))

/-- **What one odd member costs and establishes.** -/
theorem oddBody_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
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
    (bits : List Bool)
    (hbits : (W₀ (auxIdx jj wcnt)).HasBinaryContent bits)
    (hlimN : (Wa wlim).HasBinaryNat N) (prev : Code tm.Q kk x.length S)
    (hpre : (W₀ (auxIdx jj cc)).read = Γ.one →
      ∀ p, p < kk + 3 → HoldsBits (fun q i => (W₀ (walkReg i)).cells q) 0
        (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S prev p)) :
    ∃ (c : Cfg (jj + 2 + r + 1) (oddBodyTM x L dc cc wcnt wlim).Q) (t : ℕ),
      (oddBodyTM x L dc cc wcnt wlim).reachesIn t
        ⟨(oddBodyTM x L dc cc wcnt wlim).qstart, inp₀, W₀, out₀⟩ c ∧
      (oddBodyTM x L dc cc wcnt wlim).halted c ∧
      WalkTapes (r := r) x L g (s + oddBodyStages N) cc (fun c' => c.work (auxIdx jj c'))
        (fun p q => (c.work (walkReg (L.toWalkLayout.codeT p))).cells q)
        c.input c.work c.output ∧
      (∀ c' , c' ≠ cc → c' ≠ wcnt →
        c.work (auxIdx jj c')
          = Function.update Wa wcnt ((Tape.init ([] : List Γ)).move Dir3.right) c') ∧
      (c.work (auxIdx jj wcnt)).HasBinaryNat N ∧
      ((c.work (auxIdx jj cc)).read = Γ.one →
        (W₀ (auxIdx jj cc)).read = Γ.one ∧
        ∃ v : Code tm.Q kk x.length S,
          v ∈ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 1) ∧
          codeLt tm x S prev v ∧
          ∀ p, p < kk + 3 → HoldsBits (fun q i => (c.work (walkReg i)).cells q) 0
            (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S v p)) := by
  classical
  obtain ⟨cB, tB, hreachB, hhaltB, htapesB, hkeptB, hspareB, hwcntB, haccB⟩ :=
    oddHead_run x L dc g s cc wcnt wlim hcnt hlim hcl B hB1 hB hspace hwin hwc N Wa Wt
      inp₀ out₀ W₀ htapes bits hbits hlimN
  obtain ⟨hfixI, hfixW, hfixO⟩ :=
    walkTapes_transition_eq x L g (s + 1 + 2 * N + 1 + 1) cc (fun c' => cB.work (auxIdx jj c'))
      (fun p q => (cB.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      cB.input cB.work cB.output htapesB
  set v₀ : Code tm.Q kk x.length S :=
    if h : (cB.work (auxIdx jj cc)).read = Γ.one then (haccB h).2.choose
    else cfgCode x.length S (tm.initCfg x) with hv₀def
  have hv₀spec : ∀ h : (cB.work (auxIdx jj cc)).read = Γ.one,
      v₀ ∈ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 1) ∧
      (∀ p, p < kk + 3 → HoldsBits (fun q i => (cB.work (walkReg i)).cells q) 0
        (L.toWalkLayout.codeA p) (codeBlockScan tm x S v₀ p)) ∧
      cB.input = ⟨max v₀.2.1.val 1, (Tape.init (x.map Γ.ofBool)).cells⟩ := by
    intro h
    rw [hv₀def, dif_pos h]
    exact (haccB h).2.choose_spec
  obtain ⟨cO, tO, -, hreachO, hhaltO, htapesO, hinpO, haccO⟩ :=
    orderOnlyStep_run x L hsp g (s + 1 + 2 * N + 1 + 1) cc B hB1 hB
      (fun c' => cB.work (auxIdx jj c'))
      (fun p q => (cB.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      cB.input cB.output cB.work htapesB prev v₀ (fun h => by
        refine ⟨fun p hp q hq => ?_, holdsCodeTail_of_blocks tm x S _ L.toWalkLayout.codeA v₀
          ((hv₀spec h).2.1)⟩
        show (cB.work (walkReg (L.toWalkLayout.spareReg 1 p))).cells (0 + q + 1) = _
        rw [hspareB 1 hsp p hp (0 + q + 1)]
        exact hpre (haccB h).1 p hp q hq)
  obtain ⟨hfixI', hfixW', hfixO'⟩ :=
    walkTapes_transition_eq x L g (s + 1 + 2 * N + 1 + 1 + 1) cc
      (fun c' => cB.work (auxIdx jj c'))
      (fun p q => (cB.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      cO.input cO.work cO.output htapesO
  obtain ⟨cC, tC, -, hreachC, hhaltC, htapesC, hinpC, haccC⟩ :=
    copyOnlyStep_run x L hsp g (s + 1 + 2 * N + 1 + 1 + 1) cc B hB1 hB
      (fun c' => cB.work (auxIdx jj c'))
      (fun p q => (cB.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      cO.input cO.output cO.work htapesO v₀ (fun h => (haccO h).2.2)
  obtain ⟨cOC, hreachOC, hhaltOC, hinOC, hworkOC, houtOC⟩ :=
    seqTM_run_of_runs _ _ cB.input cB.output cB.work hreachO hhaltO
      (by rw [hfixI', hfixW', hfixO']; exact hreachC) hhaltC
  obtain ⟨c, hreach, hhalt, hin, hwork, hout⟩ :=
    seqTM_run_of_runs _ _ inp₀ out₀ W₀ hreachB hhaltB
      (by rw [hfixI, hfixW, hfixO]; exact hreachOC) hhaltOC
  have hworkc : c.work = cC.work := by rw [hwork, hworkOC]
  have hinc : c.input = cC.input := by rw [hin, hinOC]
  have houtc : c.output = cC.output := by rw [hout, houtOC]
  refine ⟨c, tB + 1 + (tO + 1 + tC), hreach, hhalt, ?_, ?_, ?_, fun hone => ?_⟩
  · rw [hinc, hworkc, houtc]
    refine ⟨fun c' _ => rfl, htapesC.2.1, htapesC.2.2.1, htapesC.2.2.2.1, htapesC.2.2.2.2.1,
      htapesC.2.2.2.2.2.1, htapesC.2.2.2.2.2.2.1, htapesC.2.2.2.2.2.2.2.1,
      htapesC.2.2.2.2.2.2.2.2.1, ?_, fun p hp q => rfl⟩
    have hg := htapesC.2.2.2.2.2.2.2.2.2.1
    rw [show s + 1 + 2 * N + 1 + 1 + 1 + 1 = s + oddBodyStages N by
      rw [oddBodyStages]; ring] at hg
    exact hg
  · intro c' hc' hcn
    rw [hworkc, show cC.work (auxIdx jj c') = cB.work (auxIdx jj c') from htapesC.1 c' hc']
    exact hkeptB c' hc' hcn
  · rw [hworkc, show cC.work (auxIdx jj wcnt) = cB.work (auxIdx jj wcnt) from
      htapesC.1 wcnt hcnt]
    exact hwcntB
  · rw [hworkc] at hone ⊢
    obtain ⟨holdO, hvS⟩ := haccC hone
    obtain ⟨holdB, hlt, -⟩ := haccO holdO
    exact ⟨(haccB holdB).1, v₀, (hv₀spec holdB).1, hlt, hvS⟩

/-- **What the odd member-listing loop carries.** -/
def OddMemberInv (x : List Bool) (L : WalkWidths kk jj tm x.length S wc) (g : ℕ → Bool)
    (s₀ : ℕ) (cc wcnt icnt : Fin r) (Wa : Fin r → Tape) (a₀ : Γ) (N : ℕ) (j : ℕ) :
    TM.TapePred (jj + 2 + r + 1) :=
  fun inp work out =>
    WalkTapes (r := r) x L g (s₀ + j * oddBodyStages N) cc (fun c => work (auxIdx jj c))
      (fun p q => (work (walkReg (L.toWalkLayout.codeT p))).cells q) inp work out ∧
    (∀ c, c ≠ cc → c ≠ wcnt → c ≠ icnt → work (auxIdx jj c) = Wa c) ∧
    (∃ bits, (work (auxIdx jj wcnt)).HasBinaryContent bits) ∧
    ((work (auxIdx jj cc)).read = Γ.one →
      a₀ = Γ.one ∧
      ∃ (l : List (Code tm.Q kk x.length S)) (prev : Code tm.Q kk x.length S),
        j ≤ l.length ∧ l.Pairwise (codeLt tm x S) ∧
        (∀ v ∈ l, v ∈ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 1)) ∧
        (∀ w ∈ l, codeLt tm x S w prev ∨ w = prev) ∧
        ∀ p, p < kk + 3 → HoldsBits (fun q i => (work (walkReg i)).cells q) 0
          (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S prev p))

/-- **The loop.** -/
noncomputable def oddMemberLoopTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (cc wcnt wlim icnt ilim : Fin rr) :
    TM (jj + 2 + rr + 1) :=
  TM.binaryForTM (oddBodyTM x L dc cc wcnt wlim) (auxIdx jj icnt) (auxIdx jj ilim)

/-- **One iteration carries the invariant.** -/
theorem oddMemberLoop_body (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (hsp : 1 < L.toWalkLayout.spares) (g : ℕ → Bool) (s₀ : ℕ)
    (cc wcnt wlim icnt ilim : Fin r) (hcnt : wcnt ≠ cc) (hlim : wlim ≠ cc) (hcl : wcnt ≠ wlim)
    (hic : icnt ≠ cc) (hiw : icnt ≠ wcnt) (hil : wlim ≠ icnt) (hlc : ilim ≠ cc)
    (hlw : ilim ≠ wcnt) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hspace : ∀ c, tm.ReachesCfg (tm.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hwin : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x S c)
    (hwc : wc ≤ walkScanLen tm x.length S) (Wa : Fin r → Tape) (a₀ : Γ) (N : ℕ)
    (hWaN : (Wa wlim).HasBinaryNat N) (cmax value : ℕ) :
    (oddBodyTM x L dc cc wcnt wlim).Hoare
      (TM.BinaryForFrame (auxIdx jj icnt) (auxIdx jj ilim) cmax
        (OddMemberInv x L g s₀ cc wcnt icnt Wa a₀ N) value)
      (TM.BinaryForBodyPost (auxIdx jj icnt) (auxIdx jj ilim) cmax
        (OddMemberInv x L g s₀ cc wcnt icnt Wa a₀ N) value) := by
  classical
  intro inp work out hpre
  obtain ⟨⟨htapes, haux, ⟨bits, hbits⟩, hsem⟩, hcnt0, hlim0, hin, hw, hout⟩ := hpre
  set prev₀ : Code tm.Q kk x.length S :=
    if h : (work (auxIdx jj cc)).read = Γ.one then ((hsem h).2).choose_spec.choose
    else cfgCode x.length S (tm.initCfg x) with hprev₀def
  have hprev₀spec : ∀ h : (work (auxIdx jj cc)).read = Γ.one,
      value ≤ ((hsem h).2).choose.length ∧
      ((hsem h).2).choose.Pairwise (codeLt tm x S) ∧
      (∀ v ∈ ((hsem h).2).choose,
        v ∈ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 1)) ∧
      (∀ w ∈ ((hsem h).2).choose, codeLt tm x S w prev₀ ∨ w = prev₀) ∧
      ∀ p, p < kk + 3 → HoldsBits (fun q i => (work (walkReg i)).cells q) 0
        (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S prev₀ p) := by
    intro h
    rw [hprev₀def, dif_pos h]
    exact ((hsem h).2).choose_spec.choose_spec
  obtain ⟨c', t, hreach, hhalt, htapes', hkept', hwcnt', hacc'⟩ :=
    oddBody_run x L dc hsp g (s₀ + value * oddBodyStages N) cc wcnt wlim hcnt hlim hcl
      B hB1 hB hspace hwin hwc N (fun c => work (auxIdx jj c))
      (fun p q => (work (walkReg (L.toWalkLayout.codeT p))).cells q) inp out work htapes bits
      hbits
      (by
        show (work (auxIdx jj wlim)).HasBinaryNat N
        rw [haux wlim hlim (fun h => hcl h.symm) hil]
        exact hWaN) prev₀ (fun h => (hprev₀spec h).2.2.2.2)
  have hicnt : c'.work (auxIdx jj icnt) = work (auxIdx jj icnt) := by
    rw [hkept' icnt hic hiw, Function.update_of_ne hiw]
  have hilim : c'.work (auxIdx jj ilim) = work (auxIdx jj ilim) := by
    rw [hkept' ilim hlc hlw, Function.update_of_ne hlw]
  refine ⟨c', TM.reaches_of_reachesIn hreach, hhalt, ?_, ?_, ?_, ?_, ?_, fun tc htc => ?_⟩
  · rw [hicnt]
    exact hcnt0
  · rw [hilim]
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
  have hupdcc : Function.update c'.work (auxIdx jj icnt) tc (auxIdx jj cc)
      = c'.work (auxIdx jj cc) :=
    Function.update_of_ne (auxIdx_injective (fun h => hic h.symm)) _ _
  have hstage : s₀ + value * oddBodyStages N + oddBodyStages N
      = s₀ + (value + 1) * oddBodyStages N := by
    ring
  refine ⟨?_, fun c hc hcw hci => ?_, ⟨N.bits, ?_⟩, fun hone => ?_⟩
  · rw [← hstage,
      show (fun p q => (Function.update c'.work (auxIdx jj icnt) tc
          (walkReg (L.toWalkLayout.codeT p))).cells q)
        = (fun p q => (c'.work (walkReg (L.toWalkLayout.codeT p))).cells q) from by
          funext p q
          rw [Function.update_of_ne (walkReg_ne_auxIdx _ icnt)]]
    exact walkTapes_update_aux x L g _ cc _ _ icnt tc htSI (by omega)
      c'.input c'.work c'.output htapes'
  · rw [Function.update_of_ne (auxIdx_injective hci), hkept' c hc hcw,
      Function.update_of_ne hcw]
    exact haux c hc hcw hci
  · rw [Function.update_of_ne (auxIdx_injective (fun h => hiw h.symm))]
    exact hwcnt'.2.2
  · rw [hupdcc] at hone
    obtain ⟨holdacc, v, hvmem, hvlt, hvS⟩ := hacc' hone
    obtain ⟨hlen, hpw, hmem, hbelow, -⟩ := hprev₀spec holdacc
    refine ⟨(hsem holdacc).1, ((hsem holdacc).2).choose ++ [v], v, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.length_append]
      simp only [List.length_cons, List.length_nil]
      omega
    · exact pairwise_codeLt_concat hpw hbelow hvlt
    · intro w hw
      rcases List.mem_append.mp hw with h | h
      · exact hmem w h
      · rw [List.mem_singleton.mp h]
        exact hvmem
    · intro w hw
      rcases List.mem_append.mp hw with h | h
      · refine Or.inl ?_
        rcases hbelow w h with h' | h'
        · exact codeLt_trans h' hvlt
        · rw [h']
          exact hvlt
      · exact Or.inr (List.mem_singleton.mp h)
    · intro p hp q hq
      show (Function.update c'.work (auxIdx jj icnt) tc
        (walkReg (L.toWalkLayout.spareReg 1 p))).cells (0 + q + 1) = _
      rw [Function.update_of_ne (walkReg_ne_auxIdx _ icnt)]
      exact hvS p hp q hq

/-- **The odd member-listing loop.** -/
theorem oddMemberLoop_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (hsp : 1 < L.toWalkLayout.spares) (g : ℕ → Bool) (s₀ : ℕ)
    (cc wcnt wlim icnt ilim : Fin r) (hcnt : wcnt ≠ cc) (hlim : wlim ≠ cc) (hcl : wcnt ≠ wlim)
    (hic : icnt ≠ cc) (hiw : icnt ≠ wcnt) (hil : wlim ≠ icnt) (hlc : ilim ≠ cc)
    (hlw : ilim ≠ wcnt) (hli : icnt ≠ ilim) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hspace : ∀ c, tm.ReachesCfg (tm.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hwin : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x S c)
    (hwc : wc ≤ walkScanLen tm x.length S) (Wa : Fin r → Tape) (a₀ : Γ) (N : ℕ)
    (hWaN : (Wa wlim).HasBinaryNat N) (cmax : ℕ) :
    (oddMemberLoopTM x L dc cc wcnt wlim icnt ilim).Hoare
      (TM.BinaryForFrame (auxIdx jj icnt) (auxIdx jj ilim) cmax
        (OddMemberInv x L g s₀ cc wcnt icnt Wa a₀ N) 0)
      (TM.BinaryForFrame (auxIdx jj icnt) (auxIdx jj ilim) cmax
        (OddMemberInv x L g s₀ cc wcnt icnt Wa a₀ N) cmax) :=
  TM.binaryForTM_hoare (auxIdx_injective hli) cmax _ (fun value _ =>
    oddMemberLoop_body x L dc hsp g s₀ cc wcnt wlim icnt ilim hcnt hlim hcl hic hiw hil hlc
      hlw B hB1 hB hspace hwin hwc Wa a₀ N hWaN cmax value)

/-- **What the odd member-listing loop proves.** A round list for the odd round, provided the
loop ran as many times as the round has members. -/
theorem roundList_of_oddMemberLoop (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (g : ℕ → Bool) (s₀ : ℕ) (cc wcnt icnt : Fin r) (Wa : Fin r → Tape) (a₀ : Γ) (N cmax : ℕ)
    (hcard : (NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 1)).card
      ≤ cmax)
    (inp : Tape) (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (hInv : OddMemberInv x L g s₀ cc wcnt icnt Wa a₀ N cmax inp work out)
    (hone : (work (auxIdx jj cc)).read = Γ.one) :
    ∃ l : List (Code tm.Q kk x.length S),
      NTM.RoundList tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 1) l := by
  obtain ⟨l, prev, hlen, hpw, hmem, -, -⟩ := (hInv.2.2.2 hone).2
  exact ⟨l, roundList_of_pairwise hpw hmem (by omega)⟩

/-- **The raw member list of the odd round**, for the counting split. -/
theorem memberList_of_oddMemberLoop (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (g : ℕ → Bool) (s₀ : ℕ) (cc wcnt icnt : Fin r) (Wa : Fin r → Tape) (a₀ : Γ) (N cmax : ℕ)
    (inp : Tape) (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (hInv : OddMemberInv x L g s₀ cc wcnt icnt Wa a₀ N cmax inp work out)
    (hone : (work (auxIdx jj cc)).read = Γ.one) :
    ∃ l : List (Code tm.Q kk x.length S), l.Nodup ∧
      (∀ v ∈ l, v ∈ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 1)) ∧
      cmax ≤ l.length := by
  obtain ⟨l, prev, hlen, hpw, hmem, -, -⟩ := (hInv.2.2.2 hone).2
  exact ⟨l, nodup_of_pairwise_codeLt hpw, hmem, hlen⟩

end Complexity
