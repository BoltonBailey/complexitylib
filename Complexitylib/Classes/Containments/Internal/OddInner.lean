/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.OddMember

/-!
# The inner counting loop over an odd round

⚠️ Unreviewed by Bolton

`Complexity.innerLoopTM` certifies that a code is not in round `2N + 1` by listing the members
of round `2N`. The counting recursion also needs the next step: non-membership in round
`2N + 2`, certified by listing the members of round `2N + 1`. This is the same iteration with
`Complexity.oddHeadTM` producing the member — a walk plus one more step, its result copied back
into the first tuple — so `Complexity.innerTailTM` and its contract are reused verbatim.

## Main definitions

- `oddInnerBodyTM` — one entry: walk one step further, then the four checks
- `OddInnerInv` — the loop's invariant: an increasing list of odd-round members, none of them
  the code under test and none stepping to it
- `oddInnerLoopTM` — the loop

## Main results

- `oddInnerBody_run`, `oddInnerLoop_body`, `oddInnerLoop_run`
- `not_mem_round_succ_of_oddInnerLoop` — what the loop establishes about the code under test
-/

@[expose] public section

namespace Complexity

variable {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ}

/-- How many stages one iteration of the odd inner loop consumes from the guess stream. -/
def oddInnerStages (N : ℕ) : ℕ := 1 + 2 * N + 1 + 1 + 1 + 1 + 1 + 1

/-- **One entry of the odd inner loop**: produce a member of the odd round, then check it. -/
noncomputable def oddInnerBodyTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (cc wcnt wlim : Fin rr) :
    TM (jj + 2 + rr + 1) :=
  TM.seqTM (oddHeadTM x L dc cc wcnt wlim) (innerTailTM x L dc cc)

/-- Its advancing states. -/
noncomputable def oddInnerBodyAdv {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (cc wcnt wlim : Fin rr) :
    (oddInnerBodyTM x L dc cc wcnt wlim).Q → Bool :=
  TM.seqAdv (oddHeadAdv x L dc cc wcnt wlim) (innerTailAdv x L dc cc)

/-- **It respects the guess protocol.** -/
theorem guessProtocol_oddInnerBodyTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (cc wcnt wlim : Fin rr) :
    TM.GuessProtocol (oddInnerBodyTM x L dc cc wcnt wlim)
      (oddInnerBodyAdv x L dc cc wcnt wlim) :=
  TM.guessProtocol_seqTM (guessProtocol_oddHeadTM x L dc cc wcnt wlim)
    (guessProtocol_innerTailTM x L dc cc)

/-- **What one iteration of the odd inner loop establishes.** If the accumulator survives it,
the machine has met a member of the odd round that is above the one it remembered, is not the
code under test, and does not step to it under either choice — and it now remembers that member
instead. -/
theorem oddInnerBody_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
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
    (hlimN : (Wa wlim).HasBinaryNat N)
    (prev u : Code tm.Q kk x.length S)
    (hpre : (W₀ (auxIdx jj cc)).read = Γ.one →
      (∀ p, p < kk + 3 → HoldsBits (fun q i => (W₀ (walkReg i)).cells q) 0
        (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S prev p)) ∧
      ∀ p, p < kk + 3 → HoldsBits (fun q i => (W₀ (walkReg i)).cells q) 0
        (L.toWalkLayout.codeT p) (codeBlockScan tm x S u p)) :
    ∃ (c : Cfg (jj + 2 + r + 1) (oddInnerBodyTM x L dc cc wcnt wlim).Q) (t : ℕ),
      (oddInnerBodyTM x L dc cc wcnt wlim).reachesIn t
        ⟨(oddInnerBodyTM x L dc cc wcnt wlim).qstart, inp₀, W₀, out₀⟩ c ∧
      (oddInnerBodyTM x L dc cc wcnt wlim).halted c ∧
      WalkTapes (r := r) x L g (s + 1 + 2 * N + 1 + 1 + 1 + 1 + 1 + 1) cc
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
          v ∈ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 1) ∧
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
  obtain ⟨cT, tT, -, hreachT, hhaltT, htapesT, haccT, hspT⟩ :=
    innerTail_run x L dc hsp g (s + 1 + 2 * N + 1 + 1) cc B hB1 hB
      (fun c' => cB.work (auxIdx jj c'))
      (fun p q => (cB.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      cB.input cB.output cB.work htapesB prev v₀ u (fun h => by
        obtain ⟨hvmem, hvA, hvinp⟩ := hv₀spec h
        obtain ⟨hprevB, huB⟩ := hpre (haccB h).1
        refine ⟨fun p hp q hq => ?_,
          holdsCodeTail_of_blocks tm x S _ L.toWalkLayout.codeA v₀ hvA,
          fun p hp q hq => ?_, hvinp, fun P => ?_⟩
        · show (cB.work (walkReg (L.toWalkLayout.spareReg 1 p))).cells (0 + q + 1) = _
          rw [hspareB 1 hsp p hp (0 + q + 1)]
          exact hprevB p hp q hq
        · have hk := hspareB 0 (by have := L.toWalkLayout.spares_pos; omega) p hp
            (0 + q + 1)
          rw [L.toWalkLayout.spareReg_zero] at hk
          show (cB.work (walkReg (L.toWalkLayout.codeT p))).cells (0 + q + 1) = _
          rw [hk]
          exact huB p hp q hq
        · exact clampIn_deferred x S hspace hwin v₀ (2 * N + 1) hvmem P)
  obtain ⟨c, hreach, hhalt, hin, hwork, hout⟩ :=
    seqTM_run_of_runs _ _ inp₀ out₀ W₀ hreachB hhaltB
      (by rw [hfixI, hfixW, hfixO]; exact hreachT) hhaltT
  have hspare : ∀ n, n < L.toWalkLayout.spares → n ≠ 1 → ∀ p, p < kk + 3 → ∀ q,
      (c.work (walkReg (L.toWalkLayout.spareReg n p))).cells q
        = (W₀ (walkReg (L.toWalkLayout.spareReg n p))).cells q := by
    intro n hn hne p hp q
    rw [hwork, hspT n hn hne p hp q]
    exact hspareB n hn p hp q
  refine ⟨c, tB + 1 + tT, hreach, hhalt, ?_, ?_, ?_, ⟨fun hone => ?_, hspare⟩⟩
  · rw [hin, hwork, hout]
    exact ⟨fun c' _ => rfl, htapesT.2.1, htapesT.2.2.1, htapesT.2.2.2.1, htapesT.2.2.2.2.1,
      htapesT.2.2.2.2.2.1, htapesT.2.2.2.2.2.2.1, htapesT.2.2.2.2.2.2.2.1,
      htapesT.2.2.2.2.2.2.2.2.1, htapesT.2.2.2.2.2.2.2.2.2.1, fun p hp q => rfl⟩
  · intro c' hc' hcn
    rw [hwork]
    rw [show cT.work (auxIdx jj c') = cB.work (auxIdx jj c') from htapesT.1 c' hc']
    exact hkeptB c' hc' hcn
  · rw [hwork, show cT.work (auxIdx jj wcnt) = cB.work (auxIdx jj wcnt) from
      htapesT.1 wcnt hcnt]
    exact hwcntB
  · rw [hwork] at hone ⊢
    obtain ⟨holdB, hlt, hnev, hne0, hne1, huT, hvS⟩ := haccT hone
    exact ⟨(haccB holdB).1, v₀, (hv₀spec holdB).1, hlt, hnev, hne0, hne1, huT, hvS⟩

/-- **What the odd inner loop carries.** The tapes hold the last member met; the list of all of
them lives here, in the invariant, and nowhere else. -/
def OddInnerInv (x : List Bool) (L : WalkWidths kk jj tm x.length S wc) (g : ℕ → Bool)
    (s₀ : ℕ) (cc wcnt icnt : Fin r) (Wa : Fin r → Tape) (a₀ : Γ) (Wsp : ℕ → ℕ → ℕ → Γ)
    (u : Code tm.Q kk x.length S) (N : ℕ) (j : ℕ) : TM.TapePred (jj + 2 + r + 1) :=
  fun inp work out =>
    WalkTapes (r := r) x L g (s₀ + j * oddInnerStages N) cc (fun c => work (auxIdx jj c))
      (fun p q => (work (walkReg (L.toWalkLayout.codeT p))).cells q) inp work out ∧
    (∀ c, c ≠ cc → c ≠ wcnt → c ≠ icnt → work (auxIdx jj c) = Wa c) ∧
    (∃ bits, (work (auxIdx jj wcnt)).HasBinaryContent bits) ∧
    ((work (auxIdx jj cc)).read = Γ.one →
      a₀ = Γ.one ∧
      ∃ (l : List (Code tm.Q kk x.length S)) (prev : Code tm.Q kk x.length S),
        j ≤ l.length ∧ l.Pairwise (codeLt tm x S) ∧
        (∀ v ∈ l, v ∈ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 1)) ∧
        (∀ v ∈ l, u ≠ v ∧ u ≠ succCode tm x S false v ∧ u ≠ succCode tm x S true v) ∧
        (∀ w ∈ l, codeLt tm x S w prev ∨ w = prev) ∧
        (∀ p, p < kk + 3 → HoldsBits (fun q i => (work (walkReg i)).cells q) 0
          (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S prev p)) ∧
        ∀ p, p < kk + 3 → HoldsBits (fun q i => (work (walkReg i)).cells q) 0
          (L.toWalkLayout.codeT p) (codeBlockScan tm x S u p)) ∧
    (∀ n, n < L.toWalkLayout.spares → n ≠ 1 → ∀ p, p < kk + 3 → ∀ q,
      (work (walkReg (L.toWalkLayout.spareReg n p))).cells q = Wsp n p q)

/-- **The loop.** -/
noncomputable def oddInnerLoopTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (cc wcnt wlim icnt ilim : Fin rr) :
    TM (jj + 2 + rr + 1) :=
  TM.binaryForTM (oddInnerBodyTM x L dc cc wcnt wlim) (auxIdx jj icnt) (auxIdx jj ilim)

/-- **One iteration carries the invariant.** The member the body met is appended to the list. -/
theorem oddInnerLoop_body (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (hsp : 1 < L.toWalkLayout.spares) (g : ℕ → Bool) (s₀ : ℕ)
    (cc wcnt wlim icnt ilim : Fin r) (hcnt : wcnt ≠ cc) (hlim : wlim ≠ cc) (hcl : wcnt ≠ wlim)
    (hic : icnt ≠ cc) (hiw : icnt ≠ wcnt) (hil : wlim ≠ icnt) (hlc : ilim ≠ cc)
    (hlw : ilim ≠ wcnt) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hspace : ∀ c, tm.ReachesCfg (tm.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hwin : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x S c)
    (hwc : wc ≤ walkScanLen tm x.length S) (Wa : Fin r → Tape) (a₀ : Γ) (N : ℕ)
    (hWaN : (Wa wlim).HasBinaryNat N) (Wsp : ℕ → ℕ → ℕ → Γ) (u : Code tm.Q kk x.length S)
    (cmax value : ℕ) :
    (oddInnerBodyTM x L dc cc wcnt wlim).Hoare
      (TM.BinaryForFrame (auxIdx jj icnt) (auxIdx jj ilim) cmax
        (OddInnerInv x L g s₀ cc wcnt icnt Wa a₀ Wsp u N) value)
      (TM.BinaryForBodyPost (auxIdx jj icnt) (auxIdx jj ilim) cmax
        (OddInnerInv x L g s₀ cc wcnt icnt Wa a₀ Wsp u N) value) := by
  classical
  intro inp work out hpre
  obtain ⟨⟨htapes, haux, ⟨bits, hbits⟩, hsem, hspv⟩, hcnt0, hlim0, hin, hw, hout⟩ := hpre
  set prev₀ : Code tm.Q kk x.length S :=
    if h : (work (auxIdx jj cc)).read = Γ.one then ((hsem h).2).choose_spec.choose
    else cfgCode x.length S (tm.initCfg x) with hprev₀def
  have hprev₀spec : ∀ h : (work (auxIdx jj cc)).read = Γ.one,
      value ≤ ((hsem h).2).choose.length ∧
      ((hsem h).2).choose.Pairwise (codeLt tm x S) ∧
      (∀ v ∈ ((hsem h).2).choose,
        v ∈ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 1)) ∧
      (∀ v ∈ ((hsem h).2).choose, u ≠ v ∧ u ≠ succCode tm x S false v ∧
        u ≠ succCode tm x S true v) ∧
      (∀ w ∈ ((hsem h).2).choose, codeLt tm x S w prev₀ ∨ w = prev₀) ∧
      (∀ p, p < kk + 3 → HoldsBits (fun q i => (work (walkReg i)).cells q) 0
        (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S prev₀ p)) ∧
      ∀ p, p < kk + 3 → HoldsBits (fun q i => (work (walkReg i)).cells q) 0
        (L.toWalkLayout.codeT p) (codeBlockScan tm x S u p) := by
    intro h
    rw [hprev₀def, dif_pos h]
    exact ((hsem h).2).choose_spec.choose_spec
  obtain ⟨c', t, hreach, hhalt, htapes', hkept', hwcnt', hacc', hspb⟩ :=
    oddInnerBody_run x L dc hsp g (s₀ + value * oddInnerStages N) cc wcnt wlim hcnt hlim hcl
      B hB1 hB hspace hwin hwc N (fun c => work (auxIdx jj c))
      (fun p q => (work (walkReg (L.toWalkLayout.codeT p))).cells q) inp out work htapes
      bits hbits
      (by
        show (work (auxIdx jj wlim)).HasBinaryNat N
        rw [haux wlim hlim (fun h => hcl h.symm) hil]
        exact hWaN) prev₀ u
      (fun h => ⟨(hprev₀spec h).2.2.2.2.2.1, (hprev₀spec h).2.2.2.2.2.2⟩)
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
  have hstage : s₀ + value * oddInnerStages N + 1 + 2 * N + 1 + 1 + 1 + 1 + 1 + 1
      = s₀ + (value + 1) * oddInnerStages N := by
    rw [oddInnerStages]
    ring
  refine ⟨?_, fun c hc hcw hci => ?_, ⟨N.bits, ?_⟩, fun hone => ?_,
    fun n hn hne p hp q => ?_⟩
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
    obtain ⟨holdacc, v, hvmem, hvlt, hvne, hvne0, hvne1, huT, hvS⟩ := hacc' hone
    obtain ⟨hlen, hpw, hmem, hne, hbelow, -, -⟩ := hprev₀spec holdacc
    refine ⟨(hsem holdacc).1, ((hsem holdacc).2).choose ++ [v], v, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      · exact hne w h
      · rw [List.mem_singleton.mp h]
        exact ⟨hvne, hvne0, hvne1⟩
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
    · intro p hp q hq
      show (Function.update c'.work (auxIdx jj icnt) tc
        (walkReg (L.toWalkLayout.codeT p))).cells (0 + q + 1) = _
      rw [Function.update_of_ne (walkReg_ne_auxIdx _ icnt)]
      exact huT p hp q hq
  · rw [Function.update_of_ne (walkReg_ne_auxIdx _ icnt), hspb n hn hne p hp q]
    exact hspv n hn hne p hp q

/-- **The odd inner loop.** After `cmax` iterations the machine has met `cmax` distinct members
of the odd round, none of them the code under test and none of them a step away from it —
provided the accumulator survived. -/
theorem oddInnerLoop_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (hsp : 1 < L.toWalkLayout.spares) (g : ℕ → Bool) (s₀ : ℕ)
    (cc wcnt wlim icnt ilim : Fin r) (hcnt : wcnt ≠ cc) (hlim : wlim ≠ cc) (hcl : wcnt ≠ wlim)
    (hic : icnt ≠ cc) (hiw : icnt ≠ wcnt) (hil : wlim ≠ icnt) (hlc : ilim ≠ cc)
    (hlw : ilim ≠ wcnt) (hli : icnt ≠ ilim) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hspace : ∀ c, tm.ReachesCfg (tm.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hwin : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x S c)
    (hwc : wc ≤ walkScanLen tm x.length S) (Wa : Fin r → Tape) (a₀ : Γ) (N : ℕ)
    (hWaN : (Wa wlim).HasBinaryNat N) (Wsp : ℕ → ℕ → ℕ → Γ) (u : Code tm.Q kk x.length S)
    (cmax : ℕ) :
    (oddInnerLoopTM x L dc cc wcnt wlim icnt ilim).Hoare
      (TM.BinaryForFrame (auxIdx jj icnt) (auxIdx jj ilim) cmax
        (OddInnerInv x L g s₀ cc wcnt icnt Wa a₀ Wsp u N) 0)
      (TM.BinaryForFrame (auxIdx jj icnt) (auxIdx jj ilim) cmax
        (OddInnerInv x L g s₀ cc wcnt icnt Wa a₀ Wsp u N) cmax) :=
  TM.binaryForTM_hoare (auxIdx_injective hli) cmax _ (fun value _ =>
    oddInnerLoop_body x L dc hsp g s₀ cc wcnt wlim icnt ilim hcnt hlim hcl hic hiw hil hlc hlw
      B hB1 hB hspace hwin hwc Wa a₀ N hWaN Wsp u cmax value)

/-- **What the odd inner loop proves about the code under test.** With the odd round's size on
the limit tape, the members the loop met are all of them, so a code the loop never met — and it
met none equal to the code under test, nor stepping to it — is not in the round after the odd
one. -/
theorem not_mem_round_succ_of_oddInnerLoop (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (g : ℕ → Bool) (s₀ : ℕ)
    (cc wcnt icnt : Fin r) (Wa : Fin r → Tape) (a₀ : Γ) (Wsp : ℕ → ℕ → ℕ → Γ)
    (u : Code tm.Q kk x.length S) (N cmax : ℕ)
    (hcard : (NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 1)).card
      ≤ cmax)
    (inp : Tape) (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (hInv : OddInnerInv x L g s₀ cc wcnt icnt Wa a₀ Wsp u N cmax inp work out)
    (hone : (work (auxIdx jj cc)).read = Γ.one) :
    u ∉ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 2) := by
  obtain ⟨l, prev, hlen, hpw, hmem, hne, -, -, -⟩ := (hInv.2.2.2.1 hone).2
  exact not_mem_round_succ_of_list u hpw hmem (by omega) hne

end Complexity
