/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.OddNonMember

/-!
# The final acceptance scan

⚠️ Unreviewed by Bolton

Once the counting recursion has certified the size of the last round, the machine lists that
round one member at a time and checks that *none* of them accepts — which is exactly the
certificate `Complexity.NL_complement_certificate` asks for. This file is the check itself: a
code is accepting when its state field is the halt state and its output window holds a one in
cell one, and the scanner here decides the negation from the tuple's cells.

## Main definitions

- `notAcceptScanner` — the tuple does not spell out an accepting configuration

## Main results

- `notAcceptScanner_decides` — what it decides, on a tuple holding a code
- `notAcceptStep_run` — the stage: the accumulator survives only past non-accepting members
-/

@[expose] public section

namespace Complexity

variable {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ}

/-- **The non-acceptance check.** The state field differs from the halt state, or the output
window's cell one does not hold a one — read off the marker-symbol chunk layout of the window
encoding. -/
noncomputable def notAcceptScanner (tm : NTM kk) (cP : ℕ → Fin (jj + 1)) :
    Scanner jj :=
  Scanner.or (Scanner.not (Scanner.bitsEq jj (cP 0) ((qCodec tm.Q).enc tm.qhalt)))
    (Scanner.or
      (((Scanner.isNotConst jj (cP (kk + 2)) Γ.one).after
        ((succParamsCodec tm.Q kk).width + 4)).upTo ((succParamsCodec tm.Q kk).width + 5))
      (((Scanner.isNotConst jj (cP (kk + 2)) Γ.zero).after
        ((succParamsCodec tm.Q kk).width + 5)).upTo ((succParamsCodec tm.Q kk).width + 6)))

/-- A symbol is `one` exactly when its two bits are `(true, false)`. -/
theorem gammaBits_eq_one_iff (g : Γ) : (gammaBits g).1 = true ∧ (gammaBits g).2 = false ↔
    g = Γ.one := by
  cases g <;> simp [gammaBits]

/-- **What the non-acceptance check decides**, on a tuple holding a code. -/
theorem notAcceptScanner_decides (x : List Bool) (cP : ℕ → Fin (jj + 1))
    (cols : ℕ → Fin (jj + 1) → Γ) (a : Code tm.Q kk x.length S)
    (hA : ∀ p, p < kk + 3 → HoldsBits cols 0 (cP p) (codeBlockScan tm x S a p)) :
    ((notAcceptScanner tm cP).emit
      ((notAcceptScanner tm cP).run cols (walkScanLen tm x.length S)) = true) ↔
      ¬(a.1 = tm.qhalt ∧ a.2.2.2.2 ⟨1, by omega⟩ = Γ.one) := by
  classical
  set pw := (succParamsCodec tm.Q kk).width with hpw
  have hqw : ((qCodec tm.Q).enc tm.qhalt).length ≤ walkScanLen tm x.length S := by
    rw [(qCodec tm.Q).enc_length]
    rw [walkScanLen]
    omega
  have hlen6 : pw + 6 ≤ walkScanLen tm x.length S := by
    rw [walkScanLen]
    omega
  have hw3 : (tapeCodec (S + 2)).width = (S + 2) * 3 := rfl
  -- the two output-window cells, from the block the register holds
  have hout : ∀ i, (hi2 : i < 2) →
      cols (pw + 4 + i + 1) (cP (kk + 2))
        = Γ.ofBool (((tapeCodec (S + 2)).enc a.2.2.2)[4 + i]'(by
            rw [(tapeCodec (S + 2)).enc_length, hw3]
            omega)) := by
    intro i hi2
    have hi : 4 + i < codeWidthRaw tm x.length S (kk + 2) := by
      rw [codeWidthRaw, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      omega
    have hq : pw + (4 + i) < (codeBlockScan tm x S a (kk + 2)).length := by
      rw [codeBlockScan_length, blockLen, if_neg (by omega)]
      omega
    have := hA (kk + 2) (by omega) (pw + (4 + i)) hq
    rw [Nat.zero_add] at this
    rw [show pw + 4 + i + 1 = pw + (4 + i) + 1 by omega, this,
      codeBlockScan_getElem_field x a (kk + 2) (by omega) (4 + i) hi hq]
    congr 1
    have hb : codeBlock tm x S a (kk + 2) = (tapeCodec (S + 2)).enc a.2.2.2 :=
      codeBlock_ot tm x S a
    exact List.getElem_of_eq hb _
  have hsym : ∀ i, (hi : i < 2) →
      ((tapeCodec (S + 2)).enc a.2.2.2)[4 + i]'(by
          rw [(tapeCodec (S + 2)).enc_length, hw3]; omega)
        = ([(gammaBits (a.2.2.2.2 ⟨1, by omega⟩)).1,
            (gammaBits (a.2.2.2.2 ⟨1, by omega⟩)).2])[i]'(by simpa using hi) := by
    intro i hi
    have hb1 : (⟨1, by omega⟩ : Fin (S + 2)).val * 3 + (1 + i)
        < ((tapeCodec (S + 2)).enc a.2.2.2).length := by
      rw [(tapeCodec (S + 2)).enc_length, hw3]
      simp
      omega
    have h := enc_getElem (m := S + 2) a.2.2.2.1 a.2.2.2.2 ⟨1, by omega⟩ (1 + i) (by omega)
      hb1
    calc ((tapeCodec (S + 2)).enc a.2.2.2)[4 + i]'(by
          rw [(tapeCodec (S + 2)).enc_length, hw3]; omega)
        = ((tapeCodec (S + 2)).enc a.2.2.2)[(⟨1, by omega⟩ : Fin (S + 2)).val * 3
            + (1 + i)]'hb1 := by
          congr 1
          simp
          omega
      _ = ([decide ((⟨1, by omega⟩ : Fin (S + 2)) = a.2.2.2.1),
            (gammaBits (a.2.2.2.2 ⟨1, by omega⟩)).1,
            (gammaBits (a.2.2.2.2 ⟨1, by omega⟩)).2])[1 + i]'(by simp; omega) := h
      _ = ([(gammaBits (a.2.2.2.2 ⟨1, by omega⟩)).1,
            (gammaBits (a.2.2.2.2 ⟨1, by omega⟩)).2])[i]'(by simpa using hi) := by
          rcases i with _ | _ | i
          · rfl
          · rfl
          · omega
  have hcell1 : ∀ (g : Γ) (colsx : ℕ → Fin (jj + 1) → Γ),
      ((Scanner.isNotConst jj (cP (kk + 2)) g).emit
        ((Scanner.isNotConst jj (cP (kk + 2)) g).run colsx 1) = true) ↔
        colsx 1 (cP (kk + 2)) ≠ g := by
    intro g colsx
    show (Scanner.isNotConst jj (cP (kk + 2)) g).run colsx 1 = true ↔ _
    rw [Scanner.run, Scanner.isNotConst_runL, Scanner.isNotConst_runR]
    exact ⟨fun ⟨q, h1, h2, h3⟩ => by rwa [show q = 1 by omega] at h3,
      fun h => ⟨1, le_rfl, le_rfl, h⟩⟩
  rw [notAcceptScanner, Scanner.or_emit_run, Scanner.or_emit_run, Scanner.not_run,
    Bool.not_eq_true', Bool.eq_false_iff,
    Scanner.range_emit_run _ (Scanner.rightOnly_isNotConst jj _ Γ.one)
      (pw + 4) (pw + 5) _ (by omega),
    Scanner.range_emit_run _ (Scanner.rightOnly_isNotConst jj _ Γ.zero)
      (pw + 5) (pw + 6) _ (by omega),
    show pw + 5 - (pw + 4) = 1 by omega, show pw + 6 - (pw + 5) = 1 by omega,
    hcell1 Γ.one (fun q => cols (pw + 4 + q)), hcell1 Γ.zero (fun q => cols (pw + 5 + q))]
  rw [show ((Scanner.bitsEq jj (cP 0) ((qCodec tm.Q).enc tm.qhalt)).emit
      ((Scanner.bitsEq jj (cP 0) ((qCodec tm.Q).enc tm.qhalt)).run cols
        (walkScanLen tm x.length S)) ≠ true)
      ↔ ¬ HoldsBits cols 0 (cP 0) ((qCodec tm.Q).enc tm.qhalt) from
    not_iff_not.mpr (Scanner.bitsEq_run jj (cP 0) _ cols _ hqw)]
  have hc1 : cols (pw + 4 + 1) (cP (kk + 2))
      = Γ.ofBool (gammaBits (a.2.2.2.2 ⟨1, by omega⟩)).1 := by
    rw [show pw + 4 + 1 = pw + 4 + 0 + 1 by omega, hout 0 (by omega), hsym 0 (by omega)]
    rfl
  have hc2 : cols (pw + 5 + 1) (cP (kk + 2))
      = Γ.ofBool (gammaBits (a.2.2.2.2 ⟨1, by omega⟩)).2 := by
    rw [show pw + 5 + 1 = pw + 4 + 1 + 1 by omega, hout 1 (by omega), hsym 1 (by omega)]
    rfl
  show ¬ HoldsBits cols 0 (cP 0) ((qCodec tm.Q).enc tm.qhalt) ∨
      cols (pw + 4 + 1) (cP (kk + 2)) ≠ Γ.one ∨ cols (pw + 5 + 1) (cP (kk + 2)) ≠ Γ.zero ↔ _
  rw [hc1, hc2]
  -- the state field: the register holds `enc a.1`, so equality with `enc qhalt` is state
  -- equality
  have hstate : HoldsBits cols 0 (cP 0) ((qCodec tm.Q).enc tm.qhalt) ↔ a.1 = tm.qhalt := by
    have h0 := hA 0 (by omega)
    rw [show codeBlockScan tm x S a 0 = (qCodec tm.Q).enc a.1 from by
      rw [codeBlockScan, if_pos rfl, codeBlock_st]] at h0
    constructor
    · intro h
      by_contra hne
      have hlq : ((qCodec tm.Q).enc a.1).length = ((qCodec tm.Q).enc tm.qhalt).length := by
        rw [(qCodec tm.Q).enc_length, (qCodec tm.Q).enc_length]
      have hneq : (qCodec tm.Q).enc a.1 ≠ (qCodec tm.Q).enc tm.qhalt :=
        fun hh => hne ((qCodec tm.Q).enc_injective hh)
      have : (qCodec tm.Q).enc a.1 = (qCodec tm.Q).enc tm.qhalt := by
        refine List.ext_getElem hlq ?_
        intro i h1 h2
        have hcell1 := h0 i h1
        have hcell2 := h i h2
        rw [hcell1] at hcell2
        exact ofBool_injective hcell2
      exact hneq this
    · intro h
      rw [← h] at *
      exact h0
  rw [hstate]
  constructor
  · rintro (hne | h1 | h2) ⟨hq, hone'⟩
    · exact hne hq
    · obtain ⟨hb1, -⟩ := (gammaBits_eq_one_iff _).mpr hone'
      rw [hb1] at h1
      exact h1 rfl
    · obtain ⟨-, hb2⟩ := (gammaBits_eq_one_iff _).mpr hone'
      rw [hb2] at h2
      exact h2 rfl
  · intro h
    by_cases hq : a.1 = tm.qhalt
    · by_cases ho : a.2.2.2.2 ⟨1, by omega⟩ = Γ.one
      · exact absurd ⟨hq, ho⟩ h
      · by_cases hb1 : (gammaBits (a.2.2.2.2 ⟨1, by omega⟩)).1 = true
        · have hb2 : (gammaBits (a.2.2.2.2 ⟨1, by omega⟩)).2 = true := by
            by_contra hb2
            rw [Bool.not_eq_true] at hb2
            exact ho ((gammaBits_eq_one_iff _).mp ⟨hb1, hb2⟩)
          refine Or.inr (Or.inr ?_)
          rw [hb2]
          simp [Γ.ofBool]
        · rw [Bool.not_eq_true] at hb1
          refine Or.inr (Or.inl ?_)
          rw [hb1]
          simp [Γ.ofBool]
    · exact Or.inl hq

/-- **The non-acceptance stage.** The member the loop just remembered — sitting in the first
spare tuple — is not an accepting configuration, or the accumulator dies. -/
theorem notAcceptStep_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (hsp : 1 < L.toWalkLayout.spares) (g : ℕ → Bool) (s : ℕ)
    (cc : Fin r) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) (inp₀ out₀ : Tape)
    (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (htapes : WalkTapes (r := r) x L g s cc Wa Wt inp₀ W₀ out₀)
    (v : Code tm.Q kk x.length S)
    (hpre : (W₀ (auxIdx jj cc)).read = Γ.one →
      ∀ p, p < kk + 3 → HoldsBits (fun q i => (W₀ (walkReg i)).cells q) 0
        (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S v p)) :
    ∃ (c' : Cfg (jj + 2 + r + 1)
        (famStepTM L (TM.twoPassTM (notAcceptScanner tm (L.toWalkLayout.spareReg 1)))
          1 cc).Q) (t : ℕ),
      t ≤ famTime x L r B ∧
      (famStepTM L (TM.twoPassTM (notAcceptScanner tm (L.toWalkLayout.spareReg 1)))
          1 cc).reachesIn t
        ⟨(famStepTM L (TM.twoPassTM (notAcceptScanner tm (L.toWalkLayout.spareReg 1)))
          1 cc).qstart, inp₀, W₀, out₀⟩ c' ∧
      (famStepTM L (TM.twoPassTM (notAcceptScanner tm (L.toWalkLayout.spareReg 1)))
          1 cc).halted c' ∧
      WalkTapes (r := r) x L g (s + 1) cc Wa Wt c'.input c'.work c'.output ∧
      c'.input = TM.parkTape inp₀ ∧
      ((c'.work (auxIdx jj cc)).read = Γ.one →
        (W₀ (auxIdx jj cc)).read = Γ.one ∧
        ¬(v.1 = tm.qhalt ∧ v.2.2.2.2 ⟨1, by omega⟩ = Γ.one) ∧
        ∀ p, p < kk + 3 → HoldsBits (fun q i => (c'.work (walkReg i)).cells q) 0
          (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S v p)) := by
  classical
  have hsp3 : (3 : ℕ) < 2 + L.toWalkLayout.spares := by omega
  obtain ⟨c', t, htle, hreach, hhalt, htapes', hinp', hreg, hacc, -⟩ :=
    famStep_run x L (notAcceptScanner tm (L.toWalkLayout.spareReg 1)) 1 (by omega) g s cc B
      hB1 hB Wa Wt inp₀ out₀ W₀ htapes
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
  have hv := hpre hold
  have hv' := holdsBlocks_survives x L 1 3 (by omega) hsp3 (by omega)
    (L.toWalkLayout.spareReg 1) (fun p hp => (L.toWalkLayout.famReg_spare 1 p hsp hp).symm) W₀
    htapes.2.1 htapes.2.2.1 v hv
  refine ⟨hold, ?_, fun p hp q hq => ?_⟩
  · exact (notAcceptScanner_decides x (L.toWalkLayout.spareReg 1)
      (TM.scanCol (stepCellsF L 1 W₀)) v (fun p hp => hv' p hp)).mp hverd
  · show (c'.work (walkReg (L.toWalkLayout.spareReg 1 p))).cells (0 + q + 1) = _
    rw [hcells]
    exact hv' p hp q hq

/-! ## The scan over the members of the last round -/

/-- How many stages one iteration of the final scan consumes. -/
def scanBodyStages (N : ℕ) : ℕ := memberBodyStages N + 1

/-- **One scanned member**: produce a member, remember it, and check it does not accept. -/
noncomputable def scanBodyTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (cc wcnt wlim : Fin rr) :
    TM (jj + 2 + rr + 1) :=
  TM.seqTM (memberBodyTM x L dc cc wcnt wlim)
    (famStepTM L (TM.twoPassTM (notAcceptScanner tm (L.toWalkLayout.spareReg 1))) 1 cc)

/-- Its advancing states. -/
noncomputable def scanBodyAdv {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (cc wcnt wlim : Fin rr) :
    (scanBodyTM x L dc cc wcnt wlim).Q → Bool :=
  TM.seqAdv (memberBodyAdv x L dc cc wcnt wlim)
    (famStepAdv L (TM.twoPassTM (notAcceptScanner tm (L.toWalkLayout.spareReg 1))) 1 cc)

/-- **It respects the guess protocol.** -/
theorem guessProtocol_scanBodyTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (cc wcnt wlim : Fin rr) :
    TM.GuessProtocol (scanBodyTM x L dc cc wcnt wlim) (scanBodyAdv x L dc cc wcnt wlim) :=
  TM.guessProtocol_seqTM (guessProtocol_memberBodyTM x L dc cc wcnt wlim)
    (guessProtocol_famStepTM L _ 1 cc)

/-- **What one scanned member establishes**: it is in the round, above the last, remembered —
and it does not accept. -/
theorem scanBody_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
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
    ∃ (c : Cfg (jj + 2 + r + 1) (scanBodyTM x L dc cc wcnt wlim).Q) (t : ℕ),
      (scanBodyTM x L dc cc wcnt wlim).reachesIn t
        ⟨(scanBodyTM x L dc cc wcnt wlim).qstart, inp₀, W₀, out₀⟩ c ∧
      (scanBodyTM x L dc cc wcnt wlim).halted c ∧
      WalkTapes (r := r) x L g (s + scanBodyStages N) cc (fun c' => c.work (auxIdx jj c'))
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
          codeLt tm x S prev v ∧
          ¬(v.1 = tm.qhalt ∧ v.2.2.2.2 ⟨1, by omega⟩ = Γ.one) ∧
          ∀ p, p < kk + 3 → HoldsBits (fun q i => (c.work (walkReg i)).cells q) 0
            (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S v p)) := by
  classical
  obtain ⟨cM, tM, hreachM, hhaltM, htapesM, hkeptM, hwcntM, haccM⟩ :=
    memberBody_run x L dc hsp g s cc wcnt wlim hcnt hlim hcl B hB1 hB hspace hwin hwc N Wa Wt
      inp₀ out₀ W₀ htapes bits hbits hlimN prev hpre
  obtain ⟨hfixI, hfixW, hfixO⟩ :=
    walkTapes_transition_eq x L g (s + memberBodyStages N) cc
      (fun c' => cM.work (auxIdx jj c'))
      (fun p q => (cM.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      cM.input cM.work cM.output htapesM
  set v₀ : Code tm.Q kk x.length S :=
    if h : (cM.work (auxIdx jj cc)).read = Γ.one then (haccM h).2.choose
    else cfgCode x.length S (tm.initCfg x) with hv₀def
  have hv₀spec : ∀ h : (cM.work (auxIdx jj cc)).read = Γ.one,
      v₀ ∈ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N) ∧
      codeLt tm x S prev v₀ ∧
      ∀ p, p < kk + 3 → HoldsBits (fun q i => (cM.work (walkReg i)).cells q) 0
        (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S v₀ p) := by
    intro h
    rw [hv₀def, dif_pos h]
    exact (haccM h).2.choose_spec
  obtain ⟨cA, tA, -, hreachA, hhaltA, htapesA, hinpA, haccA⟩ :=
    notAcceptStep_run x L hsp g (s + memberBodyStages N) cc B hB1 hB
      (fun c' => cM.work (auxIdx jj c'))
      (fun p q => (cM.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      cM.input cM.output cM.work htapesM v₀ (fun h => (hv₀spec h).2.2)
  obtain ⟨c, hreach, hhalt, hin, hwork, hout⟩ :=
    seqTM_run_of_runs _ _ inp₀ out₀ W₀ hreachM hhaltM
      (by rw [hfixI, hfixW, hfixO]; exact hreachA) hhaltA
  refine ⟨c, tM + 1 + tA, hreach, hhalt, ?_, ?_, ?_, fun hone => ?_⟩
  · rw [hin, hwork, hout]
    have hg := htapesA
    rw [show s + memberBodyStages N + 1 = s + scanBodyStages N by rw [scanBodyStages]; ring]
      at hg
    exact ⟨fun c' _ => rfl, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2.1,
      hg.2.2.2.2.2.2.1, hg.2.2.2.2.2.2.2.1, hg.2.2.2.2.2.2.2.2.1, hg.2.2.2.2.2.2.2.2.2.1,
      fun p hp q => rfl⟩
  · intro c' hc' hcn
    rw [hwork, show cA.work (auxIdx jj c') = cM.work (auxIdx jj c') from htapesA.1 c' hc']
    exact hkeptM c' hc' hcn
  · rw [hwork, show cA.work (auxIdx jj wcnt) = cM.work (auxIdx jj wcnt) from
      htapesA.1 wcnt hcnt]
    exact hwcntM
  · rw [hwork] at hone ⊢
    obtain ⟨holdM, hnacc, hvS⟩ := haccA hone
    obtain ⟨hvmem, hlt, -⟩ := hv₀spec holdM
    exact ⟨(haccM holdM).1, v₀, hvmem, hlt, hnacc, hvS⟩

/-- **What the final scan carries**: an increasing list of round members, none of them
accepting. -/
def ScanInv (x : List Bool) (L : WalkWidths kk jj tm x.length S wc) (g : ℕ → Bool) (s₀ : ℕ)
    (cc wcnt icnt : Fin r) (Wa : Fin r → Tape) (a₀ : Γ) (N : ℕ) (j : ℕ) :
    TM.TapePred (jj + 2 + r + 1) :=
  fun inp work out =>
    WalkTapes (r := r) x L g (s₀ + j * scanBodyStages N) cc (fun c => work (auxIdx jj c))
      (fun p q => (work (walkReg (L.toWalkLayout.codeT p))).cells q) inp work out ∧
    (∀ c, c ≠ cc → c ≠ wcnt → c ≠ icnt → work (auxIdx jj c) = Wa c) ∧
    (∃ bits, (work (auxIdx jj wcnt)).HasBinaryContent bits) ∧
    ((work (auxIdx jj cc)).read = Γ.one →
      a₀ = Γ.one ∧
      ∃ (l : List (Code tm.Q kk x.length S)) (prev : Code tm.Q kk x.length S),
        j ≤ l.length ∧ l.Pairwise (codeLt tm x S) ∧
        (∀ v ∈ l, v ∈ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N)) ∧
        (∀ v ∈ l, ¬(v.1 = tm.qhalt ∧ v.2.2.2.2 ⟨1, by omega⟩ = Γ.one)) ∧
        (∀ w ∈ l, codeLt tm x S w prev ∨ w = prev) ∧
        ∀ p, p < kk + 3 → HoldsBits (fun q i => (work (walkReg i)).cells q) 0
          (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S prev p))

/-- **The scan loop.** -/
noncomputable def scanLoopTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (cc wcnt wlim icnt ilim : Fin rr) :
    TM (jj + 2 + rr + 1) :=
  TM.binaryForTM (scanBodyTM x L dc cc wcnt wlim) (auxIdx jj icnt) (auxIdx jj ilim)

/-- **One iteration carries the invariant.** -/
theorem scanLoop_body (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (hsp : 1 < L.toWalkLayout.spares) (g : ℕ → Bool) (s₀ : ℕ)
    (cc wcnt wlim icnt ilim : Fin r) (hcnt : wcnt ≠ cc) (hlim : wlim ≠ cc) (hcl : wcnt ≠ wlim)
    (hic : icnt ≠ cc) (hiw : icnt ≠ wcnt) (hil : wlim ≠ icnt) (hlc : ilim ≠ cc)
    (hlw : ilim ≠ wcnt) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hspace : ∀ c, tm.ReachesCfg (tm.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hwin : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x S c)
    (hwc : wc ≤ walkScanLen tm x.length S) (Wa : Fin r → Tape) (a₀ : Γ) (N : ℕ)
    (hWaN : (Wa wlim).HasBinaryNat N) (cmax value : ℕ) :
    (scanBodyTM x L dc cc wcnt wlim).Hoare
      (TM.BinaryForFrame (auxIdx jj icnt) (auxIdx jj ilim) cmax
        (ScanInv x L g s₀ cc wcnt icnt Wa a₀ N) value)
      (TM.BinaryForBodyPost (auxIdx jj icnt) (auxIdx jj ilim) cmax
        (ScanInv x L g s₀ cc wcnt icnt Wa a₀ N) value) := by
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
        v ∈ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N)) ∧
      (∀ v ∈ ((hsem h).2).choose,
        ¬(v.1 = tm.qhalt ∧ v.2.2.2.2 ⟨1, by omega⟩ = Γ.one)) ∧
      (∀ w ∈ ((hsem h).2).choose, codeLt tm x S w prev₀ ∨ w = prev₀) ∧
      ∀ p, p < kk + 3 → HoldsBits (fun q i => (work (walkReg i)).cells q) 0
        (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S prev₀ p) := by
    intro h
    rw [hprev₀def, dif_pos h]
    exact ((hsem h).2).choose_spec.choose_spec
  obtain ⟨c', t, hreach, hhalt, htapes', hkept', hwcnt', hacc'⟩ :=
    scanBody_run x L dc hsp g (s₀ + value * scanBodyStages N) cc wcnt wlim hcnt hlim hcl
      B hB1 hB hspace hwin hwc N (fun c => work (auxIdx jj c))
      (fun p q => (work (walkReg (L.toWalkLayout.codeT p))).cells q) inp out work htapes bits
      hbits
      (by
        show (work (auxIdx jj wlim)).HasBinaryNat N
        rw [haux wlim hlim (fun h => hcl h.symm) hil]
        exact hWaN) prev₀ (fun h => (hprev₀spec h).2.2.2.2.2)
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
  have hstage : s₀ + value * scanBodyStages N + scanBodyStages N
      = s₀ + (value + 1) * scanBodyStages N := by
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
    obtain ⟨holdacc, v, hvmem, hvlt, hvnacc, hvS⟩ := hacc' hone
    obtain ⟨hlen, hpw, hmem, hnacc, hbelow, -⟩ := hprev₀spec holdacc
    refine ⟨(hsem holdacc).1, ((hsem holdacc).2).choose ++ [v], v, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      · exact hnacc w h
      · rw [List.mem_singleton.mp h]
        exact hvnacc
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

/-- **The scan loop carries its invariant to the end.** -/
theorem scanLoop_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (hsp : 1 < L.toWalkLayout.spares) (g : ℕ → Bool) (s₀ : ℕ)
    (cc wcnt wlim icnt ilim : Fin r) (hcnt : wcnt ≠ cc) (hlim : wlim ≠ cc) (hcl : wcnt ≠ wlim)
    (hic : icnt ≠ cc) (hiw : icnt ≠ wcnt) (hil : wlim ≠ icnt) (hlc : ilim ≠ cc)
    (hlw : ilim ≠ wcnt) (hli : icnt ≠ ilim) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hspace : ∀ c, tm.ReachesCfg (tm.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hwin : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x S c)
    (hwc : wc ≤ walkScanLen tm x.length S) (Wa : Fin r → Tape) (a₀ : Γ) (N : ℕ)
    (hWaN : (Wa wlim).HasBinaryNat N) (cmax : ℕ) :
    (scanLoopTM x L dc cc wcnt wlim icnt ilim).Hoare
      (TM.BinaryForFrame (auxIdx jj icnt) (auxIdx jj ilim) cmax
        (ScanInv x L g s₀ cc wcnt icnt Wa a₀ N) 0)
      (TM.BinaryForFrame (auxIdx jj icnt) (auxIdx jj ilim) cmax
        (ScanInv x L g s₀ cc wcnt icnt Wa a₀ N) cmax) :=
  TM.binaryForTM_hoare (auxIdx_injective hli) cmax _ (fun value _ =>
    scanLoop_body x L dc hsp g s₀ cc wcnt wlim icnt ilim hcnt hlim hcl hic hiw hil hlc hlw
      B hB1 hB hspace hwin hwc Wa a₀ N hWaN cmax value)

/-- **What the final scan proves.** With the round's certified size on the limit tape, the
members met are the whole round, and none of them accepts — the body of the complement
certificate. -/
theorem certificate_of_scanLoop (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (g : ℕ → Bool) (s₀ : ℕ) (cc wcnt icnt : Fin r) (Wa : Fin r → Tape) (a₀ : Γ) (N cmax : ℕ)
    (hcard : (NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N)).card ≤ cmax)
    (inp : Tape) (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (hInv : ScanInv x L g s₀ cc wcnt icnt Wa a₀ N cmax inp work out)
    (hone : (work (auxIdx jj cc)).read = Γ.one) :
    ∃ l : List (Code tm.Q kk x.length S),
      NTM.RoundList tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N) l ∧
      ∀ a ∈ l, ¬((decodeCfg x S a).state = tm.qhalt ∧
        (decodeCfg x S a).output.cells 1 = Γ.one) := by
  obtain ⟨l, prev, hlen, hpw, hmem, hnacc, -, -⟩ := (hInv.2.2.2 hone).2
  refine ⟨l, roundList_of_pairwise hpw hmem (by omega), fun a ha => ?_⟩
  have h := hnacc a ha
  intro ⟨hq, ho⟩
  refine h ⟨hq, ?_⟩
  have : (decodeCfg x S a).output.cells 1 = a.2.2.2.2 ⟨1, by omega⟩ := by
    show (if h : 1 < S + 2 then a.2.2.2.2 ⟨1, h⟩ else Γ.blank) = _
    rw [dif_pos (by omega)]
  rw [this] at ho
  exact ho

/-! ## The scan over the members of an odd last round -/

/-- How many stages one iteration of the final scan consumes. -/
def oddScanBodyStages (N : ℕ) : ℕ := oddBodyStages N + 1

/-- **One scanned member**: produce a member, remember it, and check it does not accept. -/
noncomputable def oddScanBodyTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (cc wcnt wlim : Fin rr) :
    TM (jj + 2 + rr + 1) :=
  TM.seqTM (oddBodyTM x L dc cc wcnt wlim)
    (famStepTM L (TM.twoPassTM (notAcceptScanner tm (L.toWalkLayout.spareReg 1))) 1 cc)

/-- Its advancing states. -/
noncomputable def oddScanBodyAdv {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (cc wcnt wlim : Fin rr) :
    (oddScanBodyTM x L dc cc wcnt wlim).Q → Bool :=
  TM.seqAdv (oddBodyAdv x L dc cc wcnt wlim)
    (famStepAdv L (TM.twoPassTM (notAcceptScanner tm (L.toWalkLayout.spareReg 1))) 1 cc)

/-- **It respects the guess protocol.** -/
theorem guessProtocol_oddScanBodyTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (cc wcnt wlim : Fin rr) :
    TM.GuessProtocol (oddScanBodyTM x L dc cc wcnt wlim)
      (oddScanBodyAdv x L dc cc wcnt wlim) :=
  TM.guessProtocol_seqTM (guessProtocol_oddBodyTM x L dc cc wcnt wlim)
    (guessProtocol_famStepTM L _ 1 cc)

/-- **What one scanned member establishes**: it is in the round, above the last, remembered —
and it does not accept. -/
theorem oddScanBody_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
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
    ∃ (c : Cfg (jj + 2 + r + 1) (oddScanBodyTM x L dc cc wcnt wlim).Q) (t : ℕ),
      (oddScanBodyTM x L dc cc wcnt wlim).reachesIn t
        ⟨(oddScanBodyTM x L dc cc wcnt wlim).qstart, inp₀, W₀, out₀⟩ c ∧
      (oddScanBodyTM x L dc cc wcnt wlim).halted c ∧
      WalkTapes (r := r) x L g (s + oddScanBodyStages N) cc (fun c' => c.work (auxIdx jj c'))
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
          ¬(v.1 = tm.qhalt ∧ v.2.2.2.2 ⟨1, by omega⟩ = Γ.one) ∧
          ∀ p, p < kk + 3 → HoldsBits (fun q i => (c.work (walkReg i)).cells q) 0
            (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S v p)) := by
  classical
  obtain ⟨cM, tM, hreachM, hhaltM, htapesM, hkeptM, hwcntM, haccM⟩ :=
    oddBody_run x L dc hsp g s cc wcnt wlim hcnt hlim hcl B hB1 hB hspace hwin hwc N Wa Wt
      inp₀ out₀ W₀ htapes bits hbits hlimN prev hpre
  obtain ⟨hfixI, hfixW, hfixO⟩ :=
    walkTapes_transition_eq x L g (s + oddBodyStages N) cc
      (fun c' => cM.work (auxIdx jj c'))
      (fun p q => (cM.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      cM.input cM.work cM.output htapesM
  set v₀ : Code tm.Q kk x.length S :=
    if h : (cM.work (auxIdx jj cc)).read = Γ.one then (haccM h).2.choose
    else cfgCode x.length S (tm.initCfg x) with hv₀def
  have hv₀spec : ∀ h : (cM.work (auxIdx jj cc)).read = Γ.one,
      v₀ ∈ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 1) ∧
      codeLt tm x S prev v₀ ∧
      ∀ p, p < kk + 3 → HoldsBits (fun q i => (cM.work (walkReg i)).cells q) 0
        (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S v₀ p) := by
    intro h
    rw [hv₀def, dif_pos h]
    exact (haccM h).2.choose_spec
  obtain ⟨cA, tA, -, hreachA, hhaltA, htapesA, hinpA, haccA⟩ :=
    notAcceptStep_run x L hsp g (s + oddBodyStages N) cc B hB1 hB
      (fun c' => cM.work (auxIdx jj c'))
      (fun p q => (cM.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      cM.input cM.output cM.work htapesM v₀ (fun h => (hv₀spec h).2.2)
  obtain ⟨c, hreach, hhalt, hin, hwork, hout⟩ :=
    seqTM_run_of_runs _ _ inp₀ out₀ W₀ hreachM hhaltM
      (by rw [hfixI, hfixW, hfixO]; exact hreachA) hhaltA
  refine ⟨c, tM + 1 + tA, hreach, hhalt, ?_, ?_, ?_, fun hone => ?_⟩
  · rw [hin, hwork, hout]
    have hg := htapesA
    rw [show s + oddBodyStages N + 1 = s + oddScanBodyStages N by rw [oddScanBodyStages]; ring]
      at hg
    exact ⟨fun c' _ => rfl, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2.1,
      hg.2.2.2.2.2.2.1, hg.2.2.2.2.2.2.2.1, hg.2.2.2.2.2.2.2.2.1, hg.2.2.2.2.2.2.2.2.2.1,
      fun p hp q => rfl⟩
  · intro c' hc' hcn
    rw [hwork, show cA.work (auxIdx jj c') = cM.work (auxIdx jj c') from htapesA.1 c' hc']
    exact hkeptM c' hc' hcn
  · rw [hwork, show cA.work (auxIdx jj wcnt) = cM.work (auxIdx jj wcnt) from
      htapesA.1 wcnt hcnt]
    exact hwcntM
  · rw [hwork] at hone ⊢
    obtain ⟨holdM, hnacc, hvS⟩ := haccA hone
    obtain ⟨hvmem, hlt, -⟩ := hv₀spec holdM
    exact ⟨(haccM holdM).1, v₀, hvmem, hlt, hnacc, hvS⟩

/-- **What the final scan carries**: an increasing list of round members, none of them
accepting. -/
def OddScanInv (x : List Bool) (L : WalkWidths kk jj tm x.length S wc) (g : ℕ → Bool) (s₀ : ℕ)
    (cc wcnt icnt : Fin r) (Wa : Fin r → Tape) (a₀ : Γ) (N : ℕ) (j : ℕ) :
    TM.TapePred (jj + 2 + r + 1) :=
  fun inp work out =>
    WalkTapes (r := r) x L g (s₀ + j * oddScanBodyStages N) cc (fun c => work (auxIdx jj c))
      (fun p q => (work (walkReg (L.toWalkLayout.codeT p))).cells q) inp work out ∧
    (∀ c, c ≠ cc → c ≠ wcnt → c ≠ icnt → work (auxIdx jj c) = Wa c) ∧
    (∃ bits, (work (auxIdx jj wcnt)).HasBinaryContent bits) ∧
    ((work (auxIdx jj cc)).read = Γ.one →
      a₀ = Γ.one ∧
      ∃ (l : List (Code tm.Q kk x.length S)) (prev : Code tm.Q kk x.length S),
        j ≤ l.length ∧ l.Pairwise (codeLt tm x S) ∧
        (∀ v ∈ l, v ∈ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 1)) ∧
        (∀ v ∈ l, ¬(v.1 = tm.qhalt ∧ v.2.2.2.2 ⟨1, by omega⟩ = Γ.one)) ∧
        (∀ w ∈ l, codeLt tm x S w prev ∨ w = prev) ∧
        ∀ p, p < kk + 3 → HoldsBits (fun q i => (work (walkReg i)).cells q) 0
          (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S prev p))

/-- **The scan loop.** -/
noncomputable def oddScanLoopTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (cc wcnt wlim icnt ilim : Fin rr) :
    TM (jj + 2 + rr + 1) :=
  TM.binaryForTM (oddScanBodyTM x L dc cc wcnt wlim) (auxIdx jj icnt) (auxIdx jj ilim)

/-- **One iteration carries the invariant.** -/
theorem oddScanLoop_body (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (hsp : 1 < L.toWalkLayout.spares) (g : ℕ → Bool) (s₀ : ℕ)
    (cc wcnt wlim icnt ilim : Fin r) (hcnt : wcnt ≠ cc) (hlim : wlim ≠ cc) (hcl : wcnt ≠ wlim)
    (hic : icnt ≠ cc) (hiw : icnt ≠ wcnt) (hil : wlim ≠ icnt) (hlc : ilim ≠ cc)
    (hlw : ilim ≠ wcnt) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hspace : ∀ c, tm.ReachesCfg (tm.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hwin : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x S c)
    (hwc : wc ≤ walkScanLen tm x.length S) (Wa : Fin r → Tape) (a₀ : Γ) (N : ℕ)
    (hWaN : (Wa wlim).HasBinaryNat N) (cmax value : ℕ) :
    (oddScanBodyTM x L dc cc wcnt wlim).Hoare
      (TM.BinaryForFrame (auxIdx jj icnt) (auxIdx jj ilim) cmax
        (OddScanInv x L g s₀ cc wcnt icnt Wa a₀ N) value)
      (TM.BinaryForBodyPost (auxIdx jj icnt) (auxIdx jj ilim) cmax
        (OddScanInv x L g s₀ cc wcnt icnt Wa a₀ N) value) := by
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
      (∀ v ∈ ((hsem h).2).choose,
        ¬(v.1 = tm.qhalt ∧ v.2.2.2.2 ⟨1, by omega⟩ = Γ.one)) ∧
      (∀ w ∈ ((hsem h).2).choose, codeLt tm x S w prev₀ ∨ w = prev₀) ∧
      ∀ p, p < kk + 3 → HoldsBits (fun q i => (work (walkReg i)).cells q) 0
        (L.toWalkLayout.spareReg 1 p) (codeBlockScan tm x S prev₀ p) := by
    intro h
    rw [hprev₀def, dif_pos h]
    exact ((hsem h).2).choose_spec.choose_spec
  obtain ⟨c', t, hreach, hhalt, htapes', hkept', hwcnt', hacc'⟩ :=
    oddScanBody_run x L dc hsp g (s₀ + value * oddScanBodyStages N) cc wcnt wlim hcnt hlim hcl
      B hB1 hB hspace hwin hwc N (fun c => work (auxIdx jj c))
      (fun p q => (work (walkReg (L.toWalkLayout.codeT p))).cells q) inp out work htapes bits
      hbits
      (by
        show (work (auxIdx jj wlim)).HasBinaryNat N
        rw [haux wlim hlim (fun h => hcl h.symm) hil]
        exact hWaN) prev₀ (fun h => (hprev₀spec h).2.2.2.2.2)
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
  have hstage : s₀ + value * oddScanBodyStages N + oddScanBodyStages N
      = s₀ + (value + 1) * oddScanBodyStages N := by
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
    obtain ⟨holdacc, v, hvmem, hvlt, hvnacc, hvS⟩ := hacc' hone
    obtain ⟨hlen, hpw, hmem, hnacc, hbelow, -⟩ := hprev₀spec holdacc
    refine ⟨(hsem holdacc).1, ((hsem holdacc).2).choose ++ [v], v, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      · exact hnacc w h
      · rw [List.mem_singleton.mp h]
        exact hvnacc
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

/-- **The scan loop carries its invariant to the end.** -/
theorem oddScanLoop_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (hsp : 1 < L.toWalkLayout.spares) (g : ℕ → Bool) (s₀ : ℕ)
    (cc wcnt wlim icnt ilim : Fin r) (hcnt : wcnt ≠ cc) (hlim : wlim ≠ cc) (hcl : wcnt ≠ wlim)
    (hic : icnt ≠ cc) (hiw : icnt ≠ wcnt) (hil : wlim ≠ icnt) (hlc : ilim ≠ cc)
    (hlw : ilim ≠ wcnt) (hli : icnt ≠ ilim) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hspace : ∀ c, tm.ReachesCfg (tm.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hwin : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x S c)
    (hwc : wc ≤ walkScanLen tm x.length S) (Wa : Fin r → Tape) (a₀ : Γ) (N : ℕ)
    (hWaN : (Wa wlim).HasBinaryNat N) (cmax : ℕ) :
    (oddScanLoopTM x L dc cc wcnt wlim icnt ilim).Hoare
      (TM.BinaryForFrame (auxIdx jj icnt) (auxIdx jj ilim) cmax
        (OddScanInv x L g s₀ cc wcnt icnt Wa a₀ N) 0)
      (TM.BinaryForFrame (auxIdx jj icnt) (auxIdx jj ilim) cmax
        (OddScanInv x L g s₀ cc wcnt icnt Wa a₀ N) cmax) :=
  TM.binaryForTM_hoare (auxIdx_injective hli) cmax _ (fun value _ =>
    oddScanLoop_body x L dc hsp g s₀ cc wcnt wlim icnt ilim hcnt hlim hcl hic hiw hil hlc hlw
      B hB1 hB hspace hwin hwc Wa a₀ N hWaN cmax value)

/-- **What the final scan proves.** With the round's certified size on the limit tape, the
members met are the whole round, and none of them accepts — the body of the complement
certificate. -/
theorem certificate_of_oddScanLoop (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (g : ℕ → Bool) (s₀ : ℕ) (cc wcnt icnt : Fin r) (Wa : Fin r → Tape) (a₀ : Γ) (N cmax : ℕ)
    (hcard : (NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 1)).card ≤ cmax)
    (inp : Tape) (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (hInv : OddScanInv x L g s₀ cc wcnt icnt Wa a₀ N cmax inp work out)
    (hone : (work (auxIdx jj cc)).read = Γ.one) :
    ∃ l : List (Code tm.Q kk x.length S),
      NTM.RoundList tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 1) l ∧
      ∀ a ∈ l, ¬((decodeCfg x S a).state = tm.qhalt ∧
        (decodeCfg x S a).output.cells 1 = Γ.one) := by
  obtain ⟨l, prev, hlen, hpw, hmem, hnacc, -, -⟩ := (hInv.2.2.2 hone).2
  refine ⟨l, roundList_of_pairwise hpw hmem (by omega), fun a ha => ?_⟩
  have h := hnacc a ha
  intro ⟨hq, ho⟩
  refine h ⟨hq, ?_⟩
  have : (decodeCfg x S a).output.cells 1 = a.2.2.2.2 ⟨1, by omega⟩ := by
    show (if h : 1 < S + 2 then a.2.2.2.2 ⟨1, h⟩ else Γ.blank) = _
    rw [dif_pos (by omega)]
  rw [this] at ho
  exact ho

end Complexity
