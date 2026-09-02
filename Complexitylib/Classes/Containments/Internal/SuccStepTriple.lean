/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.SuccStepLayout
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Window

/-!
# One stage of a walk carries the walk's invariant

⚠️ Unreviewed by Bolton

`Complexity.walkStepTM_hoareTime` says what one stage of a walk does to the tapes;
`Complexity.WalkStepInv` says what has to be true between stages. This file joins them: a stage
of a walk that really happens carries the invariant from `s` to `s + 1`, leaving the accumulator
bit alone because the scan accepts.

## Main definitions

- `AccHolds` — the accumulator tape carries a given bit, and the other auxiliary tapes are held
- `StepData` — what one stage of a real walk supplies
- `pairCert` — the guess stream a whole walk reads, alternating with the stage's parity
- `stepTime`, `WalkP`, `gammaOfBits`

## Main results

- `parkTape_read_of_walkStepInv`, `moved_of_walkStepInv`
-/

@[expose] public section

namespace Complexity

variable {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ}

/-- **The accumulator carries a bit.** The walk's verdict lives on an auxiliary tape, because
`Complexity.walkStepTM` has no way to stop early: every stage runs, and a stage that rejects
clears the bit. -/
def AccHolds (jj : ℕ) {r : ℕ} (c : Fin r) (v : Bool) (Wa : Fin r → Tape) :
    TM.TapePred (jj + 2 + r + 1) :=
  fun _ work _ => (work (auxIdx jj c)).read = Γ.ofBool v ∧
    ∀ c', c' ≠ c → work (auxIdx jj c') = Wa c'

/-! ## What the invariant says about the input tape -/

/-- **The machine's own input head is parked where the code says.** -/
theorem parkTape_of_walkStepInv (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (cOld : ℕ → Fin (jj + 1)) (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool) (s : ℕ)
    (inp : Tape) (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (h : WalkStepInv (r := r) x L cOld f g s inp work out) :
    TM.parkTape inp = ⟨max (f s).2.1.val 1, (Tape.init (x.map Γ.ofBool)).cells⟩ := by
  rw [h.2.2.2.2.2.1]
  refine Tape.ext ?_ rfl
  show max (max (f s).2.1.val 1) 1 = max (f s).2.1.val 1
  omega

/-- **The symbol the input check compares against.** Off the marker it is the symbol the code's
head field names; on the marker there is nothing to compare, and the check is waived. -/
theorem parkTape_read_of_walkStepInv (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (cOld : ℕ → Fin (jj + 1)) (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool) (s : ℕ)
    (inp : Tape) (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (h : WalkStepInv (r := r) x L cOld f g s inp work out) (hne : (f s).2.1.val ≠ 0) :
    (TM.parkTape inp).read = inSymOf tm x S (f s) := by
  rw [parkTape_of_walkStepInv x L cOld f g s inp work out h]
  show (Tape.init (x.map Γ.ofBool)).cells (max (f s).2.1.val 1) = _
  rw [show max (f s).2.1.val 1 = (f s).2.1.val by omega]
  rfl

/-- **The input tape carries its left marker and nothing else.** -/
theorem inp_startInvariant_of_walkStepInv (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc)
    (cOld : ℕ → Fin (jj + 1)) (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool) (s : ℕ)
    (inp : Tape) (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (h : WalkStepInv (r := r) x L cOld f g s inp work out) : inp.StartInvariant := by
  rw [h.2.2.2.2.2.1]
  refine ⟨?_, fun j hj => ?_⟩
  · show (Tape.init (x.map Γ.ofBool)).cells 0 = Γ.start
    exact Tape.init_cells_zero _
  · show (Tape.init (x.map Γ.ofBool)).cells j ≠ Γ.start
    exact Tape.init_ofBool_cells_ne_start x j hj

/-- **And its head is off that marker**, which is what lets the stage read it. -/
theorem inp_read_ne_start_of_walkStepInv (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc)
    (cOld : ℕ → Fin (jj + 1)) (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool) (s : ℕ)
    (inp : Tape) (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (h : WalkStepInv (r := r) x L cOld f g s inp work out) : inp.read ≠ Γ.start := by
  rw [h.2.2.2.2.2.1]
  show (Tape.init (x.map Γ.ofBool)).cells (max (f s).2.1.val 1) ≠ Γ.start
  exact Tape.init_ofBool_cells_ne_start x _ (le_max_right _ _)

/-! ## What one stage of a real walk supplies -/

/-- **One stage of a real walk.** Either the walk stays where it is, or it takes the transition
the certificate names — and then the move stays inside the window the codes live in. -/
def StepData {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ) (Ps : ℕ → SuccParams tm.Q kk)
    (ds : ℕ → Dir3) (f : ℕ → Code tm.Q kk x.length S) (s : ℕ) : Prop :=
  (f (s + 1) = f s ∧ ds s = Dir3.stay) ∨
    (∃ β : Bool, Ps s = paramsOf tm x S (f s) β ∧ f (s + 1) = succCode tm x S β (f s) ∧
      ds s = adjustedDir (succTrans tm (Ps s)).2.2.2.1 (f s).2.1.val ∧
      movedIdx (succTrans tm (Ps s)).2.2.2.1 (f s).2.1.val ≤ x.length + S + 1 ∧
      (∀ i, movedIdx (succDir tm (Ps s) i) ((f s).2.2.1 i).1.val ≤ S) ∧
      movedIdx (succTrans tm (Ps s)).2.2.2.2.2 (f s).2.2.2.1.val ≤ S + 1 ∧
      ((succTrans tm (Ps s)).2.2.2.1 = Dir3.left → 0 < (f s).2.1.val) ∧ (f s).1 ≠ tm.qhalt)

/-- **A stage of a real walk is a step of the walk.** -/
theorem stepData_walk {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (f : ℕ → Code tm.Q kk x.length S) (s : ℕ)
    (h : StepData tm x S Ps ds f s) :
    f (s + 1) = f s ∨ f (s + 1) ∈ NTM.codeSucc tm x S (f s) := by
  rcases h with ⟨hstay, -⟩ | ⟨β, -, hsucc, -, -, -, -, -, hne⟩
  · exact Or.inl hstay
  · exact Or.inr ((mem_codeSucc_iff tm x S (f s) (f (s + 1))).mpr ⟨hne, β, hsucc⟩)

/-- **And a walk of real stages reaches its last code.** This is the mathematics the walk loop's
contract is for: `Complexity.walkLoop_carries` says the machine accepts, and this says what its
acceptance means. -/
theorem mem_reachCodes_of_stepData {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (f : ℕ → Code tm.Q kk x.length S) (N : ℕ)
    (hstep : ∀ s, s < 2 * N → StepData tm x S Ps ds f s) :
    f (2 * N) ∈ NTM.reachCodes tm x S (f 0) (2 * N) :=
  mem_reachCodes_of_walk tm x S (f 0) (2 * N) f rfl
    (fun j hj => stepData_walk tm x S Ps ds f j (hstep j hj))

/-- **A stage carries the input head to where the next code says.** Both branches land the head
parked at the new code's head field, which is the input clause of the walk's invariant one stage
on. -/
theorem moved_of_stepData {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (f : ℕ → Code tm.Q kk x.length S) (s : ℕ)
    (hstep : StepData tm x S Ps ds f s) (dc : DirCodec) (m gc : Γ)
    (hm : m = dc.encMove (ds s)) (hg : gc = dc.enc (ds s)) (t : Tape)
    (ht : t.head = max (f s).2.1.val 1) :
    t.move (dc.dec m gc) = ⟨max (f (s + 1)).2.1.val 1, t.cells⟩ := by
  rcases hstep with ⟨hstay, hd⟩ | ⟨β, hPs, hsucc, hds, hclampIn, hclampW, hclampO, -, -⟩
  · rw [hstay]
    exact move_of_walkStay dc t (f s).2.1.val m gc ht (by rw [hm, hd]) (by rw [hg, hd])
  · obtain ⟨-, -, -, -, hhead, -, -⟩ :=
      succ_fields_of_eq tm x S (f s) (f (s + 1)) β hsucc (by rw [← hPs] at *; exact hclampIn)
        (by rw [← hPs] at *; exact hclampW) (by rw [← hPs] at *; exact hclampO)
    rw [← hPs] at hhead
    exact move_of_walkStep dc t (f s).2.1.val (f (s + 1)).2.1.val
      (succTrans tm (Ps s)).2.2.2.1 m gc ht (by rw [hm, hds]) (by rw [hg, hds]) hhead

/-- **A stage of a real walk is accepted.** The two branches of `Complexity.StepData` are
exactly the two acceptance lemmas. -/
theorem stage_accepts_of_stepData (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ)
    (tgt : ℕ) (f : ℕ → Code tm.Q kk x.length S) (cA cB : ℕ → Fin (jj + 1))
    (cO cN : Fin (jj + 1))
    (hcA : ∀ p, p < kk + 3 → cA p ≠ L.toWalkLayout.res)
    (hcB : ∀ p, p < kk + 3 → cB p ≠ L.toWalkLayout.res)
    (hcO : cO ≠ L.toWalkLayout.res) (hcN : cN ≠ L.toWalkLayout.res)
    (s : ℕ) (cells : Fin (jj + 1) → ℕ → Γ)
    (hc : StageCols x L dc Ps ds cOlds cNews tgt f cA cB cO cN s cells)
    (advance : Bool) (gsym : Γ)
    (hgsym : (f s).2.1.val ≠ 0 → gsym = inSymOf tm x S (f s))
    (hstep : StepData tm x S Ps ds f s)
    (hwc : wc ≤ walkScanLen tm x.length S)
    (hu : cOlds s < 2 ^ wc) (hv : cNews s < 2 ^ wc)
    (hmove : if advance then cNews s = cOlds s + 1 else cOlds s = cNews s) :
    (walkStepScanner tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
        L.toWalkLayout.res cO cN wc advance dc cA cB).emit
      ((walkStepScanner tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
        L.toWalkLayout.res cO cN wc advance dc cA cB).run
        (fun q i => checkedCells cells L.toWalkLayout.par L.toWalkLayout.res gsym i q)
        (walkScanLen tm x.length S)) = true := by
  rcases hstep with ⟨hstay, hd⟩ | ⟨β, hPs, hsucc, hds, hclampIn, hclampW, hclampO, hleft, hne⟩
  · exact stage_accepts_stay x L dc Ps ds cOlds cNews tgt f cA cB cO cN hcA hcB hcO hcN s cells
      hc advance gsym hstay hd hwc hu hv hmove
  · exact stage_accepts_succ x L dc Ps ds cOlds cNews tgt f cA cB cO cN hcA hcB hcO hcN s cells
      hc advance β gsym hgsym hPs hsucc hds hclampIn hclampW hclampO hleft hne hwc hu hv hmove

/-! ## The stage's contract, in the walk's own terms -/

/-- How long one stage of a walk takes: the guess stage, the parking, the scan and the record. -/
noncomputable def stepTime (x : List Bool) (L : WalkWidths kk jj tm x.length S wc) (rr B : ℕ) :
    ℕ :=
  TM.guessBlocksTime (stepWidth L) L.toWalkLayout.stepBlocks + 1 +
    (1 + 1 + ((stepTargets jj rr).length * (B + 3) + 1)) + 1 +
    (2 + 1 + (2 * walkScanLen tm x.length S + 3) + 1 + 1 + 1 + 1)


/-- **One stage of a real walk carries the walk's invariant.** Everything the stage needs is
either a fact about the guess stream (`hs`, `hcols`) or a fact about the walk (`hstep`); the tape
facts all come from the invariant it starts in. The accumulator keeps its bit, because a real
walk's stage is accepted. -/
theorem walkStep_carries (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ)
    (tgt : ℕ) (f aOld aNew : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool)
    (second advance : Bool) (cA cB : ℕ → Fin (jj + 1)) (cO cN : Fin (jj + 1)) (s : ℕ)
    (cc : Fin r) (v : Bool) (Wa : Fin r → Tape) (B : ℕ)
    (hB1 : 1 ≤ B) (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (bc : ℕ → ℕ → ℕ → Bool)
    (hs : TM.StageBlocks (stepWidth L) L.toWalkLayout.stepBlocks bc g)
    (hb : ∀ p q, bc s p q = stepCert L x dc Ps ds cOlds cNews tgt aOld aNew second s p q)
    (hcols : ∀ W : Fin (jj + 2 + r + 1) → Tape, (∀ i, (W i).StartInvariant) →
      (∀ i, 1 ≤ (W i).head) →
      (∀ p, p < L.toWalkLayout.stepBlocks → (W (stepReg L second p)).head = 1) →
      TM.GuessFrom (fun q => g (s * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks + q))
        (W (Fin.last (jj + 2 + r))) →
      (∀ p, p < kk + 3 → HoldsBits (fun q i => (W (walkReg i)).cells q) 0 (cA p)
        (codeBlockScan tm x S (f s) p)) →
      StageCols x L dc Ps ds cOlds cNews tgt f cA cB cO cN s (stepCells L second W))
    (hcAres : ∀ p, p < kk + 3 → cA p ≠ L.toWalkLayout.res)
    (hcBres : ∀ p, p < kk + 3 → cB p ≠ L.toWalkLayout.res)
    (hcOres : cO ≠ L.toWalkLayout.res) (hcNres : cN ≠ L.toWalkLayout.res)
    (hstep : StepData tm x S Ps ds f s)
    (hwc : wc ≤ walkScanLen tm x.length S)
    (hu : cOlds s < 2 ^ wc) (hv : cNews s < 2 ^ wc)
    (hmove : if advance then cNews s = cOlds s + 1 else cOlds s = cNews s) :
    (walkStepTM r tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
        L.toWalkLayout.res cO cN wc advance dc cA cB
        (stepReg L second) (stepWidth L) L.toWalkLayout.stepBlocks (stepTargets jj r)
        (auxIdx jj cc)).HoareTime
      (fun inp work out => WalkStepInv x L cA f g s inp work out ∧ AccHolds jj cc v Wa inp work out)
      (fun inp work out =>
        WalkStepInv x L cB f g (s + 1) inp work out ∧ AccHolds jj cc v Wa inp work out)
      (stepTime x L r B) := by
  classical
  intro inp₀ W₀ out₀ hpre
  obtain ⟨⟨hinvW, hhW, hone, hblank, hret, hinpEq, houtSI, houth, hgf⟩, hacc⟩ := hpre
  have hinv : WalkStepInv (r := r) x L cA f g s inp₀ W₀ out₀ :=
    ⟨hinvW, hhW, hone, hblank, hret, hinpEq, houtSI, houth, hgf⟩
  have hr1 : ∀ p, p < L.toWalkLayout.stepBlocks → (W₀ (stepReg L second p)).head = 1 :=
    fun p _ => hone (L.toWalkLayout.reg (L.toWalkLayout.stepIdx second p)).castSucc
  have hinpSI := inp_startInvariant_of_walkStepInv x L cA f g s inp₀ W₀ out₀ hinv
  have hinpRead := inp_read_ne_start_of_walkStepInv x L cA f g s inp₀ W₀ out₀ hinv
  have houtRead : out₀.read ≠ Γ.start := houtSI.2 _ houth
  have hpark := parkTape_of_walkStepInv x L cA f g s inp₀ W₀ out₀ hinv
  have hparkHead : (TM.parkTape inp₀).head = max (f s).2.1.val 1 := by rw [hpark]
  have hparkCells : (TM.parkTape inp₀).cells = (Tape.init (x.map Γ.ofBool)).cells := by
    rw [hpark]
  have hSC := hcols W₀ hinvW hhW hr1 hgf hret
  have hscan := scanTape_of_step x L dc Ps ds cOlds cNews tgt aOld aNew bc g second hs s hb W₀
    hinvW hhW hr1 hgf hblank
  have hmv : checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
      (TM.parkTape inp₀).read L.toWalkLayout.mv 1 = dc.encMove (ds s) := by
    rw [checked_cell _ _ _ _ _ L.toWalkLayout.mv_ne_res]
    exact hSC.mv
  have hdr : checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
      (TM.parkTape inp₀).read L.toWalkLayout.dr 1 = dc.enc (ds s) := by
    rw [checked_cell _ _ _ _ _ L.toWalkLayout.dr_ne_res]
    exact hSC.dr
  have hmovedEq := moved_of_stepData tm x S Ps ds f s hstep dc _ _ hmv hdr
    (TM.parkTape inp₀) hparkHead
  have hmoved : ((TM.parkTape inp₀).move (dc.dec
      (checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
        (TM.parkTape inp₀).read L.toWalkLayout.mv 1)
      (checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
        (TM.parkTape inp₀).read L.toWalkLayout.dr 1))).read ≠ Γ.start := by
    rw [hmovedEq]
    show (TM.parkTape inp₀).cells (max (f (s + 1)).2.1.val 1) ≠ Γ.start
    rw [hparkCells]
    exact Tape.init_ofBool_cells_ne_start x _ (le_max_right _ _)
  obtain ⟨c', t, htle, hreach, hhalt, hpost⟩ :=
    walkStepTM_hoareTime r tm x.length S L.toWalkLayout.par L.toWalkLayout.mv
      L.toWalkLayout.dr L.toWalkLayout.res cO cN wc advance dc
      cA cB (stepReg L second) (stepWidth L) L.toWalkLayout.stepBlocks (stepTargets jj r)
      (auxIdx jj cc) stepTargets_nodup (fun i => mem_stepTargets i)
      (fun c => natAdd_notMem_stepTargets c) (fun p c _ => stepReg_ne_natAdd L second p c)
      (fun i => auxIdx_ne_castAdd cc i) (auxIdx_ne_last cc)
      (fun p => stepReg_ne_last L second p) B hB1 inp₀ out₀ W₀ hinpSI houtSI hinpRead
      houtRead hinvW hhW (stepReg_inj L second)
      (head_guessBlocksTapes_le L second W₀ hinvW hhW hone B hB1 hB)
      (walkScanLen tm x.length S) (scanOk_of_step L second W₀ hinvW hhW inp₀ out₀ hinpSI houtSI)
      hscan L.toWalkLayout.par_ne_res
      (scanTape_checked hscan L.toWalkLayout.par L.toWalkLayout.res
        L.toWalkLayout.res_ne_zero _) hmoved inp₀ W₀ out₀ ⟨rfl, rfl, rfl⟩
  have hverdict :
      (walkStepScanner tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
          L.toWalkLayout.res cO cN wc advance dc cA cB).emit
        ((walkStepScanner tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
          L.toWalkLayout.res cO cN wc advance dc cA cB).run
          (TM.scanCol (checkedCells (fun i : Fin (jj + 1) =>
            (TM.guessBlocksTapes (stepReg L second) (stepWidth L) L.toWalkLayout.stepBlocks W₀
              (Fin.castAdd r i.castSucc).castSucc).cells) L.toWalkLayout.par L.toWalkLayout.res
            (TM.parkTape inp₀).read)) (walkScanLen tm x.length S)) = true :=
    stage_accepts_of_stepData x L dc Ps ds cOlds cNews tgt f cA cB cO cN hcAres hcBres hcOres
      hcNres s (stepCells L second W₀) hSC advance (TM.parkTape inp₀).read
      (fun h0 => parkTape_read_of_walkStepInv x L cA f g s inp₀ W₀ out₀ hinv h0) hstep hwc hu hv
      hmove
  obtain ⟨hlast, haux, hinp', hout', hregs, hacc'⟩ := hpost
  rw [hverdict] at hregs hacc'
  obtain ⟨ginv, ghh, -, -, -⟩ := TM.guessBlocksTapes_spec (stepReg L second)
    (fun p => stepReg_ne_last L second p) (stepWidth L) L.toWalkLayout.stepBlocks W₀ hinvW hhW
    (stepReg_inj L second)
  have hchecked := scanTape_checked hscan L.toWalkLayout.par L.toWalkLayout.res
    L.toWalkLayout.res_ne_zero (TM.parkTape inp₀).read
  have hreg : ∀ j : Fin (jj + 1), c'.work (walkReg j)
      = (⟨1, checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
        (TM.parkTape inp₀).read j⟩ : Tape) := by
    intro j
    have h := hregs j.castSucc
    rw [Fin.snoc_castSucc] at h
    exact h
  have hverd : c'.work (Fin.castAdd r (Fin.last (jj + 1))).castSucc
      = (⟨1, (TM.guessBlocksTapes (stepReg L second) (stepWidth L) L.toWalkLayout.stepBlocks W₀
          (Fin.castAdd r (Fin.last (jj + 1))).castSucc).cells⟩ : Tape).write (Γ.ofBool true) := by
    have h := hregs (Fin.last (jj + 1))
    rw [Fin.snoc_last] at h
    exact h
  have haccSI : (c'.work (auxIdx jj cc)).StartInvariant ∧ 1 ≤ (c'.work (auxIdx jj cc)).head := by
    have hh0 := hhW (auxIdx jj cc)
    rw [hacc']
    refine ⟨⟨?_, ?_⟩, hh0⟩
    · show Function.update (W₀ (auxIdx jj cc)).cells (W₀ (auxIdx jj cc)).head _ 0 = Γ.start
      rw [Function.update_of_ne (by omega)]
      exact (hinvW (auxIdx jj cc)).1
    · intro q hq
      show Function.update (W₀ (auxIdx jj cc)).cells (W₀ (auxIdx jj cc)).head _ q ≠ Γ.start
      by_cases hqh : q = (W₀ (auxIdx jj cc)).head
      · rw [hqh, Function.update_self]
        split_ifs <;> exact fun hc => Γ.noConfusion hc
      · rw [Function.update_of_ne hqh]
        exact (hinvW (auxIdx jj cc)).2 q hq
  have hall : ∀ i : Fin (jj + 2 + r + 1),
      (c'.work i).StartInvariant ∧ 1 ≤ (c'.work i).head := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [hlast]
      exact ⟨ginv _, ghh _⟩
    · refine Fin.addCases (fun i' => ?_) (fun c => ?_) i
      · refine Fin.lastCases ?_ (fun j => ?_) i'
        · rw [hverd]
          refine ⟨?_, ?_⟩
          · have hSI : (⟨1, (TM.guessBlocksTapes (stepReg L second) (stepWidth L)
                L.toWalkLayout.stepBlocks W₀
                (Fin.castAdd r (Fin.last (jj + 1))).castSucc).cells⟩ : Tape).StartInvariant :=
              ginv (Fin.castAdd r (Fin.last (jj + 1))).castSucc
            rw [← Γw.ofBool_toΓ]
            exact hSI.write (Γw.ofBool true)
          · rw [Tape.write_head]
        · show (c'.work (walkReg j)).StartInvariant ∧ 1 ≤ (c'.work (walkReg j)).head
          rw [hreg j]
          exact ⟨⟨hchecked.start j, fun q hq => hchecked.ne_start j q hq⟩, le_rfl⟩
      · by_cases hcc : c = cc
        · subst hcc
          exact haccSI
        · rw [haux c (fun hc => hcc (Fin.ext (by
            have hv := congrArg Fin.val hc
            simp only [auxIdx, val_natAdd_castSucc] at hv
            omega)))]
          exact ⟨hinvW _, hhW _⟩
  refine ⟨c', t, htle, hreach, hhalt,
    ⟨fun i => (hall i).1, fun i => (hall i).2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hverd, Tape.write_head]
    · show (c'.work (walkReg j)).head = 1
      rw [hreg j]
  · show (c'.work (walkReg (L.toWalkLayout.reg L.toWalkLayout.rulerIdx))).cells _ = Γ.blank
    rw [hreg]
    show checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
      (TM.parkTape inp₀).read (L.toWalkLayout.reg L.toWalkLayout.rulerIdx) _ = Γ.blank
    rw [L.toWalkLayout.ruler_zero]
    exact hchecked.blank
  · intro p hp q hq
    show (c'.work (walkReg (cB p))).cells _ = _
    rw [hreg (cB p)]
    exact holdsBits_checked (hcBres p hp) (hSC.codeB p hp) q hq
  · rw [hinp']
    exact hmovedEq.trans (by rw [hparkCells])
  · rw [hout']
    exact houtSI
  · rw [hout']
    show 1 ≤ max out₀.head 1
    omega
  · rw [hlast]
    exact guessFrom_after_step L second W₀ hinvW hhW g s hgf
  · refine ⟨?_, fun c' hne => ?_⟩
    swap
    · exact (haux c' (fun hc => hne (Fin.ext (by
        have hv := congrArg Fin.val hc
        simp only [auxIdx, val_natAdd_castSucc] at hv
        omega)))).trans (hacc.2 c' hne)
    show (c'.work (auxIdx jj cc)).read = Γ.ofBool v
    rw [hacc']
    show Function.update (W₀ (auxIdx jj cc)).cells (W₀ (auxIdx jj cc)).head _
      (W₀ (auxIdx jj cc)).head = _
    rw [Function.update_self]
    have hread : (W₀ (auxIdx jj cc)).read = Γ.ofBool v := hacc.1
    cases v with
    | false =>
        rw [if_neg (by rintro ⟨-, hc⟩; rw [hread] at hc; exact Γ.noConfusion hc)]
        rfl
    | true =>
        rw [if_pos ⟨rfl, hread⟩]
        rfl

/-! ## A pair of stages -/

/-- **The certificate a whole walk reads.** The first stage of a pair guesses the new code into
the second family of registers, the second guesses it back into the first — so the certificate
alternates with the stage's parity, and one guess stream serves the whole walk. -/
noncomputable def pairCert {nn : ℕ} (L : WalkWidths kk jj tm nn S wc) (x : List Bool)
    (dc : DirCodec) (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ)
    (tgt : ℕ) (f : ℕ → Code tm.Q kk x.length S) : ℕ → ℕ → ℕ → Bool :=
  fun s p q =>
    if s % 2 = 0 then
      stepCert L x dc Ps ds cOlds cNews tgt f (fun s => f (s + 1)) false s p q
    else stepCert L x dc Ps ds cOlds cNews tgt (fun s => f (s + 1)) f true s p q

theorem pairCert_even {nn : ℕ} (L : WalkWidths kk jj tm nn S wc) (x : List Bool)
    (dc : DirCodec) (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ)
    (tgt : ℕ) (f : ℕ → Code tm.Q kk x.length S) (s : ℕ) (hs : s % 2 = 0) (p q : ℕ) :
    pairCert L x dc Ps ds cOlds cNews tgt f s p q
      = stepCert L x dc Ps ds cOlds cNews tgt f (fun s => f (s + 1)) false s p q := by
  rw [pairCert, if_pos hs]

theorem pairCert_odd {nn : ℕ} (L : WalkWidths kk jj tm nn S wc) (x : List Bool)
    (dc : DirCodec) (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ)
    (tgt : ℕ) (f : ℕ → Code tm.Q kk x.length S) (s : ℕ) (hs : s % 2 = 1) (p q : ℕ) :
    pairCert L x dc Ps ds cOlds cNews tgt f s p q
      = stepCert L x dc Ps ds cOlds cNews tgt (fun s => f (s + 1)) f true s p q := by
  rw [pairCert, if_neg (by omega)]

/-- **The invariant survives a combinator's phase boundary.** Every tape it describes carries its
left marker with the head off it, so the reset that `TM.seqTM` runs between its two machines is
the identity on all of them. -/
theorem walkStepInv_transition (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (cOld : ℕ → Fin (jj + 1)) (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool) (s : ℕ)
    (cc : Fin r) (v : Bool) (Wa : Fin r → Tape) (inp : Tape)
    (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (h : WalkStepInv (r := r) x L cOld f g s inp work out ∧ AccHolds jj cc v Wa inp work out) :
    (WalkStepInv (r := r) x L cOld f g s (TM.transitionInput inp)
      (fun i => TM.transitionTape (work i)) (TM.transitionTape out) ∧
      AccHolds jj cc v Wa (TM.transitionInput inp) (fun i => TM.transitionTape (work i))
        (TM.transitionTape out)) := by
  have hinp : TM.transitionInput inp = inp :=
    TM.transitionInput_eq_self
      (inp_read_ne_start_of_walkStepInv x L cOld f g s inp work out h.1)
  have hwork : ∀ i, TM.transitionTape (work i) = work i := fun i =>
    TM.transitionTape_eq_self ((h.1.1 i).read_ne_start (h.1.2.1 i))
  have hout : TM.transitionTape out = out :=
    TM.transitionTape_eq_self (h.1.2.2.2.2.2.2.1.read_ne_start h.1.2.2.2.2.2.2.2.1)
  rw [hinp, hout, show (fun i => TM.transitionTape (work i)) = work from funext hwork]
  exact h

/-- **A pair of stages carries the walk two steps.** The two code families swap roles between
the stages, so the pair returns each code to the register it started in — which is what lets the
loop repeat the same body. -/
theorem walkPair_carries (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ)
    (tgt : ℕ) (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool) (s : ℕ) (hs2 : s % 2 = 0)
    (cc : Fin r) (v : Bool) (Wa : Fin r → Tape) (B : ℕ)
    (hB1 : 1 ≤ B) (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hs : TM.StageBlocks (stepWidth L) L.toWalkLayout.stepBlocks
      (pairCert L x dc Ps ds cOlds cNews tgt f) g)
    (hstep0 : StepData tm x S Ps ds f s) (hstep1 : StepData tm x S Ps ds f (s + 1))
    (hwc : wc ≤ walkScanLen tm x.length S)
    (hu0 : cOlds s < 2 ^ wc) (hv0 : cNews s < 2 ^ wc)
    (hu1 : cOlds (s + 1) < 2 ^ wc) (hv1 : cNews (s + 1) < 2 ^ wc)
    (hc0 : cOlds s = cNews s) (hc1 : cOlds (s + 1) = cNews (s + 1)) :
    (walkPairTM r tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
        L.toWalkLayout.res L.toWalkLayout.cnt L.toWalkLayout.cnt' wc dc
        L.toWalkLayout.codeA L.toWalkLayout.codeB (stepReg L false) (stepReg L true)
        (stepWidth L) L.toWalkLayout.stepBlocks (stepTargets jj r) (auxIdx jj cc)).HoareTime
      (fun inp work out => WalkStepInv x L L.toWalkLayout.codeA f g s inp work out ∧
        AccHolds jj cc v Wa inp work out)
      (fun inp work out => WalkStepInv x L L.toWalkLayout.codeA f g (s + 2) inp work out ∧
        AccHolds jj cc v Wa inp work out)
      (stepTime x L r B + 1 + stepTime x L r B) := by
  refine TM.seqTM_hoareTime _ _
    (mid := fun inp work out => WalkStepInv x L L.toWalkLayout.codeB f g (s + 1) inp work out ∧
      AccHolds jj cc v Wa inp work out)
    (mid' := fun inp work out => WalkStepInv x L L.toWalkLayout.codeB f g (s + 1) inp work out ∧
      AccHolds jj cc v Wa inp work out)
    ?_ (walkStepInv_transition x L L.toWalkLayout.codeB f g (s + 1) cc v Wa) ?_
  · exact walkStep_carries x L dc Ps ds cOlds cNews tgt f f (fun s => f (s + 1)) g false false
      L.toWalkLayout.codeA L.toWalkLayout.codeB L.toWalkLayout.cnt L.toWalkLayout.cnt' s cc v Wa
      B hB1 hB _ hs (fun p q => pairCert_even L x dc Ps ds cOlds cNews tgt f s hs2 p q)
      (fun W hinvW hhW hr1 hgf hret => stepCols_holds_first x L dc Ps ds cOlds cNews tgt f
        (pairCert L x dc Ps ds cOlds cNews tgt f) g s hs
        (fun p q => pairCert_even L x dc Ps ds cOlds cNews tgt f s hs2 p q)
        W hinvW hhW hr1 hgf hret)
      (fun p hp => L.toWalkLayout.codeA_ne_res hp) (fun p hp => L.toWalkLayout.codeB_ne_res hp)
      L.toWalkLayout.cnt_ne_res L.toWalkLayout.cnt'_ne_res hstep0 hwc hu0 hv0 hc0
  · have hodd : (s + 1) % 2 = 1 := by omega
    exact walkStep_carries x L dc Ps ds cOlds cNews tgt f (fun s => f (s + 1)) f g true false
      L.toWalkLayout.codeB L.toWalkLayout.codeA L.toWalkLayout.cnt' L.toWalkLayout.cnt (s + 1)
      cc v Wa B hB1 hB _ hs
      (fun p q => pairCert_odd L x dc Ps ds cOlds cNews tgt f (s + 1) hodd p q)
      (fun W hinvW hhW hr1 hgf hret => (stepCols_holds_second x L dc Ps ds cOlds cNews tgt f
        (pairCert L x dc Ps ds cOlds cNews tgt f) g (s + 1) hs
        (fun p q => pairCert_odd L x dc Ps ds cOlds cNews tgt f (s + 1) hodd p q)
        W hinvW hhW hr1 hgf hret).swapCnt hc1.symm)
      (fun p hp => L.toWalkLayout.codeB_ne_res hp) (fun p hp => L.toWalkLayout.codeA_ne_res hp)
      L.toWalkLayout.cnt'_ne_res L.toWalkLayout.cnt_ne_res hstep1 hwc hu1 hv1 hc1

/-! ## The walk loop -/

/-- **A canonical binary counter tape carries its left marker.** -/
theorem startInvariant_of_hasBinaryNat {t : Tape} {value : ℕ} (h : t.HasBinaryNat value) :
    t.StartInvariant ∧ t.head = 1 := by
  refine ⟨⟨h.1, fun j hj => ?_⟩, h.2.1⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  by_cases hi : i < value.bits.length
  · rw [h.2.2.1 i hi]
    exact Γ.ofBool_ne_start _
  · rw [h.2.2.2 i (by omega)]
    exact fun hc => Γ.noConfusion hc

/-- **The invariant does not see the auxiliary tapes.** So the loop driver may keep its counter
on one of them. -/
theorem walkStepInv_update_aux (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (cOld : ℕ → Fin (jj + 1)) (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool) (s : ℕ)
    (c₀ : Fin r) (t : Tape) (htSI : t.StartInvariant) (hth : 1 ≤ t.head)
    (inp : Tape) (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (h : WalkStepInv (r := r) x L cOld f g s inp work out) :
    WalkStepInv (r := r) x L cOld f g s inp (Function.update work (auxIdx jj c₀) t) out := by
  classical
  have hupd : ∀ i : Fin (jj + 2 + r + 1), i ≠ auxIdx jj c₀ →
      Function.update work (auxIdx jj c₀) t i = work i := fun i hi =>
    Function.update_of_ne hi _ _
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, ?_, fun p hp => ?_,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, ?_⟩
  · by_cases hi : i = auxIdx jj c₀
    · rw [hi, Function.update_self]; exact htSI
    · rw [hupd i hi]; exact h.1 i
  · by_cases hi : i = auxIdx jj c₀
    · rw [hi, Function.update_self]; exact hth
    · rw [hupd i hi]; exact h.2.1 i
  · rw [hupd _ (fun hc => auxIdx_ne_castAdd c₀ i hc.symm)]
    exact h.2.2.1 i
  · rw [hupd _ (walkReg_ne_auxIdx _ c₀)]
    exact h.2.2.2.1
  · intro q hq
    show (Function.update work (auxIdx jj c₀) t (walkReg (cOld p))).cells _ = _
    rw [hupd _ (walkReg_ne_auxIdx _ c₀)]
    exact h.2.2.2.2.1 p hp q hq
  · rw [hupd _ (Ne.symm (auxIdx_ne_last c₀))]
    exact h.2.2.2.2.2.2.2.2

/-- The walk loop's invariant after `j` iterations: two stages of the walk per iteration, and
the accumulator still carrying its bit. -/
def WalkP (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool) (cc : Fin r) (v : Bool) :
    ℕ → TM.TapePred (jj + 2 + r + 1) :=
  fun j inp work out => WalkStepInv (r := r) x L L.toWalkLayout.codeA f g (2 * j) inp work out ∧
    (work (auxIdx jj cc)).read = Γ.ofBool v

/-- **The body of the walk loop meets the count-up driver's contract.** The pair of stages
carries the invariant two steps and touches no auxiliary tape but the accumulator, so the
counter and the limit come through untouched. -/
theorem walkPair_binaryForBody (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ)
    (tgt : ℕ) (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool)
    (cc cnt lim : Fin r) (hcnt : cnt ≠ cc) (hlim : lim ≠ cc)
    (v : Bool) (B : ℕ)
    (hB1 : 1 ≤ B) (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hs : TM.StageBlocks (stepWidth L) L.toWalkLayout.stepBlocks
      (pairCert L x dc Ps ds cOlds cNews tgt f) g)
    (hwc : wc ≤ walkScanLen tm x.length S)
    (hcO : ∀ s, cOlds s < 2 ^ wc) (hcN : ∀ s, cNews s < 2 ^ wc)
    (heq : ∀ s, cOlds s = cNews s)
    (N : ℕ) (hstep : ∀ s, s < 2 * N → StepData tm x S Ps ds f s) (value : ℕ) (hvN : value < N) :
    (walkPairTM r tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
        L.toWalkLayout.res L.toWalkLayout.cnt L.toWalkLayout.cnt' wc dc
        L.toWalkLayout.codeA L.toWalkLayout.codeB (stepReg L false) (stepReg L true)
        (stepWidth L) L.toWalkLayout.stepBlocks (stepTargets jj r)
        (auxIdx jj cc)).HoareTime
      (TM.BinaryForFrame (auxIdx jj cnt) (auxIdx jj lim) N (WalkP x L f g cc v) value)
      (TM.BinaryForBodyPost (auxIdx jj cnt) (auxIdx jj lim) N (WalkP x L f g cc v) value)
      (stepTime x L r B + 1 + stepTime x L r B) := by
  classical
  intro inp₀ W₀ out₀ hpre
  obtain ⟨⟨hinv, hbit⟩, hcnt0, hlim0, -, -, -⟩ := hpre
  obtain ⟨c', t, htle, hreach, hhalt, hinv', hbit', hframe'⟩ :=
    walkPair_carries x L dc Ps ds cOlds cNews tgt f g (2 * value) (by omega) cc v
      (fun c => W₀ (auxIdx jj c)) B hB1 hB hs (hstep _ (by omega)) (hstep _ (by omega)) hwc
      (hcO _) (hcN _) (hcO _) (hcN _) (heq _) (heq _) inp₀ W₀ out₀
      ⟨hinv, hbit, fun c' _ => rfl⟩
  refine ⟨c', t, htle, hreach, hhalt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hframe' cnt hcnt]
    exact hcnt0
  · rw [hframe' lim hlim]
    exact hlim0
  · exact inp_read_ne_start_of_walkStepInv x L L.toWalkLayout.codeA f g (2 * value + 2)
      c'.input c'.work c'.output hinv'
  · exact fun i => (hinv'.1 i).read_ne_start (hinv'.2.1 i)
  · exact hinv'.2.2.2.2.2.2.1.read_ne_start hinv'.2.2.2.2.2.2.2.1
  · intro tc htc
    obtain ⟨htSI, hth⟩ := startInvariant_of_hasBinaryNat htc
    refine ⟨?_, ?_⟩
    · rw [show 2 * (value + 1) = 2 * value + 2 by omega]
      exact walkStepInv_update_aux x L L.toWalkLayout.codeA f g (2 * value + 2) cnt tc htSI
        (by omega) c'.input c'.work c'.output hinv'
    · rw [Function.update_of_ne (fun hc => hcnt (Fin.ext (by
        have hv := congrArg Fin.val hc
        simp only [auxIdx, val_natAdd_castSucc] at hv
        omega)).symm)]
      exact hbit'

/-- Distinct auxiliary slots are distinct tapes. -/
theorem auxIdx_injective {c c' : Fin r} (h : c ≠ c') : auxIdx jj c ≠ auxIdx jj c' := by
  intro hc
  exact h (Fin.ext (by
    have hv := congrArg Fin.val hc
    simp only [auxIdx, val_natAdd_castSucc] at hv
    omega))

/-- **The walk loop carries the walk to its end.** `N` iterations of the paired step take the
invariant from stage `0` to stage `2 * N`, with the accumulator's bit intact — so a walk whose
every stage is real is accepted, and the loop's own counter never leaves the auxiliary tapes. -/
theorem walkLoop_carries (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ)
    (tgt : ℕ) (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool)
    (cc cnt lim : Fin r) (hcnt : cnt ≠ cc) (hlim : lim ≠ cc) (hcl : cnt ≠ lim)
    (v : Bool) (B : ℕ)
    (hB1 : 1 ≤ B) (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hs : TM.StageBlocks (stepWidth L) L.toWalkLayout.stepBlocks
      (pairCert L x dc Ps ds cOlds cNews tgt f) g)
    (hwc : wc ≤ walkScanLen tm x.length S)
    (hcO : ∀ s, cOlds s < 2 ^ wc) (hcN : ∀ s, cNews s < 2 ^ wc)
    (heq : ∀ s, cOlds s = cNews s)
    (N : ℕ) (hstep : ∀ s, s < 2 * N → StepData tm x S Ps ds f s) :
    (walkLoopTM r tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
        L.toWalkLayout.res L.toWalkLayout.cnt L.toWalkLayout.cnt' dc
        L.toWalkLayout.codeA L.toWalkLayout.codeB (stepReg L false) (stepReg L true)
        (stepWidth L) L.toWalkLayout.stepBlocks wc (stepTargets jj r) (auxIdx jj cc)
        (auxIdx jj cnt) (auxIdx jj lim)).HoareTime
      (TM.BinaryForFrame (auxIdx jj cnt) (auxIdx jj lim) N (WalkP x L f g cc v) 0)
      (TM.BinaryForFrame (auxIdx jj cnt) (auxIdx jj lim) N (WalkP x L f g cc v) N)
      (TM.binaryForLoopTime (fun _ => stepTime x L r B + 1 + stepTime x L r B) N 0 N) :=
  TM.binaryForTM_hoareTime (auxIdx_injective hcl) N
    (fun _ => stepTime x L r B + 1 + stepTime x L r B) (WalkP x L f g cc v)
    (fun value hv => walkPair_binaryForBody x L dc Ps ds cOlds cNews tgt f g cc cnt lim hcnt
      hlim v B hB1 hB hs hwc hcO hcN heq N hstep value hv)

/-- **Some guess stream runs a real walk.** The certificate always exists — distinct stages and
blocks never share a guess-tape cell — so a walk that really happens is one the nondeterminism
can take. -/
theorem exists_walkLoop_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ)
    (tgt : ℕ) (f : ℕ → Code tm.Q kk x.length S)
    (cc cnt lim : Fin r) (hcnt : cnt ≠ cc) (hlim : lim ≠ cc) (hcl : cnt ≠ lim)
    (v : Bool) (B : ℕ)
    (hB1 : 1 ≤ B) (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hwc : wc ≤ walkScanLen tm x.length S)
    (hcO : ∀ s, cOlds s < 2 ^ wc) (hcN : ∀ s, cNews s < 2 ^ wc)
    (heq : ∀ s, cOlds s = cNews s)
    (N : ℕ) (hstep : ∀ s, s < 2 * N → StepData tm x S Ps ds f s) :
    ∃ g : ℕ → Bool,
      (walkLoopTM r tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
          L.toWalkLayout.res L.toWalkLayout.cnt L.toWalkLayout.cnt' dc
          L.toWalkLayout.codeA L.toWalkLayout.codeB (stepReg L false) (stepReg L true)
          (stepWidth L) L.toWalkLayout.stepBlocks wc (stepTargets jj r) (auxIdx jj cc)
          (auxIdx jj cnt) (auxIdx jj lim)).HoareTime
        (TM.BinaryForFrame (auxIdx jj cnt) (auxIdx jj lim) N (WalkP x L f g cc v) 0)
        (TM.BinaryForFrame (auxIdx jj cnt) (auxIdx jj lim) N (WalkP x L f g cc v) N)
        (TM.binaryForLoopTime (fun _ => stepTime x L r B + 1 + stepTime x L r B) N 0 N) := by
  obtain ⟨g, hg⟩ := TM.exists_stageBlocks (stepWidth L) (t := L.toWalkLayout.stepBlocks)
    (by rw [WalkLayout.stepBlocks]; omega) (pairCert L x dc Ps ds cOlds cNews tgt f)
  exact ⟨g, walkLoop_carries x L dc Ps ds cOlds cNews tgt f g cc cnt lim hcnt hlim hcl v B
    hB1 hB hg hwc hcO hcN heq N hstep⟩

/-! ## Reading a window back off a register

The walk's checks are stated about the windows two registers *hold*; in the soundness direction
nothing hands them one, because the register carries whatever the guess put there. What saves it
is that `Complexity.blockEmit` counts the head markers on both registers and rejects unless there
is exactly one — so acceptance itself says the guessed register spells out a window. -/

/-- The symbol two bits name. -/
def gammaOfBits : Bool × Bool → Γ
  | (false, false) => Γ.zero
  | (true, false) => Γ.one
  | (false, true) => Γ.blank
  | (true, true) => Γ.start

@[simp] theorem gammaBits_gammaOfBits (b : Bool × Bool) : gammaBits (gammaOfBits b) = b := by
  obtain ⟨b₁, b₂⟩ := b
  cases b₁ <;> cases b₂ <;> rfl

/-- A cell that carries a bit reads back as that bit. -/
theorem ofBool_decide_of_bit {c : Γ} (h : c = Γ.zero ∨ c = Γ.one) :
    Γ.ofBool (decide (c = Γ.one)) = c := by
  rcases h with h | h <;> rw [h] <;> rfl

/-- **No marker anywhere**, when the count is zero. -/
theorem markOf_eq_false_of_markCount_zero {j : ℕ} (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ)
    (rg : Fin (j + 1)) : ∀ m, markCount cols off rg m = 0 → ∀ p, p < m →
      markOf cols off rg p = false := by
  intro m
  induction m with
  | zero => intro _ p hp; omega
  | succ m ih =>
      intro h p hp
      rw [markCount] at h
      have hm : markOf cols off rg m = false := by
        by_contra hc
        rw [if_pos (by simpa using hc)] at h
        omega
      rw [if_neg (by simpa using hm), Nat.add_zero] at h
      rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hlt | rfl
      · exact ih h p hlt
      · exact hm

/-- **Exactly one marker**, when the count is one. -/
theorem exists_unique_mark {j : ℕ} (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) (rg : Fin (j + 1)) :
    ∀ m, markCount cols off rg m = 1 →
      ∃ p, p < m ∧ ∀ p', p' < m → (markOf cols off rg p' = true ↔ p' = p) := by
  intro m
  induction m with
  | zero => intro h; rw [markCount] at h; omega
  | succ m ih =>
      intro h
      rw [markCount] at h
      by_cases hm : markOf cols off rg m = true
      · rw [if_pos hm] at h
        have h0 : markCount cols off rg m = 0 := by omega
        refine ⟨m, by omega, fun p' hp' => ⟨fun _ => ?_, fun hpe => ?_⟩⟩
        · by_contra hc
          have hlt : p' < m := by omega
          rw [markOf_eq_false_of_markCount_zero cols off rg m h0 p' hlt] at *
          simp_all
        · rw [hpe]; exact hm
      · rw [if_neg (by simpa using hm), Nat.add_zero] at h
        obtain ⟨p, hp, hall⟩ := ih h
        refine ⟨p, by omega, fun p' hp' => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hp' with hlt | rfl
        · exact hall p' hlt
        · constructor
          · intro hc; exact absurd hc (by simpa using hm)
          · intro hc; omega

/-- **A register with one marker spells out a window.** The cells are bits — a guess writes
nothing else — and the marker names the head, so the register holds a window and the walk's
checks apply to it. This is what turns `Complexity.blockEmit`'s marker count into the hypothesis
`Complexity.windowScanner_decides` asks for. -/
theorem exists_holdsWindow {m : ℕ} [NeZero m] {j : ℕ} (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ)
    (rg : Fin (j + 1))
    (hbit : ∀ q, q < m * 3 → cols (off + q + 1) rg = Γ.zero ∨ cols (off + q + 1) rg = Γ.one)
    (hcount : markCount cols off rg m = 1) :
    ∃ hd : Fin m, HoldsWindow cols off rg hd
      (fun p => gammaOfBits (symOf cols off rg p.val)) := by
  obtain ⟨p₀, hp₀, hall⟩ := exists_unique_mark cols off rg m hcount
  refine ⟨⟨p₀, hp₀⟩, fun q hq => ?_⟩
  obtain ⟨p, i, hi, rfl⟩ : ∃ p i, i < 3 ∧ q = p * 3 + i :=
    ⟨q / 3, q % 3, Nat.mod_lt _ (by omega), by omega⟩
  have hplt : p < m := by omega
  rw [enc_getElem ⟨p₀, hp₀⟩ (fun p => gammaOfBits (symOf cols off rg p.val)) ⟨p, hplt⟩ i hi]
  have hmark := hall p hplt
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  · have hb0 : cols (off + 3 * p + 1) rg = Γ.zero ∨ cols (off + 3 * p + 1) rg = Γ.one := by
      have h := hbit (p * 3 + 0) (by omega)
      rwa [show off + (p * 3 + 0) + 1 = off + 3 * p + 1 by omega] at h
    have hmk : markOf cols off rg p = decide (p = p₀) := by
      rw [Bool.eq_iff_iff, decide_eq_true_eq]
      exact hmark
    have hfin : (decide ((⟨p, hplt⟩ : Fin m) = ⟨p₀, hp₀⟩)) = decide (p = p₀) := by
      rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq, Fin.mk.injEq]
    show cols (off + (p * 3 + 0) + 1) rg = Γ.ofBool (decide ((⟨p, hplt⟩ : Fin m) = ⟨p₀, hp₀⟩))
    rw [show off + (p * 3 + 0) + 1 = off + 3 * p + 1 by omega, hfin, ← hmk, markOf,
      ofBool_decide_of_bit hb0]
  · have hb1 : cols (off + 3 * p + 2) rg = Γ.zero ∨ cols (off + 3 * p + 2) rg = Γ.one := by
      have h := hbit (p * 3 + 1) (by omega)
      rwa [show off + (p * 3 + 1) + 1 = off + 3 * p + 2 by omega] at h
    show cols (off + (p * 3 + 1) + 1) rg
      = Γ.ofBool (gammaBits (gammaOfBits (symOf cols off rg p))).1
    rw [gammaBits_gammaOfBits]
    show cols (off + (p * 3 + 1) + 1) rg = Γ.ofBool (decide (cols (off + 3 * p + 2) rg = Γ.one))
    rw [show off + (p * 3 + 1) + 1 = off + 3 * p + 2 by omega, ofBool_decide_of_bit hb1]
  · have hb2 : cols (off + 3 * p + 3) rg = Γ.zero ∨ cols (off + 3 * p + 3) rg = Γ.one := by
      have h := hbit (p * 3 + 2) (by omega)
      rwa [show off + (p * 3 + 2) + 1 = off + 3 * p + 3 by omega] at h
    show cols (off + (p * 3 + 2) + 1) rg
      = Γ.ofBool (gammaBits (gammaOfBits (symOf cols off rg p))).2
    rw [gammaBits_gammaOfBits]
    show cols (off + (p * 3 + 2) + 1) rg = Γ.ofBool (decide (cols (off + 3 * p + 3) rg = Γ.one))
    rw [show off + (p * 3 + 2) + 1 = off + 3 * p + 3 by omega, ofBool_decide_of_bit hb2]

/-- **The block check counts the markers on the register it is checking.** So its acceptance is
what supplies `Complexity.exists_holdsWindow` with its hypothesis. -/
theorem markCount_of_blockEmit {j m : ℕ} (a b : Fin (j + 1)) (symB wrB : Bool × Bool) (d : Dir3)
    (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) (hm : 0 < m)
    (hend : markOf cols off a m = false)
    (h : blockEmit d (Scanner.chunkRun (blockStep a b symB wrB d) cols off blockStart m)
      = true) : markCount cols off b m = 1 :=
  ((blockEmit_run a b symB wrB d cols off m hm hend).mp h).2.1

/-- **The window checker, in the soundness direction.** Nothing hands the check a window for the
register it is checking — the guess wrote arbitrary bits there — but its acceptance says the
marker count is one, and that is enough to read a window back. So an accepting scan does exhibit
the stepped window, rather than assuming it. -/
theorem windowScanner_sound {kk : ℕ} (tm : NTM kk) (i : Fin kk) (cols : ℕ → Fin 3 → Γ) (S : ℕ)
    (hd : Fin (S + 1)) (cl : Fin (S + 1) → Γ)
    (ha : HoldsWindow cols (succParamsCodec tm.Q kk).width 1 hd cl)
    (hbit : ∀ q, q < (S + 1) * 3 →
      cols ((succParamsCodec tm.Q kk).width + q + 1) 2 = Γ.zero ∨
      cols ((succParamsCodec tm.Q kk).width + q + 1) 2 = Γ.one)
    (hend : markOf cols (succParamsCodec tm.Q kk).width 1 (S + 1) = false)
    (hemit : (windowScanner tm i).emit ((windowScanner tm i).run cols
      ((succParamsCodec tm.Q kk).width + 3 * (S + 1))) = true) :
    ∃ (hd' : Fin (S + 1)) (cl' : Fin (S + 1) → Γ),
      HoldsWindow cols (succParamsCodec tm.Q kk).width 2 hd' cl' ∧
      cl hd = (windowParams tm cols).wSym i ∧
      (∀ p, cl' p = if p = hd ∧ 0 < p.val then succWrite tm (windowParams tm cols) i
        else cl p) ∧
      hd'.val = movedIdx (succDir tm (windowParams tm cols) i) hd.val := by
  have hrun := hemit
  rw [windowScanner_run tm i cols S] at hrun
  have hcount := markCount_of_blockEmit 1 2 (gammaBits ((windowParams tm cols).wSym i))
    (gammaBits (succWrite tm (windowParams tm cols) i))
    (succDir tm (windowParams tm cols) i) cols (succParamsCodec tm.Q kk).width
    (by omega) hend hrun
  obtain ⟨hd', hw'⟩ := exists_holdsWindow (m := S + 1) cols (succParamsCodec tm.Q kk).width 2
    hbit hcount
  exact ⟨hd', _, hw',
    (windowScanner_decides tm i cols S hd hd' cl _ ha hw' hend).mp hemit⟩

/-- **The output-window checker, in the soundness direction.** The same as
`Complexity.windowScanner_sound`, for the output tape's window. -/
theorem outputScanner_sound {kk : ℕ} (tm : NTM kk) (cols : ℕ → Fin 3 → Γ) (S : ℕ)
    (hd : Fin (S + 2)) (cl : Fin (S + 2) → Γ)
    (ha : HoldsWindow cols (succParamsCodec tm.Q kk).width 1 hd cl)
    (hbit : ∀ q, q < (S + 2) * 3 →
      cols ((succParamsCodec tm.Q kk).width + q + 1) 2 = Γ.zero ∨
      cols ((succParamsCodec tm.Q kk).width + q + 1) 2 = Γ.one)
    (hend : markOf cols (succParamsCodec tm.Q kk).width 1 (S + 2) = false)
    (hemit : (outputScanner tm).emit ((outputScanner tm).run cols
      ((succParamsCodec tm.Q kk).width + 3 * (S + 2))) = true) :
    ∃ (hd' : Fin (S + 2)) (cl' : Fin (S + 2) → Γ),
      HoldsWindow cols (succParamsCodec tm.Q kk).width 2 hd' cl' ∧
      cl hd = (windowParams tm cols).oSym ∧
      (∀ p, cl' p = if p = hd ∧ 0 < p.val
        then (((succTrans tm (windowParams tm cols)).2.2.1 : Γw) : Γ) else cl p) ∧
      hd'.val = movedIdx (succTrans tm (windowParams tm cols)).2.2.2.2.2 hd.val := by
  have hrun := hemit
  rw [outputScanner_run tm cols S] at hrun
  have hcount := markCount_of_blockEmit 1 2 (gammaBits (windowParams tm cols).oSym)
    (gammaBits (((succTrans tm (windowParams tm cols)).2.2.1 : Γw) : Γ))
    (succTrans tm (windowParams tm cols)).2.2.2.2.2 cols (succParamsCodec tm.Q kk).width
    (by omega) hend hrun
  obtain ⟨hd', hw'⟩ := exists_holdsWindow (m := S + 2) cols (succParamsCodec tm.Q kk).width 2
    hbit hcount
  exact ⟨hd', _, hw', (outputScanner_decides tm cols S hd hd' cl _ ha hw' hend).mp hemit⟩

/-- **What a scan reads a register as, whatever bits it holds**, for a scan that starts at the
first cell. The companion of `Complexity.ofTable_of_holds_zero` that does not assume the register
carries an encoding — which is what the soundness direction has to work with. -/
theorem ofTable_of_holdsBits_zero {j : ℕ} {α : Type} (codec : BitCodec α) (bits : List Bool)
    (hlen : bits.length = codec.width) (cols : ℕ → Fin (j + 1) → Γ) (s w : ℕ)
    (regs : Fin s → Fin (j + 1)) (t : Fin s) (hc : codec.width ≤ w)
    (x₀ : Fin s → Fin w → Bool) (h : HoldsBits cols 0 (regs t) bits) :
    codec.ofTable (tableSlice
        (Scanner.auxRun (⟨0, Nat.zero_lt_succ w⟩, x₀) (Scanner.bitsStep s w regs) cols w).2
        t codec.width hc) = codec.dec bits := by
  have hshift : (fun q => cols (0 + q)) = cols := by
    funext q
    rw [Nat.zero_add]
  have hgen := ofTable_of_holdsBits codec bits hlen cols 0 s w regs t hc x₀
    (by rw [hshift]; exact h)
  rwa [hshift] at hgen

/-- **The slice a scan has of one register is the bits it holds**, for a scan that starts at the
first cell. -/
theorem ofFn_tableSlice_eq_zero {j : ℕ} {α : Type} (codec : BitCodec α) (bits : List Bool)
    (hlen : bits.length = codec.width) (cols : ℕ → Fin (j + 1) → Γ) (s w : ℕ)
    (regs : Fin s → Fin (j + 1)) (t : Fin s) (hc : codec.width ≤ w)
    (x₀ : Fin s → Fin w → Bool) (h : HoldsBits cols 0 (regs t) bits) :
    List.ofFn (tableSlice
        (Scanner.auxRun (⟨0, Nat.zero_lt_succ w⟩, x₀) (Scanner.bitsStep s w regs) cols w).2
        t codec.width hc) = bits := by
  have hshift : (fun q => cols (0 + q)) = cols := by
    funext q
    rw [Nat.zero_add]
  have hgen := ofFn_tableSlice_eq codec bits hlen cols 0 s w regs t hc x₀
    (by rw [hshift]; exact h)
  rwa [hshift] at hgen

/-- **The state checker, in the soundness direction.** The check reports both halves of what
soundness needs: the state the register decodes to is the one the transition names, *and* the
register carries that state's canonical encoding — the second conjunct of
`Complexity.stateScanner`'s verdict, which exists exactly so that a guessed state register is
readable by the next step. -/
theorem stateScanner_sound {kk : ℕ} (tm : NTM kk) (isNew : Bool) (cols : ℕ → Fin 2 → Γ)
    (bits : List Bool) (hlen : bits.length = (qCodec tm.Q).width)
    (h : HoldsBits cols 0 1 bits)
    (hemit : (stateScanner tm isNew).emit ((stateScanner tm isNew).run cols (stateWidth tm))
      = true) :
    (qCodec tm.Q).dec bits
        = (if isNew then succState tm (paramsOfStateTable tm (stateTable tm cols))
          else (paramsOfStateTable tm (stateTable tm cols)).q) ∧
      (qCodec tm.Q).enc ((qCodec tm.Q).dec bits) = bits ∧
      (isNew = true ∨ (qCodec tm.Q).dec bits ≠ tm.qhalt) := by
  rw [stateScanner_run, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    decide_eq_true_eq, Bool.or_eq_true, decide_eq_true_eq] at hemit
  have hdec : stateOfTable tm (stateTable tm cols) = (qCodec tm.Q).dec bits :=
    ofTable_of_holdsBits_zero (qCodec tm.Q) bits hlen cols 2 (stateWidth tm) (fun t => t) 1
      (le_max_right _ _) _ h
  have hbits : stateBitsOfTable tm (stateTable tm cols) = bits := by
    rw [stateBitsOfTable, stateTable]
    exact ofFn_tableSlice_eq_zero (qCodec tm.Q) bits hlen cols 2 (stateWidth tm) (fun t => t) 1
      (le_max_right _ _) _ h
  rw [hdec, hbits] at hemit
  exact ⟨hemit.1.1, hemit.1.2, hemit.2⟩

/-- **Any block of bits is the little-endian encoding of its own value.** So a register carrying
`w` bits carries a number, whatever the guess wrote there. -/
theorem bitsOfLenLE_self {w : ℕ} (bits : List Bool) (hlen : bits.length = w) :
    bitsOfLenLE w (binValLE bits) = bits := by
  rw [← hlen]
  exact bitsOfLenLE_binValLE bits

/-- **The input-head checker, in the soundness direction.** Unlike the state, the head field
needs no decoding step at all: `Complexity.bitsOfLenLE` is a bijection onto the bit blocks of its
width, so the register's contents *are* the encoding of the number the scan reads. -/
theorem headScanner_sound {kk : ℕ} (tm : NTM kk) (cols : ℕ → Fin 3 → Γ) (w : ℕ)
    (bitsA bitsB : List Bool) (hlenA : bitsA.length = w) (hlenB : bitsB.length = w)
    (ha : HoldsBits (fun t => cols ((succParamsCodec tm.Q kk).width + t)) 0 1 bitsA)
    (hb : HoldsBits (fun t => cols ((succParamsCodec tm.Q kk).width + t)) 0 2 bitsB)
    (hleft : (succTrans tm (windowParams tm cols)).2.2.2.1 = Dir3.left → 0 < binValLE bitsA)
    (hemit : (headScanner tm).emit ((headScanner tm).run cols
      ((succParamsCodec tm.Q kk).width + w)) = true) :
    binValLE bitsB
      = movedIdx (succTrans tm (windowParams tm cols)).2.2.2.1 (binValLE bitsA) := by
  refine (headScanner_decides tm cols w (binValLE bitsA) (binValLE bitsB) ?_ ?_ ?_ ?_
    hleft).mp hemit
  · rw [← hlenA]; exact binValLE_lt bitsA
  · rw [← hlenB]; exact binValLE_lt bitsB
  · rw [bitsOfLenLE_self bitsA hlenA]; exact ha
  · rw [bitsOfLenLE_self bitsB hlenB]; exact hb

/-! ## Reading a field out of a guessed block -/

/-- **A field of a block is held where the block is.** A guess writes one block per register; the
checks read the fields inside it at their own offsets, and this is the same statement shifted. -/
theorem holdsBits_slice {jj : ℕ} {cols : ℕ → Fin (jj + 1) → Γ} {r : Fin (jj + 1)}
    {bits : List Bool} (h : HoldsBits cols 0 r bits) (off n : ℕ) (hle : off + n ≤ bits.length) :
    HoldsBits cols off r ((bits.drop off).take n) := by
  intro q hq
  have hqn : q < n := by
    rw [List.length_take, List.length_drop] at hq
    omega
  have hidx : off + q < bits.length := by omega
  have hget : ((bits.drop off).take n)[q]'hq = bits[off + q]'hidx := by
    rw [List.getElem_take, List.getElem_drop]
  rw [hget]
  have := h (off + q) hidx
  rw [show 0 + (off + q) + 1 = off + q + 1 by omega] at this
  exact this

/-- The length of such a field. -/
theorem holdsBits_slice_length (bits : List Bool) (off n : ℕ) (hle : off + n ≤ bits.length) :
    ((bits.drop off).take n).length = n := by
  rw [List.length_take, List.length_drop]
  omega

/-- **A held cell carries a bit.** A guess writes `Γ.ofBool` of its stream and nothing else. -/
theorem cell_bit_of_holdsBits {jj : ℕ} {cols : ℕ → Fin (jj + 1) → Γ} {r : Fin (jj + 1)}
    {bits : List Bool} (h : HoldsBits cols 0 r bits) (q : ℕ) (hq : q < bits.length) :
    cols (q + 1) r = Γ.zero ∨ cols (q + 1) r = Γ.one := by
  have hc := h q hq
  rw [show 0 + q + 1 = q + 1 by omega] at hc
  rw [hc]
  cases bits[q]'hq
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ## The width of each block, unfolded -/

theorem blockLen_st {kk : ℕ} (tm : NTM kk) (nn S : ℕ) :
    blockLen tm nn S 0 = (qCodec tm.Q).width := by
  rw [blockLen, if_pos rfl, codeWidthRaw, if_pos rfl]

theorem blockLen_hd {kk : ℕ} (tm : NTM kk) (nn S : ℕ) :
    blockLen tm nn S 1
      = (succParamsCodec tm.Q kk).width + ((finCodec (nn + S + 2)).width + 1) := by
  rw [blockLen, if_neg (by omega), codeWidthRaw, if_neg (by omega), if_pos rfl]

theorem blockLen_wk {kk : ℕ} (tm : NTM kk) (nn S : ℕ) (p : ℕ) (h2 : 2 ≤ p) (hlt : p < kk + 2) :
    blockLen tm nn S p = (succParamsCodec tm.Q kk).width + ((S + 1) * 3 + 1) := by
  rw [blockLen, if_neg (by omega), codeWidthRaw, if_neg (by omega), if_neg (by omega),
    if_pos hlt]

theorem blockLen_ot {kk : ℕ} (tm : NTM kk) (nn S : ℕ) :
    blockLen tm nn S (kk + 2) = (succParamsCodec tm.Q kk).width + ((S + 2) * 3 + 1) := by
  rw [blockLen, if_neg (by omega), codeWidthRaw, if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

/-! ## Transferring what a register holds to one that agrees with it -/

/-- **Agreement over a range carries a held bitstring across.** -/
theorem holdsBits_transfer {jj : ℕ} {cols : ℕ → Fin (jj + 1) → Γ} {r r' : Fin (jj + 1)}
    {off : ℕ} {bits : List Bool} {len : ℕ}
    (h : HoldsBits cols off r bits) (hle : off + bits.length ≤ len)
    (hagree : ∀ q, 1 ≤ q → q ≤ len → cols q r = cols q r') :
    HoldsBits cols off r' bits := by
  intro q hq
  rw [← hagree (off + q + 1) (by omega) (by omega)]
  exact h q hq

/-- **And a held window.** -/
theorem holdsWindow_transfer {m : ℕ} [NeZero m] {jj : ℕ} {cols : ℕ → Fin (jj + 1) → Γ}
    {r r' : Fin (jj + 1)} {off : ℕ} {hd : Fin m} {cl : Fin m → Γ} {len : ℕ}
    (h : HoldsWindow cols off r hd cl) (hle : off + m * 3 ≤ len)
    (hagree : ∀ q, 1 ≤ q → q ≤ len → cols q r = cols q r') :
    HoldsWindow cols off r' hd cl := by
  intro q hq
  rw [← hagree (off + q + 1) (by omega) (by omega)]
  exact h q hq

/-! ## Where the input head's bound comes from

Every field of a code but the input head carries its own bound: the work and output windows are
marker-encoded, so a marked chunk is inside the window by construction. The input head is a
binary field, and the scans admit any value its width can hold. What bounds it is not a check but
the mathematics — a configuration the machine really reaches is inside its own space bound — and
that is what a caller has to supply. -/

/-- **The step a code takes lands where the space bound says.** -/
theorem clampIn_of_withinSpace {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (a : Code tm.Q kk x.length S) (P : SuccParams tm.Q kk)
    (hq : a.1 = P.q) (hin : P.inSym = inSymOf tm x S a)
    (hwsym : ∀ i, (a.2.2.1 i).2 (a.2.2.1 i).1 = P.wSym i)
    (hosym : a.2.2.2.2 a.2.2.2.1 = P.oSym)
    (hspace : (tm.stepCfg P.beta (decodeCfg x S a)).WithinDecisionSpace x.length S) :
    movedIdx (succTrans tm P).2.2.2.1 a.2.1.val ≤ x.length + S + 1 := by
  have hP : P = paramsOf tm x S a P.beta := params_eq tm x S a P hq hin hwsym hosym
  have hδ := stepCfg_decodeCfg_delta tm x S a P.beta
  rw [← hP] at hδ
  have hhead : (tm.stepCfg P.beta (decodeCfg x S a)).input.head
      = movedIdx (succTrans tm P).2.2.2.1 a.2.1.val := by
    show ((decodeCfg x S a).input.move
      (tm.δ P.beta (decodeCfg x S a).state (decodeCfg x S a).input.read
        (fun i => ((decodeCfg x S a).work i).read) (decodeCfg x S a).output.read).2.2.2.1).head
      = _
    rw [move_head_eq_movedIdx, hδ]
    rfl
  rw [← hhead]
  exact hspace.1.2

/-- **And a code the search has reached steps inside the window.** This is the shape a chained
soundness argument uses: the walk's codes are reachable by induction, and reachable
configurations obey the machine's own space bound, so the step a code takes never leaves the
window that `Complexity.Code` can represent. -/
theorem clampIn_of_mem_reachCodes {kk : ℕ} {tm : NTM kk} (x : List Bool) (S : ℕ)
    (hs : ∀ c, tm.ReachesCfg (tm.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hw : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x S c)
    (a : Code tm.Q kk x.length S) (t : ℕ)
    (ha : a ∈ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) t)
    (P : SuccParams tm.Q kk)
    (hq : a.1 = P.q) (hin : P.inSym = inSymOf tm x S a)
    (hwsym : ∀ i, (a.2.2.1 i).2 (a.2.2.1 i).1 = P.wSym i)
    (hosym : a.2.2.2.2 a.2.2.2.1 = P.oSym) (hne : a.1 ≠ tm.qhalt) :
    movedIdx (succTrans tm P).2.2.2.1 a.2.1.val ≤ x.length + S + 1 := by
  obtain ⟨c, hc, rfl⟩ := (NTM.mem_reachCodes_iff hs hw t a).mp ha
  have hreach := NTM.reachesCfg_of_mem_reachSet tm (tm.initCfg x) t hc
  have hdec : decodeCfg x S (cfgCode x.length S c) = c :=
    decodeCfg_cfgCode (hw c hreach) (hs c hreach)
  refine clampIn_of_withinSpace tm x S _ P hq hin hwsym hosym ?_
  rw [hdec]
  refine hs _ (Relation.ReflTransGen.tail hreach ⟨?_, P.beta, rfl⟩)
  rw [← hdec] at hne
  exact hne

/-- **Every code of a verified walk is reachable in as many rounds as it took.** -/
theorem mem_reachCodes_of_prefix {kk : ℕ} {tm : NTM kk} (x : List Bool) (S : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) (N : ℕ)
    (h0 : f 0 = cfgCode x.length S (tm.initCfg x))
    (hstep : ∀ s, s < N → f (s + 1) = f s ∨ f (s + 1) ∈ NTM.codeSucc tm x S (f s)) :
    ∀ s, s ≤ N → f s ∈ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) s :=
  fun s hs =>
    mem_reachCodes_of_walk tm x S (cfgCode x.length S (tm.initCfg x)) s f h0
      (fun p hp => hstep p (by omega))

/-- **And so the clamp holds at every stage of a verified walk.** This is the induction the
machine-level soundness runs: the steps taken so far make the current code reachable, and a
reachable code steps inside the window. -/
theorem clampIn_of_prefix {kk : ℕ} {tm : NTM kk} (x : List Bool) (S : ℕ)
    (hs : ∀ c, tm.ReachesCfg (tm.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hw : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x S c)
    (f : ℕ → Code tm.Q kk x.length S) (N : ℕ)
    (h0 : f 0 = cfgCode x.length S (tm.initCfg x))
    (hstep : ∀ s, s < N → f (s + 1) = f s ∨ f (s + 1) ∈ NTM.codeSucc tm x S (f s))
    (s : ℕ) (hsN : s ≤ N) (P : SuccParams tm.Q kk)
    (hq : (f s).1 = P.q) (hin : P.inSym = inSymOf tm x S (f s))
    (hwsym : ∀ i, ((f s).2.2.1 i).2 ((f s).2.2.1 i).1 = P.wSym i)
    (hosym : (f s).2.2.2.2 (f s).2.2.2.1 = P.oSym) (hne : (f s).1 ≠ tm.qhalt) :
    movedIdx (succTrans tm P).2.2.2.1 (f s).2.1.val ≤ x.length + S + 1 :=
  clampIn_of_mem_reachCodes x S hs hw (f s) s
    (mem_reachCodes_of_prefix x S f N h0 hstep s hsN) P hq hin hwsym hosym hne

/-- **Both readers of the parameter register read the same parameters**, whatever bits it holds.
The soundness form of `Complexity.params_of_holds`: the register is guessed, so it need not carry
a canonical encoding, but both readers decode it and so both get the same value. -/
theorem params_of_holdsBits {kk : ℕ} (tm : NTM kk) (bitsPar : List Bool)
    (hlen : bitsPar.length = (succParamsCodec tm.Q kk).width)
    (colsW : ℕ → Fin 3 → Γ) (colsS : ℕ → Fin 2 → Γ)
    (hW : HoldsBits colsW 0 0 bitsPar) (hS : HoldsBits colsS 0 0 bitsPar) :
    windowParams tm colsW = (succParamsCodec tm.Q kk).dec bitsPar ∧
      paramsOfStateTable tm (stateTable tm colsS)
        = (succParamsCodec tm.Q kk).dec bitsPar := by
  constructor
  · have h := ofTable_of_holdsBits_zero (succParamsCodec tm.Q kk) bitsPar hlen colsW 1
      (succParamsCodec tm.Q kk).width (fun _ => 0) 0 le_rfl (fun _ _ => false) hW
    rw [windowParams, paramsOfTable]
    exact h
  · have h := ofTable_of_holdsBits_zero (succParamsCodec tm.Q kk) bitsPar hlen colsS 2
      (stateWidth tm) (fun t => t) 0 (le_max_left _ _) (fun _ _ => false) hS
    rw [paramsOfStateTable, stateTable]
    exact h

/-! ## The guessed input symbol, read off arbitrary bits

The parameter block as a whole can be non-canonical — a state index or a written symbol may be a
pattern no encoder produces — but its *first two cells* cannot: they are a `Complexity.Γ` in two
bits, and `Γ` has exactly four values. So the input symbol the checks compare against is well
defined whatever the guess wrote. -/

@[simp] theorem gammaBits_gamma_dec (b₁ b₂ : Bool) :
    gammaBits (BitCodec.gamma.dec [b₁, b₂]) = (b₁, b₂) := by
  cases b₁ <;> cases b₂ <;> rfl

theorem inSym_dec {kk : ℕ} (tm : NTM kk) (l : List Bool) :
    ((succParamsCodec tm.Q kk).dec l).inSym = BitCodec.gamma.dec (l.take 2) := rfl

/-- **The parameter register opens with the guessed input symbol**, whatever bits it holds. -/
theorem inSym_cells_bits {kk jj : ℕ} (tm : NTM kk) (cols : ℕ → Fin (jj + 1) → Γ)
    (par : Fin (jj + 1)) (bitsPar : List Bool)
    (hlen : bitsPar.length = (succParamsCodec tm.Q kk).width)
    (h : HoldsBits cols 0 par bitsPar) :
    cols 1 par = Γ.ofBool (gammaBits ((succParamsCodec tm.Q kk).dec bitsPar).inSym).1 ∧
      cols 2 par = Γ.ofBool (gammaBits ((succParamsCodec tm.Q kk).dec bitsPar).inSym).2 := by
  have hw : 2 ≤ bitsPar.length := by
    rw [hlen, succParamsCodec_width]
    omega
  have h0 : (0 : ℕ) < bitsPar.length := by omega
  have h1 : (1 : ℕ) < bitsPar.length := by omega
  have htake : bitsPar.take 2 = [bitsPar[0]'h0, bitsPar[1]'h1] := by
    refine List.ext_getElem (by simp; omega) ?_
    intro i hi hi'
    have hilt : i < 2 := by simpa using hi'
    rw [List.getElem_take]
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · rfl
    · rfl
  rw [inSym_dec, htake, gammaBits_gamma_dec]
  refine ⟨?_, ?_⟩
  · have hc := h 0 h0
    rwa [show 0 + 0 + 1 = 1 by omega] at hc
  · have hc := h 1 h1
    rwa [show 0 + 1 + 1 = 2 by omega] at hc

/-- **The input check pins the guessed input symbol**, whatever bits the register holds. -/
theorem inSym_eq_of_inMatch_bits {kk jj : ℕ} (tm : NTM kk) (cols : ℕ → Fin (jj + 1) → Γ)
    (par : Fin (jj + 1)) (bitsPar : List Bool)
    (hlen : bitsPar.length = (succParamsCodec tm.Q kk).width)
    (h : HoldsBits cols 0 par bitsPar) (g : Γ)
    (hv : TM.inMatchVerdict gammaBits g (cols 1 par) (cols 2 par) = true) :
    ((succParamsCodec tm.Q kk).dec bitsPar).inSym = g := by
  obtain ⟨h1, h2⟩ := inSym_cells_bits tm cols par bitsPar hlen h
  rw [TM.inMatchVerdict, h1, h2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hv
  exact gammaBits_injective (Prod.ext (ofBool_injective hv.1) (ofBool_injective hv.2))

/-- **The parameter register opens with two ones exactly when the guessed symbol is the marker**,
whatever bits it holds. -/
theorem parStart_iff_bits {kk jj : ℕ} (tm : NTM kk) (cols : ℕ → Fin (jj + 1) → Γ)
    (par : Fin (jj + 1)) (bitsPar : List Bool)
    (hlen : bitsPar.length = (succParamsCodec tm.Q kk).width)
    (h : HoldsBits cols 0 par bitsPar) :
    (∀ q, 1 ≤ q → q ≤ 2 → cols q par = Γ.one)
      ↔ ((succParamsCodec tm.Q kk).dec bitsPar).inSym = Γ.start := by
  obtain ⟨h1, h2⟩ := inSym_cells_bits tm cols par bitsPar hlen h
  set P := (succParamsCodec tm.Q kk).dec bitsPar with hP
  constructor
  · intro hall
    have e1 : Γ.ofBool (gammaBits P.inSym).1 = Γ.one := by
      rw [← h1]; exact hall 1 le_rfl (by omega)
    have e2 : Γ.ofBool (gammaBits P.inSym).2 = Γ.one := by
      rw [← h2]; exact hall 2 (by omega) le_rfl
    refine gammaBits_injective (Prod.ext ?_ ?_)
    · cases hb : (gammaBits P.inSym).1 with
      | true => rfl
      | false => rw [hb] at e1; exact absurd e1 (fun hc => Γ.noConfusion hc)
    · cases hb : (gammaBits P.inSym).2 with
      | true => rfl
      | false => rw [hb] at e2; exact absurd e2 (fun hc => Γ.noConfusion hc)
  · intro hst q hq1 hq2
    rcases Nat.lt_or_ge q 2 with hlt | hge
    · rw [show q = 1 by omega, h1, hst]
      rfl
    · rw [show q = 2 by omega, h2, hst]
      rfl

/-- **The input-symbol scan decides the guessed symbol**, whatever bits the parameter register
holds. The soundness form of `Complexity.inSymScanner_decides`. -/
theorem inSymScanner_sound {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (par hd res : Fin (jj + 1)) (bitsPar : List Bool)
    (hlen : bitsPar.length = (succParamsCodec tm.Q kk).width)
    (hpar : HoldsBits cols 0 par bitsPar)
    (a : Code tm.Q kk x.length S) (g : Γ)
    (hhd : HoldsBits cols (succParamsCodec tm.Q kk).width hd
      ((finCodec (x.length + S + 2)).enc a.2.1))
    (hres : cols 1 res = Γ.ofBool (TM.inMatchVerdict gammaBits g (cols 1 par) (cols 2 par)))
    (hg : a.2.1.val ≠ 0 → g = inSymOf tm x S a)
    (hv : (inSymScanner tm x.length S par hd res).emit
      ((inSymScanner tm x.length S par hd res).run cols (walkScanLen tm x.length S)) = true) :
    ((succParamsCodec tm.Q kk).dec bitsPar).inSym = inSymOf tm x S a := by
  rw [inSymScanner, Scanner.or_emit_run] at hv
  rcases hv with h | h
  · rw [Scanner.all_emit_run] at h
    have h0 := h ⟨0, by omega⟩
    have h1 := h ⟨1, by omega⟩
    rw [if_pos (rfl : (0 : ℕ) = 0)] at h0
    rw [if_neg (by exact (by omega : (1 : ℕ) ≠ 0))] at h1
    have hzero : a.2.1.val = 0 :=
      (headZeroScanner_decides tm x.length S hd cols (walkScanLen tm x.length S)
        (headField_le_walkScanLen tm x.length S) a.2.1 hhd).mp h0
    have hstart : ((succParamsCodec tm.Q kk).dec bitsPar).inSym = Γ.start :=
      (parStart_iff_bits tm cols par bitsPar hlen hpar).mp
        ((Scanner.isConst_upTo_run jj par Γ.one cols 2 (walkScanLen tm x.length S)
          (two_le_walkScanLen tm x.length S)).mp h1)
    rw [hstart, inSymOf, hzero]
    exact (Tape.init_cells_zero _).symm
  · rw [Scanner.all_emit_run] at h
    have h0 := h ⟨0, by omega⟩
    have h1 := h ⟨1, by omega⟩
    rw [if_pos (rfl : (0 : ℕ) = 0)] at h0
    rw [if_neg (by exact (by omega : (1 : ℕ) ≠ 0))] at h1
    have hne : a.2.1.val ≠ 0 :=
      (headNonZeroScanner_decides tm x.length S hd cols (walkScanLen tm x.length S)
        (headField_le_walkScanLen tm x.length S) a.2.1 hhd).mp h0
    have hone : cols 1 res = Γ.one :=
      (Scanner.isConst_cell jj res Γ.one cols (walkScanLen tm x.length S)
        (by have := two_le_walkScanLen tm x.length S; omega)).mp h1
    have hverdict : TM.inMatchVerdict gammaBits g (cols 1 par) (cols 2 par) = true := by
      rw [hres] at hone
      cases hc : TM.inMatchVerdict gammaBits g (cols 1 par) (cols 2 par) with
      | false => rw [hc] at hone; exact absurd hone (fun hz => Γ.noConfusion hz)
      | true => rfl
    rw [inSym_eq_of_inMatch_bits tm cols par bitsPar hlen hpar g hverdict]
    exact hg hne

/-- **The direction checker decides the guessed direction**, whatever bits the parameter register
holds. -/
theorem dirScanner_sound {kk : ℕ} (tm : NTM kk) (enc : Dir3 → Γ) (cols : ℕ → Fin 2 → Γ)
    (bitsPar : List Bool) (hlen : bitsPar.length = (succParamsCodec tm.Q kk).width)
    (hpar : HoldsBits cols 0 0 bitsPar) :
    (dirScanner tm enc).emit
        ((dirScanner tm enc).run cols (succParamsCodec tm.Q kk).width) = true ↔
      cols 1 1 = enc (succTrans tm ((succParamsCodec tm.Q kk).dec bitsPar)).2.2.2.1 := by
  have hP : dirParams tm cols = (succParamsCodec tm.Q kk).dec bitsPar := by
    have h := ofTable_of_holdsBits_zero (succParamsCodec tm.Q kk) bitsPar hlen cols 1
      (succParamsCodec tm.Q kk).width (fun _ => 0) 0 le_rfl (fun _ _ => false) hpar
    rw [dirParams, paramsOfTable]
    exact h
  rw [dirScanner_run, hP, decide_eq_true_eq]

/-- **The direction check pins the register to the direction the machine must take**, whatever
bits the parameter register holds. -/
theorem dirCheckScanner_sound {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (par mv dr hdOld hdNew : Fin (jj + 1)) (dc : DirCodec)
    (bitsPar : List Bool) (hlenPar : bitsPar.length = (succParamsCodec tm.Q kk).width)
    (hpar : HoldsBits cols 0 par bitsPar) (a b : Code tm.Q kk x.length S)
    (hhdOld : HoldsBits cols (succParamsCodec tm.Q kk).width hdOld
      ((finCodec (x.length + S + 2)).enc a.2.1))
    (hhdNew : HoldsBits cols (succParamsCodec tm.Q kk).width hdNew
      ((finCodec (x.length + S + 2)).enc b.2.1))
    (hmove : b.2.1.val
      = movedIdx (succTrans tm ((succParamsCodec tm.Q kk).dec bitsPar)).2.2.2.1 a.2.1.val)
    (hv : (dirCheckScanner tm x.length S par mv dr hdOld hdNew dc).emit
      ((dirCheckScanner tm x.length S par mv dr hdOld hdNew dc).run cols
        (walkScanLen tm x.length S)) = true) :
    cols 1 mv = dc.encMove (adjustedDir
        (succTrans tm ((succParamsCodec tm.Q kk).dec bitsPar)).2.2.2.1 a.2.1.val) ∧
      cols 1 dr = dc.enc (adjustedDir
        (succTrans tm ((succParamsCodec tm.Q kk).dec bitsPar)).2.2.2.1 a.2.1.val) := by
  set P := (succParamsCodec tm.Q kk).dec bitsPar with hPdef
  have hzO := headZeroScanner_decides tm x.length S hdOld cols (walkScanLen tm x.length S)
    (headField_le_walkScanLen tm x.length S) a.2.1 hhdOld
  have hzN := headZeroScanner_decides tm x.length S hdNew cols (walkScanLen tm x.length S)
    (headField_le_walkScanLen tm x.length S) b.2.1 hhdNew
  have hnO := headNonZeroScanner_decides tm x.length S hdOld cols (walkScanLen tm x.length S)
    (headField_le_walkScanLen tm x.length S) a.2.1 hhdOld
  have hnN := headNonZeroScanner_decides tm x.length S hdNew cols (walkScanLen tm x.length S)
    (headField_le_walkScanLen tm x.length S) b.2.1 hhdNew
  rw [dirCheckScanner, Scanner.or_emit_run] at hv
  have hlen2 : 1 ≤ walkScanLen tm x.length S := by
    have := two_le_walkScanLen tm x.length S
    omega
  rcases hv with h | h
  · rw [Scanner.all_emit_run] at h
    have h0 := h ⟨0, by omega⟩
    have h1 := h ⟨1, by omega⟩
    have h2 := h ⟨2, by omega⟩
    rw [if_pos (rfl : (0 : ℕ) = 0), Scanner.or_emit_run] at h0
    rw [if_neg (by exact (by omega : (1 : ℕ) ≠ 0)), if_pos (rfl : (1 : ℕ) = 1)] at h1
    rw [if_neg (by exact (by omega : (2 : ℕ) ≠ 0)),
      if_neg (by exact (by omega : (2 : ℕ) ≠ 1))] at h2
    have hstay : adjustedDir (succTrans tm P).2.2.2.1 a.2.1.val = Dir3.stay := by
      rw [adjustedDir]
      rcases h0 with hz | hz
      · rw [if_pos (hzO.mp hz)]
      · by_cases ha : a.2.1.val = 0
        · rw [if_pos ha]
        · rw [if_neg ha, if_pos (by rw [← hmove]; exact hzN.mp hz)]
    rw [hstay]
    exact ⟨(Scanner.isConst_cell jj mv (dc.encMove Dir3.stay) cols
        (walkScanLen tm x.length S) hlen2).mp h1,
      (Scanner.isConst_cell jj dr (dc.enc Dir3.stay) cols
        (walkScanLen tm x.length S) hlen2).mp h2⟩
  · rw [Scanner.all_emit_run] at h
    have h0 := h ⟨0, by omega⟩
    have h1 := h ⟨1, by omega⟩
    have h2 := h ⟨2, by omega⟩
    have h3 := h ⟨3, by omega⟩
    rw [if_pos (rfl : (0 : ℕ) = 0)] at h0
    rw [if_neg (by exact (by omega : (1 : ℕ) ≠ 0)), if_pos (rfl : (1 : ℕ) = 1)] at h1
    rw [if_neg (by exact (by omega : (2 : ℕ) ≠ 0)),
      if_neg (by exact (by omega : (2 : ℕ) ≠ 1)), if_pos (rfl : (2 : ℕ) = 2),
      Scanner.upTo_emit_run _ (Scanner.rightOnly_comap (fun _ _ => rfl) (dirCols par mv))
        _ _ (succParamsCodec_width_le_walkScanLen tm x.length S),
      Scanner.comap_emit, Scanner.comap_run] at h2
    rw [if_neg (by exact (by omega : (3 : ℕ) ≠ 0)),
      if_neg (by exact (by omega : (3 : ℕ) ≠ 1)),
      if_neg (by exact (by omega : (3 : ℕ) ≠ 2)),
      Scanner.upTo_emit_run _ (Scanner.rightOnly_comap (fun _ _ => rfl) (dirCols par dr))
        _ _ (succParamsCodec_width_le_walkScanLen tm x.length S),
      Scanner.comap_emit, Scanner.comap_run] at h3
    have hdir : adjustedDir (succTrans tm P).2.2.2.1 a.2.1.val = (succTrans tm P).2.2.2.1 := by
      rw [adjustedDir, if_neg (hnO.mp h0), if_neg (by rw [← hmove]; exact hnN.mp h1)]
    rw [hdir]
    exact ⟨(dirScanner_sound tm dc.encMove (fun q c => cols q (dirCols par mv c)) bitsPar
        hlenPar hpar).mp h2,
      (dirScanner_sound tm dc.enc (fun q c => cols q (dirCols par dr c)) bitsPar
        hlenPar hpar).mp h3⟩

/-! ## The successor scan, in the soundness direction -/

/-- **An accepting successor scan exhibits the code it accepted.** The old tuple is a code — the
walk's invariant says so — but the new one is whatever the guess wrote, and nothing hands us a
code for it. The window fields are recovered from the marker count, the state field from the
canonicity conjunct `Complexity.stateScanner` now checks, and the input-head field from the fact
that a block of bits *is* the encoding of its value. The one thing still assumed is that the new
head is inside the window: unlike the window fields, which carry their bound in the marker, a
binary field's range has to be checked against a register that holds the bound — see
`Complexity.Scanner.le`. -/
theorem succScanner_sound {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (par : Fin (jj + 1)) (Ra Rb : CodeRegs kk jj)
    (a : Code tm.Q kk x.length S) (P : SuccParams tm.Q kk) (bs bh bitsPar : List Bool)
    (hlenPar : bitsPar.length = (succParamsCodec tm.Q kk).width)
    (hpar : HoldsBits cols 0 par bitsPar)
    (hPdec : (succParamsCodec tm.Q kk).dec bitsPar = P)
    (ha : HoldsCodeScan tm x S cols Ra a)
    (hbsLen : bs.length = (qCodec tm.Q).width) (hbs : HoldsBits cols 0 Rb.st bs)
    (hbhLen : bh.length = (finCodec (x.length + S + 2)).width)
    (hbh : HoldsBits cols (succParamsCodec tm.Q kk).width Rb.hd bh)
    (hclampIn : a.1 ≠ tm.qhalt → a.1 = P.q → P.inSym = inSymOf tm x S a →
      (∀ i, (a.2.2.1 i).2 (a.2.2.1 i).1 = P.wSym i) → a.2.2.2.2 a.2.2.2.1 = P.oSym →
      movedIdx (succTrans tm P).2.2.2.1 a.2.1.val ≤ x.length + S + 1)
    (hbitW : ∀ i : Fin kk, ∀ q, q < (S + 1) * 3 →
      cols ((succParamsCodec tm.Q kk).width + q + 1) (Rb.wk i) = Γ.zero ∨
      cols ((succParamsCodec tm.Q kk).width + q + 1) (Rb.wk i) = Γ.one)
    (hbitO : ∀ q, q < (S + 2) * 3 →
      cols ((succParamsCodec tm.Q kk).width + q + 1) Rb.ot = Γ.zero ∨
      cols ((succParamsCodec tm.Q kk).width + q + 1) Rb.ot = Γ.one)
    (hne : a.1 ≠ tm.qhalt)
    (hendW : ∀ i, markOf (fun q c => cols q (windowCols par Ra Rb i c))
      (succParamsCodec tm.Q kk).width 1 (S + 1) = false)
    (hendO : markOf (fun q c => cols q (outputCols par Ra Rb c))
      (succParamsCodec tm.Q kk).width 1 (S + 2) = false)
    (hin : P.inSym = inSymOf tm x S a)
    (hv : (succScanner tm x.length S par Ra Rb).emit
      ((succScanner tm x.length S par Ra Rb).run cols (walkScanLen tm x.length S)) = true) :
    ∃ b : Code tm.Q kk x.length S, HoldsCodeScan tm x S cols Rb b ∧
      b = succCode tm x S P.beta a ∧
      b.2.1.val = movedIdx (succTrans tm P).2.2.2.1 a.2.1.val := by
  classical
  obtain ⟨vwork, vout, vhead, vsta, vstb⟩ :=
    succScanner_verdicts tm x.length S par Ra Rb cols hv
  have hleft : (succTrans tm P).2.2.2.1 = Dir3.left → 0 < a.2.1.val := by
    intro hd
    by_contra hzero
    have h0 : a.2.1.val = 0 := by omega
    have hstart : P.inSym = Γ.start := by
      rw [hin, inSymOf, h0]
      exact Tape.init_cells_zero _
    have hright := (tm.δ_right_of_start P.beta P.q P.inSym P.wSym P.oSym).1 hstart
    rw [succTrans] at hd
    rw [hd] at hright
    exact Dir3.noConfusion hright
  obtain ⟨hast, hahd, hawk, haot⟩ := ha
  have hPo : windowParams tm (fun q c => cols q (outputCols par Ra Rb c)) = P := by
    rw [← hPdec]
    exact (params_of_holdsBits tm bitsPar hlenPar (fun q c => cols q (outputCols par Ra Rb c))
      (fun q c => cols q (stateCols par Ra c)) hpar hpar).1
  have hPsa : paramsOfStateTable tm
      (stateTable tm (fun q c => cols q (stateCols par Ra c))) = P := by
    rw [← hPdec]
    exact (params_of_holdsBits tm bitsPar hlenPar (fun q c => cols q (outputCols par Ra Rb c))
      (fun q c => cols q (stateCols par Ra c)) hpar hpar).2
  have hPsb : paramsOfStateTable tm
      (stateTable tm (fun q c => cols q (stateCols par Rb c))) = P := by
    rw [← hPdec]
    exact (params_of_holdsBits tm bitsPar hlenPar (fun q c => cols q (outputCols par Ra Rb c))
      (fun q c => cols q (stateCols par Rb c)) hpar hpar).2
  have hpar' : windowParams tm (fun q c => cols q (headCols par Ra Rb c)) = P := by
    rw [windowParams_congr tm (fun q c => cols q (headCols par Ra Rb c))
      (fun q c => cols q (outputCols par Ra Rb c)) (fun _ => rfl)]
    exact hPo
  have hq : a.1 = P.q := by
    have h := (stateScanner_decides tm false (fun q c => cols q (stateCols par Ra c)) a.1
      hast (Or.inr hne)).mp vsta
    rwa [hPsa, if_neg (by simp)] at h
  obtain ⟨hbstEq, hbcanon, -⟩ :=
    stateScanner_sound tm true (fun q c => cols q (stateCols par Rb c)) bs hbsLen hbs vstb
  rw [hPsb, if_pos rfl] at hbstEq
  have hencA : binValLE ((finCodec (x.length + S + 2)).enc a.2.1) = a.2.1.val := by
    show binValLE (bitsOfLenLE (bitWidth (x.length + S + 2)) a.2.1.val) = _
    exact binValLE_bitsOfLenLE _ _ (lt_of_lt_of_le a.2.1.isLt (le_two_pow_bitWidth _))
  have hheadEq := headScanner_sound tm (fun q c => cols q (headCols par Ra Rb c))
    (bitWidth (x.length + S + 2)) ((finCodec (x.length + S + 2)).enc a.2.1) bh
    ((finCodec (x.length + S + 2)).enc_length _) hbhLen hahd.shift hbh.shift
    (by rw [hpar', hencA]; exact hleft) vhead
  rw [hpar', hencA] at hheadEq
  have hwin : ∀ i : Fin kk, ∃ (hd' : Fin (S + 1)) (cl' : Fin (S + 1) → Γ),
      HoldsWindow (fun q c => cols q (windowCols par Ra Rb i c))
        (succParamsCodec tm.Q kk).width 2 hd' cl' ∧
      (a.2.2.1 i).2 (a.2.2.1 i).1 = P.wSym i ∧
      (∀ p, cl' p = if p = (a.2.2.1 i).1 ∧ 0 < p.val then succWrite tm P i
        else (a.2.2.1 i).2 p) ∧
      hd'.val = movedIdx (succDir tm P i) (a.2.2.1 i).1.val := by
    intro i
    have hcong : windowParams tm (fun q c => cols q (windowCols par Ra Rb i c)) = P := by
      rw [windowParams_congr tm (fun q c => cols q (windowCols par Ra Rb i c))
        (fun q c => cols q (outputCols par Ra Rb c)) (fun _ => rfl)]
      exact hPo
    obtain ⟨hd', cl', hw', h1, h2, h3⟩ := windowScanner_sound tm i
      (fun q c => cols q (windowCols par Ra Rb i c)) S (a.2.2.1 i).1 (a.2.2.1 i).2 (hawk i)
      (hbitW i) (hendW i) (vwork i)
    rw [hcong] at h1 h2 h3
    exact ⟨hd', cl', hw', h1, h2, h3⟩
  choose hdW clW hwW hsymW hcellW hmovW using hwin
  obtain ⟨hdO, clO, hwO, hsymO, hcellO, hmovO⟩ := outputScanner_sound tm
    (fun q c => cols q (outputCols par Ra Rb c)) S a.2.2.2.1 a.2.2.2.2 haot hbitO hendO vout
  rw [hPo] at hsymO hcellO hmovO
  have hbound : binValLE bh < x.length + S + 2 := by
    rw [hheadEq]
    have := hclampIn hne hq hin (fun i => hsymW i) hsymO
    omega
  refine ⟨((qCodec tm.Q).dec bs, ⟨binValLE bh, hbound⟩, fun i => (hdW i, clW i), (hdO, clO)),
    ⟨?_, ?_, fun i => hwW i, hwO⟩, ?_, hheadEq⟩
  · show HoldsBits cols 0 Rb.st ((qCodec tm.Q).enc ((qCodec tm.Q).dec bs))
    rw [hbcanon]
    exact hbs
  · show HoldsBits cols (succParamsCodec tm.Q kk).width Rb.hd
      ((finCodec (x.length + S + 2)).enc ⟨binValLE bh, hbound⟩)
    rw [show (finCodec (x.length + S + 2)).enc ⟨binValLE bh, hbound⟩ = bh from
      bitsOfLenLE_self bh hbhLen]
    exact hbh
  · refine eq_succCode_of_checks' tm x S a _ P hq hin (fun i => hsymW i) hsymO ?_ ?_ ?_
      hbstEq hheadEq (fun i => ⟨hmovW i, hcellW i⟩) ⟨hmovO, hcellO⟩
    · exact hclampIn hne hq hin (fun i => hsymW i) hsymO
    · intro i
      rw [← hmovW i]
      exact Nat.lt_succ_iff.mp (hdW i).isLt
    · rw [← hmovO]
      exact Nat.lt_succ_iff.mp hdO.isLt

/-- **The deferred clamp, discharged from reachability.** This is what a caller of
`Complexity.walkStepScanner_sound` supplies: the code the step starts from is one the search has
reached, and a reachable code steps inside the window. The antecedents are exactly the facts the
scan itself establishes, so the caller need not know them in advance. -/
theorem clampIn_deferred {kk : ℕ} {tm : NTM kk} (x : List Bool) (S : ℕ)
    (hs : ∀ c, tm.ReachesCfg (tm.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hw : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x S c)
    (a : Code tm.Q kk x.length S) (t : ℕ)
    (ha : a ∈ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) t)
    (P : SuccParams tm.Q kk) :
    a.1 ≠ tm.qhalt → a.1 = P.q → P.inSym = inSymOf tm x S a →
      (∀ i, (a.2.2.1 i).2 (a.2.2.1 i).1 = P.wSym i) → a.2.2.2.2 a.2.2.2.1 = P.oSym →
      movedIdx (succTrans tm P).2.2.2.1 a.2.1.val ≤ x.length + S + 1 :=
  fun hne hq hin hwsym hosym =>
    clampIn_of_mem_reachCodes x S hs hw a t ha P hq hin hwsym hosym hne

/-! ## What a guess actually writes

In the soundness direction there is no certificate: the guess stream is whatever the
nondeterminism chose. But that is still a certificate — of itself — so the same machinery says
what each register ends up holding. -/

/-- The certificate a guess stream is, read as one. -/
noncomputable def streamCert (w : ℕ → ℕ) (t : ℕ) (g : ℕ → Bool) : ℕ → ℕ → ℕ → Bool :=
  fun s p q => g (s * TM.guessOffset w t + (TM.guessOffset w p + q))

theorem stageBlocks_streamCert (w : ℕ → ℕ) (t : ℕ) (g : ℕ → Bool) :
    TM.StageBlocks w t (streamCert w t g) g := fun _ _ _ _ _ => rfl

/-- **The registers a step guesses into hold blocks of the stream's own bits.** -/
theorem exists_bits_guessed {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (second : Bool) (g : ℕ → Bool) (s : ℕ)
    (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.stepBlocks → (W (stepReg L second p)).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks + q))
      (W (Fin.last (jj + 2 + r))))
    (cB : ℕ → Fin (jj + 1))
    (hcB : ∀ p, p < kk + 3 →
      (stepReg L second (L.toWalkLayout.scratch + p) : Fin (jj + 2 + r + 1)) = walkReg (cB p)) :
    ∃ bits : ℕ → List Bool,
      (∀ p, p < kk + 3 → (bits p).length = blockLen tm x.length S p) ∧
      ∀ p, p < kk + 3 →
        HoldsBits (fun q i => stepCells L second W i q) 0 (cB p) (bits p) := by
  classical
  refine ⟨fun p => (List.ofFn fun q : Fin (stepWidth L (L.toWalkLayout.scratch + p) + 1) =>
      streamCert (stepWidth L) L.toWalkLayout.stepBlocks g s
        (L.toWalkLayout.scratch + p) q.val).take (blockLen tm x.length S p),
    fun p hp => ?_, fun p hp => ?_⟩
  · rw [List.length_take, List.length_ofFn, stepWidth_code L p hp]
    have := blockLen_le_codeWidthScan tm x.length S p
    omega
  · have h := holdsBits_block_of_step x L second
      (streamCert (stepWidth L) L.toWalkLayout.stepBlocks g)
      g (stageBlocks_streamCert _ _ _) s W hinv hh hr1 hgf (L.toWalkLayout.scratch + p)
      (by rw [WalkLayout.stepBlocks]; omega)
      (List.ofFn fun q : Fin (stepWidth L (L.toWalkLayout.scratch + p) + 1) =>
        streamCert (stepWidth L) L.toWalkLayout.stepBlocks g s
          (L.toWalkLayout.scratch + p) q.val)
      (fun q hq => by
        rw [List.getElem_ofFn])
      (by rw [List.length_ofFn])
    rw [hcB p hp] at h
    exact h.of_isPrefix (List.take_prefix _ _)

/-- **And so does every scratch register**, at whatever width the check reads it. -/
theorem exists_bits_scratch {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (second : Bool) (g : ℕ → Bool) (s : ℕ)
    (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.stepBlocks → (W (stepReg L second p)).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks + q))
      (W (Fin.last (jj + 2 + r))))
    (p : ℕ) (hp : p < L.toWalkLayout.scratch) (n : ℕ) (hn : n ≤ stepWidth L p + 1) :
    ∃ bits : List Bool, bits.length = n ∧
      HoldsBits (fun q i => stepCells L second W i q) 0 (L.toWalkLayout.reg p) bits := by
  classical
  refine ⟨(List.ofFn fun q : Fin (stepWidth L p + 1) =>
      streamCert (stepWidth L) L.toWalkLayout.stepBlocks g s p q.val).take n, ?_, ?_⟩
  · rw [List.length_take, List.length_ofFn]
    omega
  · have h := holdsBits_block_of_step x L second
      (streamCert (stepWidth L) L.toWalkLayout.stepBlocks g)
      g (stageBlocks_streamCert _ _ _) s W hinv hh hr1 hgf p
      (by rw [WalkLayout.stepBlocks]; omega)
      (List.ofFn fun q : Fin (stepWidth L p + 1) =>
        streamCert (stepWidth L) L.toWalkLayout.stepBlocks g s p q.val)
      (fun q hq => by rw [List.getElem_ofFn]) (by rw [List.length_ofFn])
    rw [stepReg_scratch L second p hp] at h
    exact h.of_isPrefix (List.take_prefix _ _)

/-- **The scan is well formed whatever the guess wrote.** The ruler register is guessed like any
other, so a bad guess could in principle shorten the scan — but a guess writes `Γ.ofBool` of its
stream, never a blank, and the invariant says the cell just past the ruler was blank to begin
with. So the scan runs for exactly `Complexity.walkScanLen` cells on every guess. -/
theorem scanTape_of_step_any {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (second : Bool) (g : ℕ → Bool) (s : ℕ)
    (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.stepBlocks → (W (stepReg L second p)).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks + q))
      (W (Fin.last (jj + 2 + r))))
    (hblank : (W (walkReg (L.toWalkLayout.reg L.toWalkLayout.rulerIdx))).cells
      (walkScanLen tm x.length S + 1) = Γ.blank) :
    TM.ScanTape (stepCells L second W) (walkScanLen tm x.length S) := by
  classical
  have hlt : L.toWalkLayout.rulerIdx < L.toWalkLayout.stepBlocks := by
    rw [WalkLayout.stepBlocks]
    have := L.toWalkLayout.ruler_scratch
    omega
  obtain ⟨ginv, -, -, -, -⟩ := TM.guessBlocksTapes_spec (stepReg L second)
    (fun p => walkReg_ne_last _) (stepWidth L) L.toWalkLayout.stepBlocks W hinv hh
    (stepReg_inj L second)
  obtain ⟨bits, hlen, hbits⟩ := exists_bits_scratch x L second g s W hinv hh hr1 hgf
    L.toWalkLayout.rulerIdx L.toWalkLayout.ruler_scratch (walkScanLen tm x.length S)
    (by rw [stepWidth_scratch L _ L.toWalkLayout.ruler_scratch, L.width_ruler]
        have := one_le_walkScanLen tm x.length S
        omega)
  refine ⟨fun i => (ginv (walkReg i)).1, fun i q hq => (ginv (walkReg i)).2 q hq,
    fun q h1 h2 => ?_, ?_⟩
  · rw [← L.toWalkLayout.ruler_zero]
    have hc := hbits (q - 1) (by rw [hlen]; omega)
    rw [show 0 + (q - 1) + 1 = q by omega] at hc
    have hc' : stepCells L second W (L.toWalkLayout.reg L.toWalkLayout.rulerIdx) q
        = Γ.ofBool (bits[q - 1]'(by rw [hlen]; omega)) := hc
    show stepCells L second W (L.toWalkLayout.reg L.toWalkLayout.rulerIdx) q ≠ Γ.blank
    rw [hc']
    cases bits[q - 1]'(by rw [hlen]; omega) <;> exact fun hz => Γ.noConfusion hz
  · have hbeyond := TM.guessBlocksTapes_beyond (stepReg L second) (fun p => walkReg_ne_last _)
      (stepWidth L) L.toWalkLayout.stepBlocks W hinv hh
      (fun p q hp hq hpq => L.toWalkLayout.stepIdx_inj second p q hp hq
        (L.toWalkLayout.reg_inj _ _ (L.toWalkLayout.stepIdx_lt second p hp)
          (L.toWalkLayout.stepIdx_lt second q hq) (walkReg_inj hpq)))
      L.toWalkLayout.rulerIdx hlt (walkScanLen tm x.length S + 1) ?_
    · rw [← L.toWalkLayout.ruler_zero]
      show (TM.guessBlocksTapes (stepReg L second) (stepWidth L) L.toWalkLayout.stepBlocks W
        (walkReg (L.toWalkLayout.reg L.toWalkLayout.rulerIdx))).cells _ = _
      rw [← stepReg_scratch L second _ L.toWalkLayout.ruler_scratch, hbeyond,
        stepReg_scratch L second _ L.toWalkLayout.ruler_scratch, hblank]
    · rw [hr1 _ hlt, stepWidth_scratch L _ L.toWalkLayout.ruler_scratch, L.width_ruler]
      have := one_le_walkScanLen tm x.length S
      omega

/-! ## One walk step, in the soundness direction -/

/-- **What a chained soundness argument carries about a register tuple**: it holds a code, and
the cell past each window is a zero — which is what the next step's window checks read as "no
head marker here". A tuple written from a code has both; so does one a step has verified. -/
def HoldsCodeTail {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ) {jj : ℕ}
    (cols : ℕ → Fin (jj + 1) → Γ) (j : ℕ → Fin (jj + 1)) (a : Code tm.Q kk x.length S) : Prop :=
  HoldsCodeScan tm x S cols (codeRegsOf j) a ∧
    ∀ i : Fin (kk + 2), cols (blockLen tm x.length S (i.val + 1)) (j (i.val + 1)) = Γ.zero

/-- **A tuple written from a code has both halves.** -/
theorem holdsCodeTail_of_blocks {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (j : ℕ → Fin (jj + 1)) (a : Code tm.Q kk x.length S)
    (ha : ∀ p, p < kk + 3 → HoldsBits cols 0 (j p) (codeBlockScan tm x S a p)) :
    HoldsCodeTail tm x S cols j a := by
  refine ⟨holdsCodeScan_of_blocks tm x S cols j a ha, fun i => ?_⟩
  have hone := one_le_blockLen tm x.length S (i.val + 1) (by omega)
  have hlen : (codeBlockScan tm x S a (i.val + 1)).length
      = blockLen tm x.length S (i.val + 1) := codeBlockScan_length tm x S a _
  have hc := ha (i.val + 1) (by omega) (blockLen tm x.length S (i.val + 1) - 1) (by omega)
  rw [codeBlockScan_tail tm x S a (i.val + 1) (by omega) (by omega)] at hc
  rw [show blockLen tm x.length S (i.val + 1)
    = 0 + (blockLen tm x.length S (i.val + 1) - 1) + 1 by omega]
  exact hc

/-- **The successor branch of a walk-step scan, on its own.** The four checks that make up the
branch pin the new tuple to *the* successor the guessed choice bit names — which is what a
certificate that a code is not a successor needs, since it has to rule out both. -/
theorem succBranch_sound {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (par mv dr res : Fin (jj + 1)) (dc : DirCodec)
    (j j' : ℕ → Fin (jj + 1)) (a : Code tm.Q kk x.length S) (P : SuccParams tm.Q kk) (g : Γ)
    (bitsPar : List Bool) (hlenPar : bitsPar.length = (succParamsCodec tm.Q kk).width)
    (hpar : HoldsBits cols 0 par bitsPar)
    (hPdec : (succParamsCodec tm.Q kk).dec bitsPar = P)
    (ha : HoldsCodeTail tm x S cols j a)
    (bits : ℕ → List Bool)
    (hbitsLen : ∀ p, p < kk + 3 → (bits p).length = blockLen tm x.length S p)
    (hbits : ∀ p, p < kk + 3 → HoldsBits cols 0 (j' p) (bits p))
    (hclampIn : a.1 ≠ tm.qhalt → a.1 = P.q → P.inSym = inSymOf tm x S a →
      (∀ i, (a.2.2.1 i).2 (a.2.2.1 i).1 = P.wSym i) → a.2.2.2.2 a.2.2.2.1 = P.oSym →
      movedIdx (succTrans tm P).2.2.2.1 a.2.1.val ≤ x.length + S + 1)
    (hres : cols 1 res = Γ.ofBool (TM.inMatchVerdict gammaBits g (cols 1 par) (cols 2 par)))
    (hg : a.2.1.val ≠ 0 → g = inSymOf tm x S a)
    (h0 : (succScanner tm x.length S par (codeRegsOf j) (codeRegsOf j')).emit
      ((succScanner tm x.length S par (codeRegsOf j) (codeRegsOf j')).run cols
        (walkScanLen tm x.length S)) = true)
    (h1 : (dirCheckScanner tm x.length S par mv dr (codeRegsOf (kk := kk) j).hd
        (codeRegsOf (kk := kk) j').hd dc).emit
      ((dirCheckScanner tm x.length S par mv dr (codeRegsOf (kk := kk) j).hd
        (codeRegsOf (kk := kk) j').hd dc).run cols (walkScanLen tm x.length S)) = true)
    (h2 : (inSymScanner tm x.length S par (codeRegsOf (kk := kk) j).hd res).emit
      ((inSymScanner tm x.length S par (codeRegsOf (kk := kk) j).hd res).run cols
        (walkScanLen tm x.length S)) = true)
    (h3 : (tailZeroScanner tm x.length S j').emit
      ((tailZeroScanner tm x.length S j').run cols (walkScanLen tm x.length S)) = true) :
    ∃ b : Code tm.Q kk x.length S, HoldsCodeTail tm x S cols j' b ∧ a.1 ≠ tm.qhalt ∧
      b = succCode tm x S P.beta a ∧
      b.2.1.val = movedIdx (succTrans tm P).2.2.2.1 a.2.1.val ∧
      cols 1 mv = dc.encMove (adjustedDir (succTrans tm P).2.2.2.1 a.2.1.val) ∧
      cols 1 dr = dc.enc (adjustedDir (succTrans tm P).2.2.2.1 a.2.1.val) := by
  classical
  obtain ⟨haCode, haTail⟩ := ha
  have hendW : ∀ i : Fin kk, markOf (fun q c =>
      cols q (windowCols par (codeRegsOf (kk := kk) j) (codeRegsOf (kk := kk) j') i c))
      (succParamsCodec tm.Q kk).width 1 (S + 1) = false := by
    intro i
    have hi := haTail ⟨i.val + 1, by omega⟩
    rw [blockLen_wk tm x.length S (i.val + 2) (by omega) (by omega)] at hi
    show decide (cols ((succParamsCodec tm.Q kk).width + 3 * (S + 1) + 1)
      (j (i.val + 2)) = Γ.one) = false
    rw [show (succParamsCodec tm.Q kk).width + 3 * (S + 1) + 1
      = (succParamsCodec tm.Q kk).width + ((S + 1) * 3 + 1) by omega, hi]
    simp
  have hendO : markOf (fun q c => cols q
      (outputCols par (codeRegsOf (kk := kk) j) (codeRegsOf (kk := kk) j') c))
      (succParamsCodec tm.Q kk).width 1 (S + 2) = false := by
    have hi := haTail ⟨kk + 1, by omega⟩
    rw [blockLen_ot tm x.length S] at hi
    show decide (cols ((succParamsCodec tm.Q kk).width + 3 * (S + 2) + 1)
      (j (kk + 2)) = Γ.one) = false
    rw [show (succParamsCodec tm.Q kk).width + 3 * (S + 2) + 1
      = (succParamsCodec tm.Q kk).width + ((S + 2) * 3 + 1) by omega, hi]
    simp
  have htail := (tailZeroScanner_decides tm x.length S j' cols).mp h3
  obtain ⟨-, -, -, vsta, -⟩ := succScanner_verdicts tm x.length S par (codeRegsOf j)
    (codeRegsOf j') cols h0
  have hne : a.1 ≠ tm.qhalt := by
    obtain ⟨-, -, hhalt⟩ := stateScanner_sound tm false
      (fun q c => cols q (stateCols par (codeRegsOf (kk := kk) j) c)) ((qCodec tm.Q).enc a.1)
      ((qCodec tm.Q).enc_length a.1) haCode.1 vsta
    rcases hhalt with hc | hc
    · exact absurd hc (by simp)
    · rwa [(qCodec tm.Q).dec_enc] at hc
  have hin : P.inSym = inSymOf tm x S a := by
    rw [← hPdec]
    exact inSymScanner_sound tm x S cols par (codeRegsOf j).hd res bitsPar hlenPar hpar a g
      haCode.2.1 hres hg h2
  have hlen0 : (bits 0).length = (qCodec tm.Q).width := by
    rw [hbitsLen 0 (by omega), blockLen_st]
  have hlen1 : (bits 1).length
      = (succParamsCodec tm.Q kk).width + ((finCodec (x.length + S + 2)).width + 1) := by
    rw [hbitsLen 1 (by omega), blockLen_hd]
  obtain ⟨b, hbHolds, hbSucc, hbHead⟩ := succScanner_sound tm x S cols par (codeRegsOf j)
    (codeRegsOf j') a P (bits 0)
    (((bits 1).drop (succParamsCodec tm.Q kk).width).take (finCodec (x.length + S + 2)).width)
    bitsPar hlenPar hpar hPdec haCode hlen0 (hbits 0 (by omega))
    (holdsBits_slice_length (bits 1) _ _ (by omega))
    (holdsBits_slice (hbits 1 (by omega)) _ _ (by omega)) hclampIn
    (fun i q hq => by
      have hlt : (succParamsCodec tm.Q kk).width + q < (bits (i.val + 2)).length := by
        rw [hbitsLen (i.val + 2) (by omega),
          blockLen_wk tm x.length S (i.val + 2) (by omega) (by omega)]
        omega
      exact cell_bit_of_holdsBits (hbits (i.val + 2) (by omega)) _ hlt)
    (fun q hq => by
      have hlt : (succParamsCodec tm.Q kk).width + q < (bits (kk + 2)).length := by
        rw [hbitsLen (kk + 2) (by omega), blockLen_ot]
        omega
      exact cell_bit_of_holdsBits (hbits (kk + 2) (by omega)) _ hlt)
    hne hendW hendO hin h0
  obtain ⟨hmvc, hdrc⟩ := dirCheckScanner_sound tm x S cols par mv dr (codeRegsOf j).hd
    (codeRegsOf j').hd dc bitsPar hlenPar hpar a b haCode.2.1 hbHolds.2.1
    (by rw [hPdec]; exact hbHead) h1
  rw [hPdec] at hmvc hdrc
  exact ⟨b, ⟨hbHolds, htail⟩, hne, hbSucc, hbHead, hmvc, hdrc⟩

/-- **An accepting walk-step scan exhibits the step it accepted.** The old tuple holds a code and
carries its tail zeros; the new one is a block of guesses, and all that is known of it is that
each register carries bits. Either the scan took the equality branch — and then the new tuple
agrees with the old cell by cell, so it holds the same code — or it took the successor branch,
and `Complexity.succBranch_sound` reads the code back out of it. -/
theorem walkCodeScanner_sound {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (par mv dr res : Fin (jj + 1)) (dc : DirCodec)
    (j j' : ℕ → Fin (jj + 1)) (a : Code tm.Q kk x.length S) (P : SuccParams tm.Q kk) (g : Γ)
    (bitsPar : List Bool) (hlenPar : bitsPar.length = (succParamsCodec tm.Q kk).width)
    (hpar : HoldsBits cols 0 par bitsPar)
    (hPdec : (succParamsCodec tm.Q kk).dec bitsPar = P)
    (ha : HoldsCodeTail tm x S cols j a)
    (bits : ℕ → List Bool)
    (hbitsLen : ∀ p, p < kk + 3 → (bits p).length = blockLen tm x.length S p)
    (hbits : ∀ p, p < kk + 3 → HoldsBits cols 0 (j' p) (bits p))
    (hclampIn : a.1 ≠ tm.qhalt → a.1 = P.q → P.inSym = inSymOf tm x S a →
      (∀ i, (a.2.2.1 i).2 (a.2.2.1 i).1 = P.wSym i) → a.2.2.2.2 a.2.2.2.1 = P.oSym →
      movedIdx (succTrans tm P).2.2.2.1 a.2.1.val ≤ x.length + S + 1)
    (hres : cols 1 res = Γ.ofBool (TM.inMatchVerdict gammaBits g (cols 1 par) (cols 2 par)))
    (hg : a.2.1.val ≠ 0 → g = inSymOf tm x S a)
    (hv : (walkCodeScanner tm x.length S par mv dr res dc j j').emit
      ((walkCodeScanner tm x.length S par mv dr res dc j j').run cols
        (walkScanLen tm x.length S)) = true) :
    ∃ b : Code tm.Q kk x.length S, HoldsCodeTail tm x S cols j' b ∧
      ((b = a ∧ cols 1 mv = dc.encMove Dir3.stay ∧ cols 1 dr = dc.enc Dir3.stay) ∨
        (b ∈ NTM.codeSucc tm x S a ∧
          b.2.1.val = movedIdx (succTrans tm P).2.2.2.1 a.2.1.val ∧
          cols 1 mv = dc.encMove (adjustedDir (succTrans tm P).2.2.2.1 a.2.1.val) ∧
          cols 1 dr = dc.enc (adjustedDir (succTrans tm P).2.2.2.1 a.2.1.val))) := by
  classical
  obtain ⟨haCode, haTail⟩ := ha
  rw [walkCodeScanner, Scanner.or_emit_run] at hv
  rcases hv with h | h
  · rw [Scanner.all_emit_run] at h
    have h0 := h ⟨0, by omega⟩
    have h1 := h ⟨1, by omega⟩
    have h2 := h ⟨2, by omega⟩
    rw [if_pos (rfl : (0 : ℕ) = 0)] at h0
    rw [if_neg (by exact (by omega : (1 : ℕ) ≠ 0)), if_pos (rfl : (1 : ℕ) = 1)] at h1
    rw [if_neg (by exact (by omega : (2 : ℕ) ≠ 0)),
      if_neg (by exact (by omega : (2 : ℕ) ≠ 1))] at h2
    have hagree := eqScanner_agree tm x.length S cols j j' h0
    obtain ⟨hst, hhd, hwk, hot⟩ := haCode
    refine ⟨a, ⟨⟨?_, ?_, fun i => ?_, ?_⟩, fun i => ?_⟩, Or.inl ⟨rfl, ?_, ?_⟩⟩
    · exact holdsBits_transfer hst
        (by rw [(qCodec tm.Q).enc_length, blockLen_st]; omega) (hagree 0 (by omega))
    · exact holdsBits_transfer hhd
        (by rw [(finCodec (x.length + S + 2)).enc_length, blockLen_hd]; omega)
        (hagree 1 (by omega))
    · exact holdsWindow_transfer (hwk i)
        (by rw [blockLen_wk tm x.length S (i.val + 2) (by omega) (by omega)]; omega)
        (hagree (i.val + 2) (by omega))
    · exact holdsWindow_transfer hot (by rw [blockLen_ot]; omega) (hagree (kk + 2) (by omega))
    · rw [← hagree (i.val + 1) (by omega) _ (one_le_blockLen tm x.length S _ (by omega)) le_rfl]
      exact haTail i
    · exact (Scanner.isConst_cell jj mv (dc.encMove Dir3.stay) cols (walkScanLen tm x.length S)
        (one_le_walkScanLen tm x.length S)).mp h1
    · exact (Scanner.isConst_cell jj dr (dc.enc Dir3.stay) cols (walkScanLen tm x.length S)
        (one_le_walkScanLen tm x.length S)).mp h2
  · rw [Scanner.all_emit_run] at h
    have h0 := h ⟨0, by omega⟩
    have h1 := h ⟨1, by omega⟩
    have h2 := h ⟨2, by omega⟩
    have h3 := h ⟨3, by omega⟩
    rw [if_pos (rfl : (0 : ℕ) = 0)] at h0
    rw [if_neg (by exact (by omega : (1 : ℕ) ≠ 0)), if_pos (rfl : (1 : ℕ) = 1)] at h1
    rw [if_neg (by exact (by omega : (2 : ℕ) ≠ 0)),
      if_neg (by exact (by omega : (2 : ℕ) ≠ 1)), if_pos (rfl : (2 : ℕ) = 2)] at h2
    rw [if_neg (by exact (by omega : (3 : ℕ) ≠ 0)),
      if_neg (by exact (by omega : (3 : ℕ) ≠ 1)),
      if_neg (by exact (by omega : (3 : ℕ) ≠ 2))] at h3
    obtain ⟨b, hbTail, hne, hbSucc, hbHead, hmvc, hdrc⟩ :=
      succBranch_sound tm x S cols par mv dr res dc j j' a P g bitsPar hlenPar hpar hPdec
        ⟨haCode, haTail⟩ bits hbitsLen hbits hclampIn hres hg h0 h1 h2 h3
    exact ⟨b, hbTail, Or.inr ⟨(mem_codeSucc_iff tm x S a b).mpr ⟨hne, P.beta, hbSucc⟩,
      hbHead, hmvc, hdrc⟩⟩

/-- **The whole step scan, in the soundness direction.** The counter registers are guessed too,
so their values are read off whatever bits they carry — which loses nothing, because a block of
bits is the encoding of its own value. -/
theorem walkStepScanner_sound {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (par mv dr res cntOld cntNew : Fin (jj + 1)) (wc : ℕ)
    (advance : Bool) (dc : DirCodec) (j j' : ℕ → Fin (jj + 1))
    (a : Code tm.Q kk x.length S) (P : SuccParams tm.Q kk) (g : Γ)
    (bitsPar : List Bool) (hlenPar : bitsPar.length = (succParamsCodec tm.Q kk).width)
    (hpar : HoldsBits cols 0 par bitsPar)
    (hPdec : (succParamsCodec tm.Q kk).dec bitsPar = P)
    (ha : HoldsCodeTail tm x S cols j a)
    (bits : ℕ → List Bool)
    (hbitsLen : ∀ p, p < kk + 3 → (bits p).length = blockLen tm x.length S p)
    (hbits : ∀ p, p < kk + 3 → HoldsBits cols 0 (j' p) (bits p))
    (hclampIn : a.1 ≠ tm.qhalt → a.1 = P.q → P.inSym = inSymOf tm x S a →
      (∀ i, (a.2.2.1 i).2 (a.2.2.1 i).1 = P.wSym i) → a.2.2.2.2 a.2.2.2.1 = P.oSym →
      movedIdx (succTrans tm P).2.2.2.1 a.2.1.val ≤ x.length + S + 1)
    (bitsO bitsN : List Bool) (hlenO : bitsO.length = wc) (hlenN : bitsN.length = wc)
    (hO : HoldsBits cols 0 cntOld bitsO) (hN : HoldsBits cols 0 cntNew bitsN)
    (hwc : wc ≤ walkScanLen tm x.length S)
    (hres : cols 1 res = Γ.ofBool (TM.inMatchVerdict gammaBits g (cols 1 par) (cols 2 par)))
    (hg : a.2.1.val ≠ 0 → g = inSymOf tm x S a)
    (hv : (walkStepScanner tm x.length S par mv dr res cntOld cntNew wc advance dc j j').emit
      ((walkStepScanner tm x.length S par mv dr res cntOld cntNew wc advance dc j j').run cols
        (walkScanLen tm x.length S)) = true) :
    (∃ b : Code tm.Q kk x.length S, HoldsCodeTail tm x S cols j' b ∧
      ((b = a ∧ cols 1 mv = dc.encMove Dir3.stay ∧ cols 1 dr = dc.enc Dir3.stay) ∨
        (b ∈ NTM.codeSucc tm x S a ∧
          b.2.1.val = movedIdx (succTrans tm P).2.2.2.1 a.2.1.val ∧
          cols 1 mv = dc.encMove (adjustedDir (succTrans tm P).2.2.2.1 a.2.1.val) ∧
          cols 1 dr = dc.enc (adjustedDir (succTrans tm P).2.2.2.1 a.2.1.val)))) ∧
      (if advance then binValLE bitsN = binValLE bitsO + 1
        else binValLE bitsO = binValLE bitsN) := by
  rw [walkStepScanner, Scanner.all_emit_run] at hv
  have h0 := hv ⟨0, by omega⟩
  have h1 := hv ⟨1, by omega⟩
  rw [if_pos (rfl : (0 : ℕ) = 0)] at h0
  rw [if_neg (by exact (by omega : (1 : ℕ) ≠ 0))] at h1
  refine ⟨walkCodeScanner_sound tm x S cols par mv dr res dc j j' a P g bitsPar hlenPar hpar
    hPdec ha bits hbitsLen hbits hclampIn hres hg h0, ?_⟩
  refine counterStepScanner_decides cntOld cntNew wc (walkScanLen tm x.length S) advance hwc
    cols (binValLE bitsO) (binValLE bitsN) ?_ ?_ ?_ ?_ h1
  · rw [← hlenO]; exact binValLE_lt bitsO
  · rw [← hlenN]; exact binValLE_lt bitsN
  · rw [bitsOfLenLE_self bitsO hlenO]; exact hO
  · rw [bitsOfLenLE_self bitsN hlenN]; exact hN

/-! ## One stage of the machine, in the soundness direction -/

/-- **What holds between the stages of a walk the machine has verified.** Unlike
`Complexity.WalkStepInv`, which pins a code the caller names, this carries the code the registers
turned out to hold, together with the tail zeros the next stage's window checks read. -/
def WalkSoundInv {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (cOld : ℕ → Fin (jj + 1))
    (a : Code tm.Q kk x.length S) (g : ℕ → Bool) (s : ℕ) : TM.TapePred (jj + 2 + r + 1) :=
  fun inp work out =>
    (∀ i, (work i).StartInvariant) ∧ (∀ i, 1 ≤ (work i).head) ∧
    (∀ i : Fin (jj + 2), (work (Fin.castAdd r i).castSucc).head = 1) ∧
    (work (walkReg (L.toWalkLayout.reg L.toWalkLayout.rulerIdx))).cells
      (walkScanLen tm x.length S + 1) = Γ.blank ∧
    HoldsCodeTail tm x S (fun q i => (work (walkReg i)).cells q) cOld a ∧
    inp = ⟨max a.2.1.val 1, (Tape.init (x.map Γ.ofBool)).cells⟩ ∧
    out.StartInvariant ∧ 1 ≤ out.head ∧
    TM.GuessFrom (fun q => g (s * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks + q))
      (work (Fin.last (jj + 2 + r)))

/-- **The stage's move is safe exactly when its scan accepts.** `Complexity.adjustedDir` turns a
leftward move at the marker into a stay, so a verdict of one leaves the machine's own input head
off the marker — which is the side condition `Complexity.walkStepTM_hoareTime` asks for. On a
rejecting guess the direction cells are unconstrained and the head may land on the marker; the
contract then says nothing, which is why the machine-level soundness needs a contract that does
not assume the move was safe. -/
theorem move_ne_start_of_adjusted (x : List Bool) (dcd : DirCodec) (t : Tape) (h : ℕ) (d : Dir3)
    (m gc : Γ) (ht : t.head = max h 1) (hcells : t.cells = (Tape.init (x.map Γ.ofBool)).cells)
    (hm : m = dcd.encMove (adjustedDir d h)) (hg : gc = dcd.enc (adjustedDir d h)) :
    (t.move (dcd.dec m gc)).read ≠ Γ.start := by
  rw [move_of_walkStep dcd t h (movedIdx d h) d m gc ht hm hg rfl]
  show t.cells (max (movedIdx d h) 1) ≠ Γ.start
  rw [hcells]
  exact Tape.init_ofBool_cells_ne_start x _ (le_max_right _ _)

/-! ## What the sound invariant says about the input tape -/

theorem parkTape_of_walkSoundInv (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (cOld : ℕ → Fin (jj + 1)) (a : Code tm.Q kk x.length S) (g : ℕ → Bool) (s : ℕ)
    (inp : Tape) (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (h : WalkSoundInv (r := r) x L cOld a g s inp work out) :
    TM.parkTape inp = ⟨max a.2.1.val 1, (Tape.init (x.map Γ.ofBool)).cells⟩ := by
  rw [h.2.2.2.2.2.1]
  refine Tape.ext ?_ rfl
  show max (max a.2.1.val 1) 1 = max a.2.1.val 1
  omega

theorem parkTape_read_of_walkSoundInv (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (cOld : ℕ → Fin (jj + 1)) (a : Code tm.Q kk x.length S) (g : ℕ → Bool) (s : ℕ)
    (inp : Tape) (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (h : WalkSoundInv (r := r) x L cOld a g s inp work out) (hne : a.2.1.val ≠ 0) :
    (TM.parkTape inp).read = inSymOf tm x S a := by
  rw [parkTape_of_walkSoundInv x L cOld a g s inp work out h]
  show (Tape.init (x.map Γ.ofBool)).cells (max a.2.1.val 1) = _
  rw [show max a.2.1.val 1 = a.2.1.val by omega]
  rfl

theorem inp_startInvariant_of_walkSoundInv (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (cOld : ℕ → Fin (jj + 1))
    (a : Code tm.Q kk x.length S) (g : ℕ → Bool) (s : ℕ)
    (inp : Tape) (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (h : WalkSoundInv (r := r) x L cOld a g s inp work out) : inp.StartInvariant := by
  rw [h.2.2.2.2.2.1]
  refine ⟨?_, fun q hq => ?_⟩
  · show (Tape.init (x.map Γ.ofBool)).cells 0 = Γ.start
    exact Tape.init_cells_zero _
  · show (Tape.init (x.map Γ.ofBool)).cells q ≠ Γ.start
    exact Tape.init_ofBool_cells_ne_start x q hq

theorem inp_read_ne_start_of_walkSoundInv (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (cOld : ℕ → Fin (jj + 1))
    (a : Code tm.Q kk x.length S) (g : ℕ → Bool) (s : ℕ)
    (inp : Tape) (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (h : WalkSoundInv (r := r) x L cOld a g s inp work out) : inp.read ≠ Γ.start := by
  rw [h.2.2.2.2.2.1]
  show (Tape.init (x.map Γ.ofBool)).cells (max a.2.1.val 1) ≠ Γ.start
  exact Tape.init_ofBool_cells_ne_start x _ (le_max_right _ _)

/-- **What a register tuple holds depends only on the cells of its own registers.** -/
theorem holdsCodeTail_congr {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols cols' : ℕ → Fin (jj + 1) → Γ) (j : ℕ → Fin (jj + 1)) (a : Code tm.Q kk x.length S)
    (h : HoldsCodeTail tm x S cols j a)
    (heq : ∀ p, p < kk + 3 → ∀ q, cols' q (j p) = cols q (j p)) :
    HoldsCodeTail tm x S cols' j a := by
  obtain ⟨⟨hst, hhd, hwk, hot⟩, htail⟩ := h
  refine ⟨⟨fun q hq => ?_, fun q hq => ?_, fun i q hq => ?_, fun q hq => ?_⟩, fun i => ?_⟩
  · show cols' (0 + q + 1) (j 0) = _
    rw [heq 0 (by omega)]
    exact hst q hq
  · show cols' ((succParamsCodec tm.Q kk).width + q + 1) (j 1) = _
    rw [heq 1 (by omega)]
    exact hhd q hq
  · show cols' ((succParamsCodec tm.Q kk).width + q + 1) (j (i.val + 2)) = _
    rw [heq (i.val + 2) (by omega)]
    exact hwk i q hq
  · show cols' ((succParamsCodec tm.Q kk).width + q + 1) (j (kk + 2)) = _
    rw [heq (kk + 2) (by omega)]
    exact hot q hq
  · rw [heq (i.val + 1) (by omega)]
    exact htail i

/-- **The same tuple under another name.** -/
theorem holdsCodeTail_reg_congr {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (j j' : ℕ → Fin (jj + 1)) (a : Code tm.Q kk x.length S)
    (h : HoldsCodeTail tm x S cols j a) (heq : ∀ p, p < kk + 3 → j p = j' p) :
    HoldsCodeTail tm x S cols j' a := by
  obtain ⟨⟨hst, hhd, hwk, hot⟩, htail⟩ := h
  refine ⟨⟨?_, ?_, fun i => ?_, ?_⟩, fun i => ?_⟩
  · rw [show (codeRegsOf (kk := kk) j').st = (codeRegsOf (kk := kk) j).st from
      (heq 0 (by omega)).symm]
    exact hst
  · rw [show (codeRegsOf (kk := kk) j').hd = (codeRegsOf (kk := kk) j).hd from
      (heq 1 (by omega)).symm]
    exact hhd
  · rw [show (codeRegsOf (kk := kk) j').wk i = (codeRegsOf (kk := kk) j).wk i from
      (heq (i.val + 2) (by omega)).symm]
    exact hwk i
  · rw [show (codeRegsOf (kk := kk) j').ot = (codeRegsOf (kk := kk) j).ot from
      (heq (kk + 2) (by omega)).symm]
    exact hot
  · rw [← heq (i.val + 1) (by omega)]
    exact htail i

/-- The machine one stage of a walk runs, named once. -/
noncomputable def stepMachine {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (second advance : Bool)
    (cA cB : ℕ → Fin (jj + 1)) (cO cN : Fin (jj + 1)) (cc : Fin rr) : TM (jj + 2 + rr + 1) :=
  walkStepTM rr tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
    L.toWalkLayout.res cO cN wc advance dc cA cB (stepReg (r := rr) L second) (stepWidth L)
    L.toWalkLayout.stepBlocks (stepTargets jj rr) (auxIdx jj cc)

/-- **What holds of the tapes between stages, whatever the guesses were.** These are the facts
the machine needs to run at all; they say nothing about codes, and they survive every guess. -/
def WalkTapes {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (g : ℕ → Bool) (s : ℕ) (cc : Fin r)
    (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) : TM.TapePred (jj + 2 + r + 1) :=
  fun inp work out =>
    (∀ c : Fin r, c ≠ cc → work (auxIdx jj c) = Wa c) ∧
    (∀ i, (work i).StartInvariant) ∧ (∀ i, 1 ≤ (work i).head) ∧
    (∀ i : Fin (jj + 2), (work (Fin.castAdd r i).castSucc).head = 1) ∧
    (work (walkReg (L.toWalkLayout.reg L.toWalkLayout.rulerIdx))).cells
      (walkScanLen tm x.length S + 1) = Γ.blank ∧
    inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧ 1 ≤ inp.head ∧
    out.StartInvariant ∧ 1 ≤ out.head ∧
    TM.GuessFrom (fun q => g (s * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks + q))
      (work (Fin.last (jj + 2 + r))) ∧
    ∀ p, p < kk + 3 → ∀ q,
      (work (walkReg (L.toWalkLayout.codeT p))).cells q = Wt p q

/-- **A stage that knows its code knows its tapes.** -/
theorem walkTapes_of_walkSoundInv (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (cOld : ℕ → Fin (jj + 1)) (a : Code tm.Q kk x.length S) (g : ℕ → Bool) (s : ℕ)
    (cc : Fin r) (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ)
    (inp : Tape) (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (hframe : ∀ c : Fin r, c ≠ cc → work (auxIdx jj c) = Wa c)
    (hframeT : ∀ p, p < kk + 3 → ∀ q,
      (work (walkReg (L.toWalkLayout.codeT p))).cells q = Wt p q)
    (h : WalkSoundInv (r := r) x L cOld a g s inp work out) :
    WalkTapes (r := r) x L g s cc Wa Wt inp work out :=
  ⟨hframe, h.1, h.2.1, h.2.2.1, h.2.2.2.1, by rw [h.2.2.2.2.2.1], by
      rw [h.2.2.2.2.2.1]
      show 1 ≤ max a.2.1.val 1
      omega,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2, hframeT⟩

/-- **A stage leaves the tapes fit for the next one, whatever the guesses were.** The machine
runs on every guess; this is what it always leaves behind, together with the fact that the
accumulator only ever loses its one. -/
theorem walkStep_tapes (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (g : ℕ → Bool) (second advance : Bool)
    (cA cB : ℕ → Fin (jj + 1)) (cO cN : Fin (jj + 1)) (s : ℕ) (cc : Fin r) (B : ℕ)
    (hB1 : 1 ≤ B) (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) (inp₀ out₀ : Tape)
    (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (htapes : WalkTapes (r := r) x L g s cc Wa Wt inp₀ W₀ out₀) :
    ∃ (c' : Cfg (jj + 2 + r + 1)
        (stepMachine x L dc second advance cA cB cO cN cc).Q) (t : ℕ),
      t ≤ stepTime x L r B ∧
      (stepMachine x L dc second advance cA cB cO cN cc).reachesIn t
        ⟨(stepMachine x L dc second advance cA cB cO cN cc).qstart, inp₀, W₀, out₀⟩ c' ∧
      (stepMachine x L dc second advance cA cB cO cN cc).halted c' ∧
      WalkTapes (r := r) x L g (s + 1) cc Wa Wt c'.input c'.work c'.output ∧
      (∀ n, n < L.toWalkLayout.spares → ∀ p, p < kk + 3 → ∀ q,
        (c'.work (walkReg (L.toWalkLayout.spareReg n p))).cells q
          = (W₀ (walkReg (L.toWalkLayout.spareReg n p))).cells q) ∧
      ((c'.work (auxIdx jj cc)).read = Γ.one → (W₀ (auxIdx jj cc)).read = Γ.one) := by
  classical
  obtain ⟨hframe, hinvW, hhW, hone, hblank, hinpCells, hinpHead, houtSI, houth, hgf, hframeT⟩ :=
    htapes
  have hr1 : ∀ p, p < L.toWalkLayout.stepBlocks → (W₀ (stepReg L second p)).head = 1 :=
    fun p _ => hone (L.toWalkLayout.reg (L.toWalkLayout.stepIdx second p)).castSucc
  have hinpSI : inp₀.StartInvariant := by
    refine ⟨?_, fun q hq => ?_⟩
    · rw [show inp₀.cells 0 = (Tape.init (x.map Γ.ofBool)).cells 0 from congrFun hinpCells 0]
      exact Tape.init_cells_zero _
    · rw [show inp₀.cells q = (Tape.init (x.map Γ.ofBool)).cells q from congrFun hinpCells q]
      exact Tape.init_ofBool_cells_ne_start x q hq
  have hinpRead : inp₀.read ≠ Γ.start := hinpSI.read_ne_start hinpHead
  have houtRead : out₀.read ≠ Γ.start := houtSI.2 _ houth
  have hscan := scanTape_of_step_any x L second g s W₀ hinvW hhW hr1 hgf hblank
  have hchecked := scanTape_checked hscan L.toWalkLayout.par L.toWalkLayout.res
    L.toWalkLayout.res_ne_zero (TM.parkTape inp₀).read
  obtain ⟨c', t, htle, hreach, hhalt, hlast, haux, hinp', hout', hregs, hacc'⟩ :=
    walkStepTM_hoareTime' r tm x.length S L.toWalkLayout.par L.toWalkLayout.mv
      L.toWalkLayout.dr L.toWalkLayout.res cO cN wc advance dc cA cB (stepReg L second)
      (stepWidth L) L.toWalkLayout.stepBlocks (stepTargets jj r) (auxIdx jj cc)
      stepTargets_nodup (fun i => mem_stepTargets i) (fun c => natAdd_notMem_stepTargets c)
      (fun p c _ => stepReg_ne_natAdd L second p c) (fun i => auxIdx_ne_castAdd cc i)
      (auxIdx_ne_last cc) (fun p => stepReg_ne_last L second p) B hB1 inp₀ out₀ W₀ hinpSI
      houtSI hinpRead houtRead hinvW hhW (stepReg_inj L second)
      (head_guessBlocksTapes_le L second W₀ hinvW hhW hone B hB1 hB)
      (walkScanLen tm x.length S)
      (scanOk_of_step L second W₀ hinvW hhW inp₀ out₀ hinpSI houtSI) hscan
      L.toWalkLayout.par_ne_res hchecked inp₀ W₀ out₀ ⟨rfl, rfl, rfl⟩
  obtain ⟨ginv, ghh, -, -, -⟩ := TM.guessBlocksTapes_spec (stepReg L second)
    (fun p => stepReg_ne_last L second p) (stepWidth L) L.toWalkLayout.stepBlocks W₀ hinvW hhW
    (stepReg_inj L second)
  set v := (walkStepScanner tm x.length S L.toWalkLayout.par L.toWalkLayout.mv
      L.toWalkLayout.dr L.toWalkLayout.res cO cN wc advance dc cA cB).emit
    ((walkStepScanner tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
        L.toWalkLayout.res cO cN wc advance dc cA cB).run
      (TM.scanCol (checkedCells (fun i : Fin (jj + 1) =>
        (TM.guessBlocksTapes (stepReg L second) (stepWidth L) L.toWalkLayout.stepBlocks W₀
          (Fin.castAdd r i.castSucc).castSucc).cells) L.toWalkLayout.par L.toWalkLayout.res
        (TM.parkTape inp₀).read)) (walkScanLen tm x.length S)) with hvdef
  have hread' : (c'.work (auxIdx jj cc)).read
      = (if v = true ∧ (W₀ (auxIdx jj cc)).read = Γ.one then Γ.one else Γ.zero) := by
    rw [hacc']
    show Function.update (W₀ (auxIdx jj cc)).cells (W₀ (auxIdx jj cc)).head _
      (W₀ (auxIdx jj cc)).head = _
    rw [Function.update_self]
  have hreg : ∀ i : Fin (jj + 1), c'.work (walkReg i)
      = (⟨1, checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
        (TM.parkTape inp₀).read i⟩ : Tape) := by
    intro i
    have h := hregs i.castSucc
    rw [Fin.snoc_castSucc] at h
    exact h
  have hverdT : c'.work (Fin.castAdd r (Fin.last (jj + 1))).castSucc
      = (⟨1, (TM.guessBlocksTapes (stepReg L second) (stepWidth L) L.toWalkLayout.stepBlocks W₀
          (Fin.castAdd r (Fin.last (jj + 1))).castSucc).cells⟩ : Tape).write (Γ.ofBool v) := by
    have h := hregs (Fin.last (jj + 1))
    rw [Fin.snoc_last] at h
    exact h
  have haccSI : (c'.work (auxIdx jj cc)).StartInvariant ∧ 1 ≤ (c'.work (auxIdx jj cc)).head := by
    have hh0 := hhW (auxIdx jj cc)
    rw [hacc']
    refine ⟨⟨?_, ?_⟩, hh0⟩
    · show Function.update (W₀ (auxIdx jj cc)).cells (W₀ (auxIdx jj cc)).head _ 0 = Γ.start
      rw [Function.update_of_ne (by omega)]
      exact (hinvW (auxIdx jj cc)).1
    · intro q hq
      show Function.update (W₀ (auxIdx jj cc)).cells (W₀ (auxIdx jj cc)).head _ q ≠ Γ.start
      by_cases hqh : q = (W₀ (auxIdx jj cc)).head
      · rw [hqh, Function.update_self]
        split_ifs
        all_goals exact fun hc => Γ.noConfusion hc
      · rw [Function.update_of_ne hqh]
        exact (hinvW (auxIdx jj cc)).2 q hq
  have hall : ∀ i : Fin (jj + 2 + r + 1),
      (c'.work i).StartInvariant ∧ 1 ≤ (c'.work i).head := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [hlast]
      exact ⟨ginv _, ghh _⟩
    · refine Fin.addCases (fun i' => ?_) (fun c => ?_) i
      · refine Fin.lastCases ?_ (fun j => ?_) i'
        · have hSI : (⟨1, (TM.guessBlocksTapes (stepReg L second) (stepWidth L)
                L.toWalkLayout.stepBlocks W₀
                (Fin.castAdd r (Fin.last (jj + 1))).castSucc).cells⟩ : Tape).StartInvariant :=
            ginv (Fin.castAdd r (Fin.last (jj + 1))).castSucc
          rw [hverdT]
          refine ⟨?_, ?_⟩
          · rw [← Γw.ofBool_toΓ]
            exact hSI.write (Γw.ofBool v)
          · rw [Tape.write_head]
        · show (c'.work (walkReg j)).StartInvariant ∧ 1 ≤ (c'.work (walkReg j)).head
          rw [hreg j]
          exact ⟨⟨hchecked.start j, fun q hq => hchecked.ne_start j q hq⟩, le_rfl⟩
      · by_cases hcc : c = cc
        · subst hcc
          exact haccSI
        · rw [haux c (fun hc => hcc (Fin.ext (by
            have hv := congrArg Fin.val hc
            simp only [auxIdx, val_natAdd_castSucc] at hv
            omega)))]
          exact ⟨hinvW _, hhW _⟩
  have hmovedSI : ((TM.parkTape inp₀).move (dc.dec
      (checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
        (TM.parkTape inp₀).read L.toWalkLayout.mv 1)
      (checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
        (TM.parkTape inp₀).read L.toWalkLayout.dr 1))).StartInvariant := by
    have hc : ((TM.parkTape inp₀).move (dc.dec
        (checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
          (TM.parkTape inp₀).read L.toWalkLayout.mv 1)
        (checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
          (TM.parkTape inp₀).read L.toWalkLayout.dr 1))).cells = (TM.parkTape inp₀).cells :=
      Tape.move_cells _ _
    refine ⟨?_, fun q hq => ?_⟩
    · rw [congrFun hc 0]
      exact hinpSI.1
    · rw [congrFun hc q]
      exact hinpSI.2 q hq
  refine ⟨c', t, htle, hreach, hhalt,
    ⟨fun c hc => ?_, fun i => (hall i).1, fun i => (hall i).2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun n hn p hp q => ?_, fun hone' => ?_⟩
  · show c'.work (Fin.natAdd (jj + 2) c).castSucc = Wa c
    rw [haux c (fun hcc => hc (Fin.ext (by
      have hv := congrArg Fin.val hcc
      simp only [auxIdx, val_natAdd_castSucc] at hv
      omega)))]
    exact hframe c hc
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hverdT, Tape.write_head]
    · show (c'.work (walkReg j)).head = 1
      rw [hreg j]
  · show (c'.work (walkReg (L.toWalkLayout.reg L.toWalkLayout.rulerIdx))).cells _ = Γ.blank
    rw [hreg]
    show checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
      (TM.parkTape inp₀).read (L.toWalkLayout.reg L.toWalkLayout.rulerIdx) _ = Γ.blank
    rw [L.toWalkLayout.ruler_zero]
    exact hchecked.blank
  · rw [hinp']
    show (TM.transitionInput ((TM.parkTape inp₀).move (dc.dec
        (checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
          (TM.parkTape inp₀).read L.toWalkLayout.mv 1)
        (checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
          (TM.parkTape inp₀).read L.toWalkLayout.dr 1)))).cells = _
    rw [TM.transitionInput, Tape.move_cells, Tape.move_cells]
    exact hinpCells
  · rw [hinp']
    exact TM.one_le_transitionInput_head hmovedSI
  · rw [hout']
    exact houtSI
  · rw [hout']
    show 1 ≤ max out₀.head 1
    omega
  · rw [hlast]
    exact guessFrom_after_step L second W₀ hinvW hhW g s hgf
  · intro p hp q
    rw [hreg (L.toWalkLayout.codeT p)]
    show checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
      (TM.parkTape inp₀).read (L.toWalkLayout.codeT p) q = _
    rw [checked_cell _ _ _ _ _ (L.toWalkLayout.codeT_ne_res hp),
      congrFun (stepCells_codeT L second W₀ hinvW hhW p hp) q]
    exact hframeT p hp q
  · rw [hreg (L.toWalkLayout.spareReg n p)]
    show checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
      (TM.parkTape inp₀).read (L.toWalkLayout.spareReg n p) q = _
    rw [checked_cell _ _ _ _ _ (L.toWalkLayout.spareReg_ne_res n hn p hp),
      congrFun (stepCells_spare L second W₀ hinvW hhW n hn p hp) q]
  · rw [hread'] at hone'
    by_contra hc
    rw [if_neg (fun hcc => hc hcc.2)] at hone'
    exact Γ.noConfusion hone'

/-- **A stage the machine accepts is a step of the walk.** The run is the one
`Complexity.walkStepTM_hoareTime'` describes — it assumes nothing about the guess — and if the
accumulator survives it, the registers the stage leaves hold a code one step on. -/
theorem walkStep_sound (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (g : ℕ → Bool) (second advance : Bool)
    (cA cB : ℕ → Fin (jj + 1)) (cO cN : Fin (jj + 1)) (pO pN : ℕ)
    (a : Code tm.Q kk x.length S) (s : ℕ) (cc : Fin r) (B : ℕ)
    (hB1 : 1 ≤ B) (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hcAres : ∀ p, p < kk + 3 → cA p ≠ L.toWalkLayout.res)
    (hcBres : ∀ p, p < kk + 3 → cB p ≠ L.toWalkLayout.res)
    (hcOres : cO ≠ L.toWalkLayout.res) (hcNres : cN ≠ L.toWalkLayout.res)
    (hpO : pO < L.toWalkLayout.scratch) (hpN : pN < L.toWalkLayout.scratch)
    (hcOeq : cO = L.toWalkLayout.reg pO) (hcNeq : cN = L.toWalkLayout.reg pN)
    (hwO : wc ≤ stepWidth L pO + 1) (hwN : wc ≤ stepWidth L pN + 1)
    (hcAkeep : ∀ p, p < kk + 3 → ∀ p', p' < L.toWalkLayout.stepBlocks →
      (walkReg (cA p) : Fin (jj + 2 + r + 1)) ≠ stepReg L second p')
    (hclampIn : ∀ P : SuccParams tm.Q kk, a.1 ≠ tm.qhalt → a.1 = P.q →
      P.inSym = inSymOf tm x S a →
      (∀ i, (a.2.2.1 i).2 (a.2.2.1 i).1 = P.wSym i) → a.2.2.2.2 a.2.2.2.1 = P.oSym →
      movedIdx (succTrans tm P).2.2.2.1 a.2.1.val ≤ x.length + S + 1)
    (hwc : wc ≤ walkScanLen tm x.length S)
    (inp₀ out₀ : Tape) (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (bits : ℕ → List Bool)
    (hbitsLen : ∀ p, p < kk + 3 → (bits p).length = blockLen tm x.length S p)
    (hbitsRaw : ∀ p, p < kk + 3 →
      HoldsBits (fun q i => stepCells L second W₀ i q) 0 (cB p) (bits p))
    (hinv : WalkSoundInv (r := r) x L cA a g s inp₀ W₀ out₀) :
    ∃ (c' : Cfg (jj + 2 + r + 1)
        (stepMachine x L dc second advance cA cB cO cN cc).Q) (t : ℕ),
      t ≤ stepTime x L r B ∧
      (stepMachine x L dc second advance cA cB cO cN cc).reachesIn t
        ⟨(stepMachine x L dc second advance cA cB cO cN cc).qstart, inp₀, W₀, out₀⟩ c' ∧
      (stepMachine x L dc second advance cA cB cO cN cc).halted c' ∧
      ((c'.work (auxIdx jj cc)).read = Γ.one →
        (W₀ (auxIdx jj cc)).read = Γ.one ∧
        ∃ b : Code tm.Q kk x.length S, (b = a ∨ b ∈ NTM.codeSucc tm x S a) ∧
          WalkSoundInv (r := r) x L cB b g (s + 1) c'.input c'.work c'.output) := by
  classical
  obtain ⟨hinvW, hhW, hone, hblank, haTail, hinpEq, houtSI, houth, hgf⟩ := hinv
  have hinvFull : WalkSoundInv (r := r) x L cA a g s inp₀ W₀ out₀ :=
    ⟨hinvW, hhW, hone, hblank, haTail, hinpEq, houtSI, houth, hgf⟩
  have hr1 : ∀ p, p < L.toWalkLayout.stepBlocks → (W₀ (stepReg L second p)).head = 1 :=
    fun p _ => hone (L.toWalkLayout.reg (L.toWalkLayout.stepIdx second p)).castSucc
  have hinpSI := inp_startInvariant_of_walkSoundInv x L cA a g s inp₀ W₀ out₀ hinvFull
  have hinpRead := inp_read_ne_start_of_walkSoundInv x L cA a g s inp₀ W₀ out₀ hinvFull
  have houtRead : out₀.read ≠ Γ.start := houtSI.2 _ houth
  have hpark := parkTape_of_walkSoundInv x L cA a g s inp₀ W₀ out₀ hinvFull
  have hscan := scanTape_of_step_any x L second g s W₀ hinvW hhW hr1 hgf hblank
  have hchecked := scanTape_checked hscan L.toWalkLayout.par L.toWalkLayout.res
    L.toWalkLayout.res_ne_zero (TM.parkTape inp₀).read
  obtain ⟨c', t, htle, hreach, hhalt, hlast, haux, hinp', hout', hregs, hacc'⟩ :=
    walkStepTM_hoareTime' r tm x.length S L.toWalkLayout.par L.toWalkLayout.mv
      L.toWalkLayout.dr L.toWalkLayout.res cO cN wc advance dc cA cB (stepReg L second)
      (stepWidth L) L.toWalkLayout.stepBlocks (stepTargets jj r) (auxIdx jj cc)
      stepTargets_nodup (fun i => mem_stepTargets i) (fun c => natAdd_notMem_stepTargets c)
      (fun p c _ => stepReg_ne_natAdd L second p c) (fun i => auxIdx_ne_castAdd cc i)
      (auxIdx_ne_last cc) (fun p => stepReg_ne_last L second p) B hB1 inp₀ out₀ W₀ hinpSI
      houtSI hinpRead houtRead hinvW hhW (stepReg_inj L second)
      (head_guessBlocksTapes_le L second W₀ hinvW hhW hone B hB1 hB)
      (walkScanLen tm x.length S)
      (scanOk_of_step L second W₀ hinvW hhW inp₀ out₀ hinpSI houtSI) hscan
      L.toWalkLayout.par_ne_res hchecked inp₀ W₀ out₀ ⟨rfl, rfl, rfl⟩
  refine ⟨c', t, htle, hreach, hhalt, fun haccOne => ?_⟩
  set v := (walkStepScanner tm x.length S L.toWalkLayout.par L.toWalkLayout.mv
      L.toWalkLayout.dr L.toWalkLayout.res cO cN wc advance dc cA cB).emit
    ((walkStepScanner tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
        L.toWalkLayout.res cO cN wc advance dc cA cB).run
      (TM.scanCol (checkedCells (fun i : Fin (jj + 1) =>
        (TM.guessBlocksTapes (stepReg L second) (stepWidth L) L.toWalkLayout.stepBlocks W₀
          (Fin.castAdd r i.castSucc).castSucc).cells) L.toWalkLayout.par L.toWalkLayout.res
        (TM.parkTape inp₀).read)) (walkScanLen tm x.length S)) with hvdef
  have hread' : (c'.work (auxIdx jj cc)).read
      = (if v = true ∧ (W₀ (auxIdx jj cc)).read = Γ.one then Γ.one else Γ.zero) := by
    rw [hacc']
    show Function.update (W₀ (auxIdx jj cc)).cells (W₀ (auxIdx jj cc)).head _
      (W₀ (auxIdx jj cc)).head = _
    rw [Function.update_self]
  rw [hread'] at haccOne
  have hcond : v = true ∧ (W₀ (auxIdx jj cc)).read = Γ.one := by
    by_contra hc
    rw [if_neg hc] at haccOne
    exact Γ.noConfusion haccOne
  refine ⟨hcond.2, ?_⟩
  obtain ⟨bitsPar, hlenPar, hparRaw⟩ := exists_bits_scratch x L second g s W₀ hinvW hhW hr1 hgf
    L.toWalkLayout.parIdx L.toWalkLayout.par_scratch (succParamsCodec tm.Q kk).width
    (by rw [stepWidth_scratch L _ L.toWalkLayout.par_scratch, L.width_par]
        have := succParamsCodec_width_pos tm
        omega)
  obtain ⟨bitsO, hlenO, hORaw⟩ := exists_bits_scratch x L second g s W₀ hinvW hhW hr1 hgf
    pO hpO wc hwO
  obtain ⟨bitsN, hlenN, hNRaw⟩ := exists_bits_scratch x L second g s W₀ hinvW hhW hr1 hgf
    pN hpN wc hwN
  have haCols : HoldsCodeTail tm x S (fun q i => checkedCells (stepCells L second W₀)
      L.toWalkLayout.par L.toWalkLayout.res (TM.parkTape inp₀).read i q) cA a := by
    refine holdsCodeTail_congr tm x S _ _ cA a haTail (fun p hp q => ?_)
    show checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
      (TM.parkTape inp₀).read (cA p) q = _
    rw [checked_cell _ _ _ _ _ (hcAres p hp),
      congrFun (stepCells_retained L second W₀ hinvW hhW (cA p) (hcAkeep p hp)) q]
  have hverdict : (walkStepScanner tm x.length S L.toWalkLayout.par L.toWalkLayout.mv
        L.toWalkLayout.dr L.toWalkLayout.res cO cN wc advance dc cA cB).emit
      ((walkStepScanner tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
          L.toWalkLayout.res cO cN wc advance dc cA cB).run
        (fun q i => checkedCells (stepCells L second W₀) L.toWalkLayout.par
          L.toWalkLayout.res (TM.parkTape inp₀).read i q) (walkScanLen tm x.length S))
      = true := hcond.1
  obtain ⟨⟨b, hbTail, hbStep⟩, -⟩ := walkStepScanner_sound tm x S
    (fun q i => checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
      (TM.parkTape inp₀).read i q)
    L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr L.toWalkLayout.res cO cN wc advance
    dc cA cB a ((succParamsCodec tm.Q kk).dec bitsPar) ((TM.parkTape inp₀).read)
    bitsPar hlenPar (holdsBits_checked L.toWalkLayout.par_ne_res hparRaw) rfl haCols bits
    hbitsLen (fun p hp => holdsBits_checked (hcBres p hp) (hbitsRaw p hp))
    (hclampIn _) bitsO bitsN hlenO hlenN
    (holdsBits_checked (hcOeq ▸ hcOres) (hcOeq ▸ hORaw))
    (holdsBits_checked (hcNeq ▸ hcNres) (hcNeq ▸ hNRaw)) hwc
    (by show checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
            (TM.parkTape inp₀).read L.toWalkLayout.res 1
          = Γ.ofBool (TM.inMatchVerdict gammaBits (TM.parkTape inp₀).read
            (checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
              (TM.parkTape inp₀).read L.toWalkLayout.par 1)
            (checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
              (TM.parkTape inp₀).read L.toWalkLayout.par 2))
        rw [checkedCells_res, checked_cell _ _ _ _ _ L.toWalkLayout.par_ne_res,
          checked_cell _ _ _ _ _ L.toWalkLayout.par_ne_res])
    (fun h0 => parkTape_read_of_walkSoundInv x L cA a g s inp₀ W₀ out₀ hinvFull h0) hverdict
  obtain ⟨ginv, ghh, -, -, -⟩ := TM.guessBlocksTapes_spec (stepReg L second)
    (fun p => stepReg_ne_last L second p) (stepWidth L) L.toWalkLayout.stepBlocks W₀ hinvW hhW
    (stepReg_inj L second)
  have hreg : ∀ i : Fin (jj + 1), c'.work (walkReg i)
      = (⟨1, checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
        (TM.parkTape inp₀).read i⟩ : Tape) := by
    intro i
    have h := hregs i.castSucc
    rw [Fin.snoc_castSucc] at h
    exact h
  have hverdT : c'.work (Fin.castAdd r (Fin.last (jj + 1))).castSucc
      = (⟨1, (TM.guessBlocksTapes (stepReg L second) (stepWidth L) L.toWalkLayout.stepBlocks W₀
          (Fin.castAdd r (Fin.last (jj + 1))).castSucc).cells⟩ : Tape).write (Γ.ofBool v) := by
    have h := hregs (Fin.last (jj + 1))
    rw [Fin.snoc_last] at h
    exact h
  have haccSI : (c'.work (auxIdx jj cc)).StartInvariant ∧ 1 ≤ (c'.work (auxIdx jj cc)).head := by
    have hh0 := hhW (auxIdx jj cc)
    rw [hacc']
    refine ⟨⟨?_, ?_⟩, hh0⟩
    · show Function.update (W₀ (auxIdx jj cc)).cells (W₀ (auxIdx jj cc)).head _ 0 = Γ.start
      rw [Function.update_of_ne (by omega)]
      exact (hinvW (auxIdx jj cc)).1
    · intro q hq
      show Function.update (W₀ (auxIdx jj cc)).cells (W₀ (auxIdx jj cc)).head _ q ≠ Γ.start
      by_cases hqh : q = (W₀ (auxIdx jj cc)).head
      · rw [hqh, Function.update_self]
        split_ifs
        all_goals exact fun hc => Γ.noConfusion hc
      · rw [Function.update_of_ne hqh]
        exact (hinvW (auxIdx jj cc)).2 q hq
  have hall : ∀ i : Fin (jj + 2 + r + 1),
      (c'.work i).StartInvariant ∧ 1 ≤ (c'.work i).head := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [hlast]
      exact ⟨ginv _, ghh _⟩
    · refine Fin.addCases (fun i' => ?_) (fun c => ?_) i
      · refine Fin.lastCases ?_ (fun j => ?_) i'
        · have hSI : (⟨1, (TM.guessBlocksTapes (stepReg L second) (stepWidth L)
                L.toWalkLayout.stepBlocks W₀
                (Fin.castAdd r (Fin.last (jj + 1))).castSucc).cells⟩ : Tape).StartInvariant :=
            ginv (Fin.castAdd r (Fin.last (jj + 1))).castSucc
          rw [hverdT]
          refine ⟨?_, ?_⟩
          · rw [← Γw.ofBool_toΓ]
            exact hSI.write (Γw.ofBool v)
          · rw [Tape.write_head]
        · show (c'.work (walkReg j)).StartInvariant ∧ 1 ≤ (c'.work (walkReg j)).head
          rw [hreg j]
          exact ⟨⟨hchecked.start j, fun q hq => hchecked.ne_start j q hq⟩, le_rfl⟩
      · by_cases hcc : c = cc
        · subst hcc
          exact haccSI
        · rw [haux c (fun hc => hcc (Fin.ext (by
            have hv := congrArg Fin.val hc
            simp only [auxIdx, val_natAdd_castSucc] at hv
            omega)))]
          exact ⟨hinvW _, hhW _⟩
  have hmovedEq : (TM.parkTape inp₀).move (dc.dec
        (checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
          (TM.parkTape inp₀).read L.toWalkLayout.mv 1)
        (checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
          (TM.parkTape inp₀).read L.toWalkLayout.dr 1))
      = ⟨max b.2.1.val 1, (TM.parkTape inp₀).cells⟩ := by
    refine (walkStep_transports dc a b ((succParamsCodec tm.Q kk).dec bitsPar)
      (TM.parkTape inp₀) _ _ (by rw [hpark]) ?_).2
    rcases hbStep with ⟨hba, hmv, hdr⟩ | ⟨hsucc, hhead, hmv, hdr⟩
    · exact Or.inl ⟨hba, hmv, hdr⟩
    · exact Or.inr ⟨hsucc, hhead, hmv, hdr⟩
  refine ⟨b, ?_, fun i => (hall i).1, fun i => (hall i).2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hbStep with ⟨hba, -, -⟩ | ⟨hsucc, -, -, -⟩
    · exact Or.inl hba
    · exact Or.inr hsucc
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hverdT, Tape.write_head]
    · show (c'.work (walkReg j)).head = 1
      rw [hreg j]
  · show (c'.work (walkReg (L.toWalkLayout.reg L.toWalkLayout.rulerIdx))).cells _ = Γ.blank
    rw [hreg]
    show checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
      (TM.parkTape inp₀).read (L.toWalkLayout.reg L.toWalkLayout.rulerIdx) _ = Γ.blank
    rw [L.toWalkLayout.ruler_zero]
    exact hchecked.blank
  · refine holdsCodeTail_congr tm x S _ _ cB b hbTail (fun p hp q => ?_)
    show (c'.work (walkReg (cB p))).cells q = _
    rw [hreg (cB p)]
  · rw [hinp']
    show TM.transitionInput ((TM.parkTape inp₀).move (dc.dec
        (checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
          (TM.parkTape inp₀).read L.toWalkLayout.mv 1)
        (checkedCells (stepCells L second W₀) L.toWalkLayout.par L.toWalkLayout.res
          (TM.parkTape inp₀).read L.toWalkLayout.dr 1))) = _
    rw [hmovedEq]
    have hcells : (TM.parkTape inp₀).cells = (Tape.init (x.map Γ.ofBool)).cells := by rw [hpark]
    rw [hcells]
    refine TM.transitionInput_eq_self ?_
    show (Tape.init (x.map Γ.ofBool)).cells (max b.2.1.val 1) ≠ Γ.start
    exact Tape.init_ofBool_cells_ne_start x _ (le_max_right _ _)
  · rw [hout']
    exact houtSI
  · rw [hout']
    show 1 ≤ max out₀.head 1
    omega
  · rw [hlast]
    exact guessFrom_after_step L second W₀ hinvW hhW g s hgf

/-! ## Chaining the stages -/

/-- **What a verified walk carries.** The tapes are fit to run, and for as long as the
accumulator still holds its one, the registers hold a code the search has reached in as many
rounds as the walk has taken stages. -/
def WalkChain {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (cOld : ℕ → Fin (jj + 1)) (g : ℕ → Bool) (s : ℕ)
    (cc : Fin r) (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) : TM.TapePred (jj + 2 + r + 1) :=
  fun inp work out => WalkTapes (r := r) x L g s cc Wa Wt inp work out ∧
    ((work (auxIdx jj cc)).read = Γ.one →
      ∃ a, a ∈ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) s ∧
        WalkSoundInv (r := r) x L cOld a g s inp work out)

/-- **One stage carries the chain.** This is the soundness counterpart of
`Complexity.walkStep_carries`: whatever the guesses were, the machine runs, and the codes it
leaves behind — while the accumulator survives — are one round further along. -/
theorem walkStep_chain (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (g : ℕ → Bool) (second advance : Bool)
    (cA cB : ℕ → Fin (jj + 1)) (cO cN : Fin (jj + 1)) (pO pN : ℕ)
    (s : ℕ) (cc : Fin r) (B : ℕ)
    (hspace : ∀ c, tm.ReachesCfg (tm.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hwin : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x S c)
    (hB1 : 1 ≤ B) (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hcAres : ∀ p, p < kk + 3 → cA p ≠ L.toWalkLayout.res)
    (hcBres : ∀ p, p < kk + 3 → cB p ≠ L.toWalkLayout.res)
    (hcOres : cO ≠ L.toWalkLayout.res) (hcNres : cN ≠ L.toWalkLayout.res)
    (hpO : pO < L.toWalkLayout.scratch) (hpN : pN < L.toWalkLayout.scratch)
    (hcOeq : cO = L.toWalkLayout.reg pO) (hcNeq : cN = L.toWalkLayout.reg pN)
    (hwO : wc ≤ stepWidth L pO + 1) (hwN : wc ≤ stepWidth L pN + 1)
    (hcBreg : ∀ p, p < kk + 3 →
      (stepReg L second (L.toWalkLayout.scratch + p) : Fin (jj + 2 + r + 1)) = walkReg (cB p))
    (hcAkeep : ∀ p, p < kk + 3 → ∀ p', p' < L.toWalkLayout.stepBlocks →
      (walkReg (cA p) : Fin (jj + 2 + r + 1)) ≠ stepReg L second p')
    (hwc : wc ≤ walkScanLen tm x.length S) (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) :

    (stepMachine x L dc second advance cA cB cO cN cc).HoareTime
      (WalkChain (r := r) x L cA g s cc Wa Wt) (WalkChain (r := r) x L cB g (s + 1) cc Wa Wt)
      (stepTime x L r B) := by
  intro inp₀ W₀ out₀ hpre
  obtain ⟨htapes, hcode⟩ := hpre
  obtain ⟨c', t, htle, hreach, hhalt, htapes', hspare, hmono⟩ :=
    walkStep_tapes x L dc g second advance cA cB cO cN s cc B hB1 hB Wa Wt inp₀ out₀ W₀
      htapes
  refine ⟨c', t, htle, hreach, hhalt, htapes', fun haccOne => ?_⟩
  obtain ⟨a, ha, hinvA⟩ := hcode (hmono haccOne)
  obtain ⟨bits, hbitsLen, hbitsRaw⟩ := exists_bits_guessed x L second g s W₀ htapes.2.1
    htapes.2.2.1 (fun p _ => htapes.2.2.2.1 (L.toWalkLayout.reg
      (L.toWalkLayout.stepIdx second p)).castSucc) htapes.2.2.2.2.2.2.2.2.2.1 cB hcBreg
  obtain ⟨c'', t'', -, hreach'', hhalt'', hcond⟩ :=
    walkStep_sound x L dc g second advance cA cB cO cN pO pN a s cc B hB1 hB hcAres hcBres
      hcOres hcNres hpO hpN hcOeq hcNeq hwO hwN hcAkeep
      (fun P => clampIn_deferred x S hspace hwin a s ha P) hwc inp₀ out₀ W₀
      bits hbitsLen hbitsRaw hinvA
  have heq : c'' = c' := TM.reachesIn_halted_unique hreach'' hreach hhalt'' hhalt
  subst heq
  obtain ⟨-, b, hbStep, hbInv⟩ := hcond haccOne
  refine ⟨b, ?_, hbInv⟩
  rcases hbStep with rfl | hsucc
  · exact NTM.reachCodes_subset_succ _ s ha
  · exact (NTM.mem_reachCodes_succ_iff _ s b).mpr (Or.inr ⟨a, ha, hsucc⟩)

/-- **Reading the guess stream from a later stage.** A machine that runs after `s₀` stages sees
the tail of the stream, and its own stage counting starts again at zero; this is the translation
between the two. -/
theorem walkTapes_shift (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (g : ℕ → Bool) (s₀ s : ℕ) (cc : Fin r) (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ)
    (inp : Tape) (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape) :
    WalkTapes (r := r) x L
        (fun q => g (s₀ * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks + q)) s cc
        Wa Wt inp work out ↔
      WalkTapes (r := r) x L g (s₀ + s) cc Wa Wt inp work out := by
  have hfun : (fun q => g (s₀ * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks +
        (s * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks + q)))
      = fun q => g ((s₀ + s) * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks + q) := by
    funext q
    congr 1
    ring
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, by rwa [hfun] at h10, h11⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, by rwa [← hfun] at h10, h11⟩

/-- **A combinator's phase boundary moves nothing.** Every tape a walk stage leaves has its head
off the marker, so the transition the combinator applies is the identity. -/
theorem walkTapes_transition_eq (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (g : ℕ → Bool) (s : ℕ) (cc : Fin r) (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ)
    (inp : Tape) (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (h : WalkTapes (r := r) x L g s cc Wa Wt inp work out) :
    TM.transitionInput inp = inp ∧ (fun i => TM.transitionTape (work i)) = work ∧
      TM.transitionTape out = out := by
  refine ⟨?_, funext fun i =>
    TM.transitionTape_eq_self ((h.2.1 i).read_ne_start (h.2.2.1 i)), ?_⟩
  · have hinpSI : inp.StartInvariant := by
      refine ⟨?_, fun q hq => ?_⟩
      · rw [show inp.cells 0 = (Tape.init (x.map Γ.ofBool)).cells 0 from
          congrFun h.2.2.2.2.2.1 0]
        exact Tape.init_cells_zero _
      · rw [show inp.cells q = (Tape.init (x.map Γ.ofBool)).cells q from
          congrFun h.2.2.2.2.2.1 q]
        exact Tape.init_ofBool_cells_ne_start x q hq
    exact TM.transitionInput_eq_self (hinpSI.read_ne_start h.2.2.2.2.2.2.1)
  · exact TM.transitionTape_eq_self
      (h.2.2.2.2.2.2.2.1.read_ne_start h.2.2.2.2.2.2.2.2.1)

/-- **The chain survives a combinator's phase boundary.** -/
theorem walkChain_transition (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (cOld : ℕ → Fin (jj + 1)) (g : ℕ → Bool) (s : ℕ) (cc : Fin r) (Wa : Fin r → Tape)
    (Wt : ℕ → ℕ → Γ)
    (inp : Tape) (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (h : WalkChain (r := r) x L cOld g s cc Wa Wt inp work out) :
    WalkChain (r := r) x L cOld g s cc Wa Wt (TM.transitionInput inp)
      (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
  obtain ⟨hinp, hwork, hout⟩ := walkTapes_transition_eq x L g s cc Wa Wt inp work out h.1
  rw [hinp, hwork, hout]
  exact h

/-- **A pair of stages carries the chain two steps.** The soundness counterpart of
`Complexity.walkPair_carries`. -/
theorem walkPair_chain (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (g : ℕ → Bool) (s : ℕ) (cc : Fin r) (B : ℕ)
    (hspace : ∀ c, tm.ReachesCfg (tm.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hwin : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x S c)
    (hB1 : 1 ≤ B) (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hwc : wc ≤ walkScanLen tm x.length S) (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) :
    (walkPairTM r tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
        L.toWalkLayout.res L.toWalkLayout.cnt L.toWalkLayout.cnt' wc dc
        L.toWalkLayout.codeA L.toWalkLayout.codeB (stepReg L false) (stepReg L true)
        (stepWidth L) L.toWalkLayout.stepBlocks (stepTargets jj r) (auxIdx jj cc)).HoareTime
      (WalkChain (r := r) x L L.toWalkLayout.codeA g s cc Wa Wt)
      (WalkChain (r := r) x L L.toWalkLayout.codeA g (s + 2) cc Wa Wt)
      (stepTime x L r B + 1 + stepTime x L r B) := by
  have hcntW : wc ≤ stepWidth L L.toWalkLayout.cntIdx + 1 := by
    rw [stepWidth_scratch L _ L.toWalkLayout.cnt_scratch, L.width_cnt]
    omega
  have hcnt'W : wc ≤ stepWidth L L.toWalkLayout.cnt'Idx + 1 := by
    rw [stepWidth_scratch L _ L.toWalkLayout.cnt'_scratch, L.width_cnt']
    omega
  refine TM.seqTM_hoareTime _ _
    (mid := WalkChain (r := r) x L L.toWalkLayout.codeB g (s + 1) cc Wa Wt)
    (mid' := WalkChain (r := r) x L L.toWalkLayout.codeB g (s + 1) cc Wa Wt)
    ?_ (walkChain_transition x L L.toWalkLayout.codeB g (s + 1) cc Wa Wt) ?_
  · exact walkStep_chain x L dc g false false L.toWalkLayout.codeA L.toWalkLayout.codeB
      L.toWalkLayout.cnt L.toWalkLayout.cnt' L.toWalkLayout.cntIdx L.toWalkLayout.cnt'Idx s cc B
      hspace hwin hB1 hB (fun p hp => L.toWalkLayout.codeA_ne_res hp)
      (fun p hp => L.toWalkLayout.codeB_ne_res hp) L.toWalkLayout.cnt_ne_res
      L.toWalkLayout.cnt'_ne_res L.toWalkLayout.cnt_scratch L.toWalkLayout.cnt'_scratch rfl rfl
      hcntW hcnt'W
      (fun p hp => by rw [stepReg, L.toWalkLayout.stepIdx_codeB p hp]; rfl)
      (fun p hp p' hp' hc => L.toWalkLayout.stepIdx_ne_codeA p' p hp' hp
        (L.toWalkLayout.reg_inj _ _ (L.toWalkLayout.stepIdx_lt false p' hp')
          (L.toWalkLayout.codeA_lt p hp) (walkReg_inj hc).symm)) hwc Wa Wt
  · exact walkStep_chain x L dc g true false L.toWalkLayout.codeB L.toWalkLayout.codeA
      L.toWalkLayout.cnt' L.toWalkLayout.cnt L.toWalkLayout.cnt'Idx L.toWalkLayout.cntIdx
      (s + 1) cc B hspace hwin hB1 hB (fun p hp => L.toWalkLayout.codeB_ne_res hp)
      (fun p hp => L.toWalkLayout.codeA_ne_res hp) L.toWalkLayout.cnt'_ne_res
      L.toWalkLayout.cnt_ne_res L.toWalkLayout.cnt'_scratch L.toWalkLayout.cnt_scratch rfl rfl
      hcnt'W hcntW
      (fun p hp => by rw [stepReg, L.toWalkLayout.stepIdx_codeA p hp]; rfl)
      (fun p hp p' hp' hc => L.toWalkLayout.stepIdx_ne_codeB p' p hp' hp
        (L.toWalkLayout.reg_inj _ _ (L.toWalkLayout.stepIdx_lt true p' hp')
          (L.toWalkLayout.codeB_lt p hp) (walkReg_inj hc).symm)) hwc Wa Wt

/-- **The sound invariant does not see the auxiliary tapes.** -/
theorem walkSoundInv_update_aux (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (cOld : ℕ → Fin (jj + 1)) (a : Code tm.Q kk x.length S) (g : ℕ → Bool) (s : ℕ)
    (c₀ : Fin r) (t : Tape) (htSI : t.StartInvariant) (hth : 1 ≤ t.head)
    (inp : Tape) (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (h : WalkSoundInv (r := r) x L cOld a g s inp work out) :
    WalkSoundInv (r := r) x L cOld a g s inp (Function.update work (auxIdx jj c₀) t) out := by
  classical
  have hupd : ∀ i : Fin (jj + 2 + r + 1), i ≠ auxIdx jj c₀ →
      Function.update work (auxIdx jj c₀) t i = work i := fun i hi =>
    Function.update_of_ne hi _ _
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, ?_, ?_,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, ?_⟩
  · by_cases hi : i = auxIdx jj c₀
    · rw [hi, Function.update_self]; exact htSI
    · rw [hupd i hi]; exact h.1 i
  · by_cases hi : i = auxIdx jj c₀
    · rw [hi, Function.update_self]; exact hth
    · rw [hupd i hi]; exact h.2.1 i
  · rw [hupd _ (fun hc => auxIdx_ne_castAdd c₀ i hc.symm)]
    exact h.2.2.1 i
  · rw [hupd _ (walkReg_ne_auxIdx _ c₀)]
    exact h.2.2.2.1
  · refine holdsCodeTail_congr tm x S _ _ cOld a h.2.2.2.2.1 (fun p hp q => ?_)
    show (Function.update work (auxIdx jj c₀) t (walkReg (cOld p))).cells q = _
    rw [hupd _ (walkReg_ne_auxIdx _ c₀)]
  · rw [hupd _ (Ne.symm (auxIdx_ne_last c₀))]
    exact h.2.2.2.2.2.2.2.2

/-- **Nor do the tape facts.** -/
theorem walkTapes_update_aux (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (g : ℕ → Bool) (s : ℕ) (cc : Fin r) (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ)
    (c₀ : Fin r) (t : Tape) (htSI : t.StartInvariant) (hth : 1 ≤ t.head)
    (inp : Tape) (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (h : WalkTapes (r := r) x L g s cc Wa Wt inp work out) :
    WalkTapes (r := r) x L g s cc
      (fun c => Function.update work (auxIdx jj c₀) t (auxIdx jj c)) Wt inp
      (Function.update work (auxIdx jj c₀) t) out := by
  classical
  have hupd : ∀ i : Fin (jj + 2 + r + 1), i ≠ auxIdx jj c₀ →
      Function.update work (auxIdx jj c₀) t i = work i := fun i hi =>
    Function.update_of_ne hi _ _
  refine ⟨fun c hc => rfl, fun i => ?_, fun i => ?_, fun i => ?_, ?_,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, ?_,
    fun p hp q => ?_⟩
  · by_cases hi : i = auxIdx jj c₀
    · rw [hi, Function.update_self]; exact htSI
    · rw [hupd i hi]; exact h.2.1 i
  · by_cases hi : i = auxIdx jj c₀
    · rw [hi, Function.update_self]; exact hth
    · rw [hupd i hi]; exact h.2.2.1 i
  · rw [hupd _ (fun hc => auxIdx_ne_castAdd c₀ i hc.symm)]
    exact h.2.2.2.1 i
  · rw [hupd _ (walkReg_ne_auxIdx _ c₀)]
    exact h.2.2.2.2.1
  · rw [hupd _ (Ne.symm (auxIdx_ne_last c₀))]
    exact h.2.2.2.2.2.2.2.2.2.1
  · rw [hupd _ (walkReg_ne_auxIdx _ c₀)]
    exact h.2.2.2.2.2.2.2.2.2.2 p hp q

/-- The chain, as the count-up loop's invariant: two stages of the walk per iteration. -/
def WalkChainP {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (g : ℕ → Bool) (cc : Fin r) (Wt : ℕ → ℕ → Γ) :
    ℕ → TM.TapePred (jj + 2 + r + 1) :=
  fun j inp work out => WalkChain (r := r) x L L.toWalkLayout.codeA g (2 * j) cc
    (fun c => work (auxIdx jj c)) Wt inp work out

/-- **The body of the walk loop, in the soundness direction.** -/
theorem walkPair_chain_body (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (g : ℕ → Bool) (cc cnt lim : Fin r) (hcnt : cnt ≠ cc) (hlim : lim ≠ cc)
    (B : ℕ)
    (hspace : ∀ c, tm.ReachesCfg (tm.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hwin : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x S c)
    (hB1 : 1 ≤ B) (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hwc : wc ≤ walkScanLen tm x.length S) (Wt : ℕ → ℕ → Γ) (N value : ℕ) :
    (walkPairTM r tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
        L.toWalkLayout.res L.toWalkLayout.cnt L.toWalkLayout.cnt' wc dc
        L.toWalkLayout.codeA L.toWalkLayout.codeB (stepReg L false) (stepReg L true)
        (stepWidth L) L.toWalkLayout.stepBlocks (stepTargets jj r) (auxIdx jj cc)).HoareTime
      (TM.BinaryForFrame (auxIdx jj cnt) (auxIdx jj lim) N (WalkChainP x L g cc Wt) value)
      (TM.BinaryForBodyPost (auxIdx jj cnt) (auxIdx jj lim) N (WalkChainP x L g cc Wt) value)
      (stepTime x L r B + 1 + stepTime x L r B) := by
  classical
  intro inp work out hpre
  obtain ⟨hP, hcnt0, hlim0, -, -, -⟩ := hpre
  obtain ⟨c', t, htle, hreach, hhalt, hpost⟩ :=
    walkPair_chain x L dc g (2 * value) cc B hspace hwin hB1 hB hwc
      (fun c => work (auxIdx jj c)) Wt inp work out hP
  have hframe := hpost.1.1
  refine ⟨c', t, htle, hreach, hhalt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hframe cnt hcnt]
    exact hcnt0
  · rw [hframe lim hlim]
    exact hlim0
  · refine Tape.StartInvariant.read_ne_start ⟨?_, fun q hq => ?_⟩ hpost.1.2.2.2.2.2.2.1
    · rw [show c'.input.cells 0 = (Tape.init (x.map Γ.ofBool)).cells 0 from
        congrFun hpost.1.2.2.2.2.2.1 0]
      exact Tape.init_cells_zero _
    · rw [show c'.input.cells q = (Tape.init (x.map Γ.ofBool)).cells q from
        congrFun hpost.1.2.2.2.2.2.1 q]
      exact Tape.init_ofBool_cells_ne_start x q hq
  · exact fun i => (hpost.1.2.1 i).read_ne_start (hpost.1.2.2.1 i)
  · exact hpost.1.2.2.2.2.2.2.2.1.read_ne_start hpost.1.2.2.2.2.2.2.2.2.1
  · intro tc htc
    obtain ⟨htSI, hth⟩ := startInvariant_of_hasBinaryNat htc
    have hupdcc : Function.update c'.work (auxIdx jj cnt) tc (auxIdx jj cc)
        = c'.work (auxIdx jj cc) :=
      Function.update_of_ne (fun hc => hcnt (Fin.ext (by
        have hv' := congrArg Fin.val hc
        simp only [auxIdx, val_natAdd_castSucc] at hv'
        omega))) _ _
    show WalkChain (r := r) x L L.toWalkLayout.codeA g (2 * (value + 1)) cc _ _ _ _ _
    rw [show 2 * (value + 1) = 2 * value + 2 by omega]
    refine ⟨walkTapes_update_aux x L g (2 * value + 2) cc _ _ cnt tc htSI (by omega)
      c'.input c'.work c'.output hpost.1, fun haccOne => ?_⟩
    rw [hupdcc] at haccOne
    obtain ⟨a, ha, hinvA⟩ := hpost.2 haccOne
    exact ⟨a, ha, walkSoundInv_update_aux x L L.toWalkLayout.codeA a g (2 * value + 2) cnt tc
      htSI (by omega) c'.input c'.work c'.output hinvA⟩

/-- **The walk loop, in the soundness direction.** After `N` iterations, for as long as the
accumulator has kept its one, the code registers hold something the search reaches in `2 * N`
rounds. This is the counterpart of `Complexity.walkLoop_carries`, and together with
`Complexity.mem_reachCodes_of_walk` it is what makes an accepted walk mean something. -/
theorem walkLoop_chain (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (g : ℕ → Bool) (cc cnt lim : Fin r) (hcnt : cnt ≠ cc) (hlim : lim ≠ cc)
    (hcl : cnt ≠ lim) (B : ℕ)
    (hspace : ∀ c, tm.ReachesCfg (tm.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hwin : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x S c)
    (hB1 : 1 ≤ B) (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hwc : wc ≤ walkScanLen tm x.length S) (Wt : ℕ → ℕ → Γ) (N : ℕ) :
    (walkLoopTM r tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
        L.toWalkLayout.res L.toWalkLayout.cnt L.toWalkLayout.cnt' dc
        L.toWalkLayout.codeA L.toWalkLayout.codeB (stepReg L false) (stepReg L true)
        (stepWidth L) L.toWalkLayout.stepBlocks wc (stepTargets jj r) (auxIdx jj cc)
        (auxIdx jj cnt) (auxIdx jj lim)).HoareTime
      (TM.BinaryForFrame (auxIdx jj cnt) (auxIdx jj lim) N (WalkChainP x L g cc Wt) 0)
      (TM.BinaryForFrame (auxIdx jj cnt) (auxIdx jj lim) N (WalkChainP x L g cc Wt) N)
      (TM.binaryForLoopTime (fun _ => stepTime x L r B + 1 + stepTime x L r B) N 0 N) :=
  TM.binaryForTM_hoareTime (auxIdx_injective hcl) N
    (fun _ => stepTime x L r B + 1 + stepTime x L r B) (WalkChainP x L g cc Wt)
    (fun value _ => walkPair_chain_body x L dc g cc cnt lim hcnt hlim B hspace hwin hB1 hB hwc
      Wt N value)

/-! ## What a walk leaves alone

The chain says what the code registers hold; a loop that *contains* a walk also needs to know that
its own auxiliary tapes come through, and that the accumulator cannot come back to life. Neither
is about codes, so both are carried beside the chain. -/

/-- **What a walk does not own**: the auxiliary tapes other than its accumulator and its own
counter, a spare code tuple, and the record that the accumulator survived. -/
def WalkKept {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (cc cnt : Fin r) (Wa : Fin r → Tape) (a₀ : Γ)
    (Wf : ℕ → ℕ → ℕ → Γ) : TM.TapePred (jj + 2 + r + 1) :=
  fun _ work _ => (∀ c, c ≠ cc → c ≠ cnt → work (auxIdx jj c) = Wa c) ∧
    ((work (auxIdx jj cc)).read = Γ.one → a₀ = Γ.one) ∧
    ∀ n, n < L.toWalkLayout.spares → ∀ p, p < kk + 3 → ∀ q,
      (work (walkReg (L.toWalkLayout.spareReg n p))).cells q = Wf n p q

/-- **One stage keeps them.** -/
theorem walkStep_kept (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (g : ℕ → Bool) (second advance : Bool)
    (cA cB : ℕ → Fin (jj + 1)) (cO cN : Fin (jj + 1)) (s : ℕ) (cc cnt : Fin r) (B : ℕ)
    (hB1 : 1 ≤ B) (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (Wt : ℕ → ℕ → Γ) (Wa : Fin r → Tape) (a₀ : Γ) (Wf : ℕ → ℕ → ℕ → Γ) :
    (stepMachine x L dc second advance cA cB cO cN cc).HoareTime
      (fun i w o => WalkTapes (r := r) x L g s cc (fun c => w (auxIdx jj c)) Wt i w o ∧
        WalkKept x L cc cnt Wa a₀ Wf i w o)
      (fun i w o => WalkTapes (r := r) x L g (s + 1) cc (fun c => w (auxIdx jj c)) Wt i w o ∧
        WalkKept x L cc cnt Wa a₀ Wf i w o)
      (stepTime x L r B) := by
  rintro inp₀ W₀ out₀ ⟨htapes, hkept⟩
  obtain ⟨c', t, htle, hreach, hhalt, htapes', hspare, hmono⟩ :=
    walkStep_tapes x L dc g second advance cA cB cO cN s cc B hB1 hB
      (fun c => W₀ (auxIdx jj c)) Wt inp₀ out₀ W₀ htapes
  refine ⟨c', t, htle, hreach, hhalt,
    ⟨fun c _ => rfl, htapes'.2.1, htapes'.2.2.1, htapes'.2.2.2.1, htapes'.2.2.2.2.1,
      htapes'.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.2.1,
      htapes'.2.2.2.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.2.2.2.1,
      htapes'.2.2.2.2.2.2.2.2.2.2⟩,
    fun c hc hcn => ?_, fun hone => hkept.2.1 (hmono hone), fun n hn p hp q => ?_⟩
  · rw [htapes'.1 c hc]
    exact hkept.1 c hc hcn
  · rw [hspare n hn p hp q]
    exact hkept.2.2 n hn p hp q

/-- **A pair of stages keeps them.** -/
theorem walkPair_kept (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (g : ℕ → Bool) (s : ℕ) (cc cnt : Fin r) (B : ℕ)
    (hB1 : 1 ≤ B) (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (Wt : ℕ → ℕ → Γ) (Wa : Fin r → Tape) (a₀ : Γ) (Wf : ℕ → ℕ → ℕ → Γ) :
    (walkPairTM r tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
        L.toWalkLayout.res L.toWalkLayout.cnt L.toWalkLayout.cnt' wc dc
        L.toWalkLayout.codeA L.toWalkLayout.codeB (stepReg L false) (stepReg L true)
        (stepWidth L) L.toWalkLayout.stepBlocks (stepTargets jj r) (auxIdx jj cc)).HoareTime
      (fun i w o => WalkTapes (r := r) x L g s cc (fun c => w (auxIdx jj c)) Wt i w o ∧
        WalkKept x L cc cnt Wa a₀ Wf i w o)
      (fun i w o => WalkTapes (r := r) x L g (s + 2) cc (fun c => w (auxIdx jj c)) Wt i w o ∧
        WalkKept x L cc cnt Wa a₀ Wf i w o)
      (stepTime x L r B + 1 + stepTime x L r B) := by
  refine TM.seqTM_hoareTime _ _
    (mid := fun i w o => WalkTapes (r := r) x L g (s + 1) cc (fun c => w (auxIdx jj c)) Wt i w o ∧
      WalkKept x L cc cnt Wa a₀ Wf i w o)
    (mid' := fun i w o => WalkTapes (r := r) x L g (s + 1) cc (fun c => w (auxIdx jj c)) Wt i w o ∧
      WalkKept x L cc cnt Wa a₀ Wf i w o)
    (walkStep_kept x L dc g false false L.toWalkLayout.codeA L.toWalkLayout.codeB
      L.toWalkLayout.cnt L.toWalkLayout.cnt' s cc cnt B hB1 hB Wt Wa a₀ Wf)
    (fun inp work out h => ?_)
    (by
      have h := walkStep_kept x L dc g true false L.toWalkLayout.codeB L.toWalkLayout.codeA
        L.toWalkLayout.cnt' L.toWalkLayout.cnt (s + 1) cc cnt B hB1 hB Wt Wa a₀ Wf
      rw [show s + 1 + 1 = s + 2 by omega] at h
      exact h)
  obtain ⟨hinp, hwork, hout⟩ :=
    walkTapes_transition_eq x L g (s + 1) cc (fun c => work (auxIdx jj c)) Wt inp work out h.1
  rw [hinp, hwork, hout]
  exact h

/-- **A whole walk keeps them.** -/
theorem walkLoop_kept (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (g : ℕ → Bool) (cc cnt lim : Fin r) (hcnt : cnt ≠ cc) (hlim : lim ≠ cc)
    (hcl : cnt ≠ lim) (B : ℕ)
    (hspace : ∀ c, tm.ReachesCfg (tm.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hwin : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x S c)
    (hB1 : 1 ≤ B) (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hwc : wc ≤ walkScanLen tm x.length S) (Wt : ℕ → ℕ → Γ) (Wa : Fin r → Tape) (a₀ : Γ)
    (Wf : ℕ → ℕ → ℕ → Γ) (N : ℕ) :
    (walkLoopTM r tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
        L.toWalkLayout.res L.toWalkLayout.cnt L.toWalkLayout.cnt' dc
        L.toWalkLayout.codeA L.toWalkLayout.codeB (stepReg L false) (stepReg L true)
        (stepWidth L) L.toWalkLayout.stepBlocks wc (stepTargets jj r) (auxIdx jj cc)
        (auxIdx jj cnt) (auxIdx jj lim)).HoareTime
      (TM.BinaryForFrame (auxIdx jj cnt) (auxIdx jj lim) N
        (fun j i w o => WalkChainP x L g cc Wt j i w o ∧
          WalkKept x L cc cnt Wa a₀ Wf i w o) 0)
      (TM.BinaryForFrame (auxIdx jj cnt) (auxIdx jj lim) N
        (fun j i w o => WalkChainP x L g cc Wt j i w o ∧
          WalkKept x L cc cnt Wa a₀ Wf i w o) N)
      (TM.binaryForLoopTime (fun _ => stepTime x L r B + 1 + stepTime x L r B) N 0 N) := by
  refine TM.binaryForTM_hoareTime (auxIdx_injective hcl) N
    (fun _ => stepTime x L r B + 1 + stepTime x L r B) _ (fun value _ => ?_)
  rintro inp work out ⟨⟨hP, hK⟩, hcnt0, hlim0, hin, hw, hout⟩
  obtain ⟨c', t, htle, hreach, hhalt, hpost⟩ :=
    walkPair_chain_body x L dc g cc cnt lim hcnt hlim B hspace hwin hB1 hB hwc Wt N value
      inp work out ⟨hP, hcnt0, hlim0, hin, hw, hout⟩
  obtain ⟨c'', t'', -, hreach'', hhalt'', hpost''⟩ :=
    walkPair_kept x L dc g (2 * value) cc cnt B hB1 hB Wt Wa a₀ Wf inp work out ⟨hP.1, hK⟩
  have hc : c'' = c' := TM.reachesIn_halted_unique hreach'' hreach hhalt'' hhalt
  subst hc
  refine ⟨c'', t, htle, hreach, hhalt, hpost.1, hpost.2.1, hpost.2.2.1, hpost.2.2.2.1,
    hpost.2.2.2.2.1, fun tc htc => ⟨hpost.2.2.2.2.2 tc htc, fun c hc hcn => ?_, fun hone => ?_,
      fun n hn p hp q => ?_⟩⟩
  · rw [Function.update_of_ne (auxIdx_injective hcn)]
    exact hpost''.2.1 c hc hcn
  · rw [Function.update_of_ne (auxIdx_injective (fun h => hcnt h.symm))] at hone
    exact hpost''.2.2.1 hone
  · rw [Function.update_of_ne (walkReg_ne_auxIdx _ cnt)]
    exact hpost''.2.2.2 n hn p hp q

/-! ## Entering the loop -/

/-- **The state the walk loop starts in.** The code registers hold the initial code, the
accumulator holds its one, and the driver's counter and limit are set — which is exactly the
frame `TM.binaryForTM_hoareTime` asks for at index zero. -/
theorem binaryForFrame_walkChainP_init (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (g : ℕ → Bool) (cc cnt lim : Fin r) (N : ℕ)
    (inp : Tape) (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (htapes : WalkTapes (r := r) x L g 0 cc (fun c => work (auxIdx jj c))
      (fun p q => (work (walkReg (L.toWalkLayout.codeT p))).cells q) inp work out)
    (hcode : (work (auxIdx jj cc)).read = Γ.one →
      HoldsCodeTail tm x S (fun q i => (work (walkReg i)).cells q) L.toWalkLayout.codeA
        (cfgCode x.length S (tm.initCfg x)))
    (hinp : (work (auxIdx jj cc)).read = Γ.one →
      inp.head = max (cfgCode x.length S (tm.initCfg x)).2.1.val 1)
    (hcnt : (work (auxIdx jj cnt)).HasBinaryNat 0)
    (hlim : (work (auxIdx jj lim)).HasBinaryNat N) :
    TM.BinaryForFrame (auxIdx jj cnt) (auxIdx jj lim) N
      (WalkChainP x L g cc (fun p q => (work (walkReg (L.toWalkLayout.codeT p))).cells q)) 0
      inp work out := by
  refine ⟨⟨htapes, fun hone => ⟨cfgCode x.length S (tm.initCfg x), ?_, ?_⟩⟩, hcnt, hlim, ?_, ?_,
    ?_⟩
  · rw [NTM.reachCodes]
    exact Finset.mem_singleton_self _
  · exact ⟨htapes.2.1, htapes.2.2.1, htapes.2.2.2.1, htapes.2.2.2.2.1, hcode hone,
      Tape.ext (hinp hone) htapes.2.2.2.2.2.1, htapes.2.2.2.2.2.2.2.1,
      htapes.2.2.2.2.2.2.2.2.1, htapes.2.2.2.2.2.2.2.2.2.1⟩
  · refine Tape.StartInvariant.read_ne_start ⟨?_, fun q hq => ?_⟩ htapes.2.2.2.2.2.2.1
    · rw [show inp.cells 0 = (Tape.init (x.map Γ.ofBool)).cells 0 from
        congrFun htapes.2.2.2.2.2.1 0]
      exact Tape.init_cells_zero _
    · rw [show inp.cells q = (Tape.init (x.map Γ.ofBool)).cells q from
        congrFun htapes.2.2.2.2.2.1 q]
      exact Tape.init_ofBool_cells_ne_start x q hq
  · exact fun i => (htapes.2.1 i).read_ne_start (htapes.2.2.1 i)
  · exact htapes.2.2.2.2.2.2.2.1.read_ne_start htapes.2.2.2.2.2.2.2.2.1

/-- **And what it leaves when it stops.** An accepted walk of `N` iterations puts a code the
search reaches in `2 * N` rounds into the registers — which, with
`Complexity.mem_reachCodes_of_walk`, is the whole point of the walk. -/
theorem mem_reachCodes_of_binaryForFrame (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (g : ℕ → Bool) (cc cnt lim : Fin r) (N : ℕ)
    (inp : Tape) (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (Wt : ℕ → ℕ → Γ)
    (h : TM.BinaryForFrame (auxIdx jj cnt) (auxIdx jj lim) N (WalkChainP x L g cc Wt) N
      inp work out)
    (hacc : (work (auxIdx jj cc)).read = Γ.one) :
    ∃ a, a ∈ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N) ∧
      HoldsCodeTail tm x S (fun q i => (work (walkReg i)).cells q) L.toWalkLayout.codeA a :=
  let ⟨a, ha, hinv⟩ := h.1.2 hacc
  ⟨a, ha, hinv.2.2.2.2.1⟩

/-! ## The walk fits in a logarithmic window

Every register the walk uses is as wide as its scan, and the scan is as long as
`Complexity.walkScanLen` — a constant of the machine plus a few multiples of the space bound and
one binary counter over the input. With a logarithmic space bound that is logarithmic. -/

theorem bitWidth_mono {m n : ℕ} (h : m ≤ n) : bitWidth m ≤ bitWidth n :=
  Nat.clog_mono_right _ h

/-- **The scan is logarithmically long.** -/
theorem walkScanLen_le_logWindow {kk : ℕ} (tm : NTM kk) (C D : ℕ) (n : ℕ) :
    walkScanLen tm n (logWindow C D n)
      ≤ logWindow (1 + 9 * C)
        ((succParamsCodec tm.Q kk).width + (qCodec tm.Q).width + stateWidth tm
          + (C + D + 5) + 9 * D + 15) n := by
  have hlog : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  have hS : logWindow C D n = C * Nat.log 2 n + D := rfl
  have hle : n + logWindow C D n + 2 ≤ (C + D + 3) * (n + 1) ^ 1 + 1 := by
    rw [hS, pow_one]
    have h1 : C * Nat.log 2 n ≤ C * n := Nat.mul_le_mul_left C hlog
    have h2 : (1 + C) * n ≤ (C + D + 3) * n := Nat.mul_le_mul_right n (by omega)
    have h3 : (C + D + 3) * (n + 1) = (C + D + 3) * n + (C + D + 3) := by ring
    have h4 : (1 + C) * n = n + C * n := by ring
    omega
  have hbw : bitWidth (n + logWindow C D n + 2) ≤ Nat.log 2 n + (C + D + 5) := by
    refine le_trans (bitWidth_mono hle) ?_
    have h := bitWidth_poly_le (C + D + 3) 1 n
    have hw : logWindow 1 (C + D + 3 + 1 + 1) n = Nat.log 2 n + (C + D + 5) := by
      show 1 * Nat.log 2 n + (C + D + 3 + 1 + 1) = _
      omega
    rw [hw] at h
    exact h
  rw [walkScanLen, finCodec_width]
  show _ ≤ (1 + 9 * C) * Nat.log 2 n + _
  have hmul : (1 + 9 * C) * Nat.log 2 n = Nat.log 2 n + 9 * (C * Nat.log 2 n) := by ring
  omega

/-- **The code the enclosing enumeration is testing survives the whole walk.** The walk writes
only the scratch and its own two code tuples, so the third one comes out of the loop holding
exactly what went in — which is what lets a caller compare the walk's endpoint against it. -/
theorem codeT_of_binaryForFrame (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (g : ℕ → Bool) (cc cnt lim : Fin r) (Wt : ℕ → ℕ → Γ) (N : ℕ)
    (inp : Tape) (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (h : TM.BinaryForFrame (auxIdx jj cnt) (auxIdx jj lim) N (WalkChainP x L g cc Wt) N
      inp work out) :
    ∀ p, p < kk + 3 → ∀ q, (work (walkReg (L.toWalkLayout.codeT p))).cells q = Wt p q :=
  h.1.1.2.2.2.2.2.2.2.2.2.2

/-- And so a code it held is still held. -/
theorem holdsCodeTail_codeT_survives (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (g : ℕ → Bool) (cc cnt lim : Fin r) (N : ℕ)
    (u : Code tm.Q kk x.length S) (inp : Tape) (work W₀ : Fin (jj + 2 + r + 1) → Tape)
    (out : Tape)
    (h : TM.BinaryForFrame (auxIdx jj cnt) (auxIdx jj lim) N
      (WalkChainP x L g cc (fun p q => (W₀ (walkReg (L.toWalkLayout.codeT p))).cells q)) N
      inp work out)
    (hu : HoldsCodeTail tm x S (fun q i => (W₀ (walkReg i)).cells q) L.toWalkLayout.codeT u) :
    HoldsCodeTail tm x S (fun q i => (work (walkReg i)).cells q) L.toWalkLayout.codeT u :=
  holdsCodeTail_congr tm x S _ _ L.toWalkLayout.codeT u hu
    (fun p hp q => codeT_of_binaryForFrame x L g cc cnt lim _ N inp work out h p hp q)

/-! ## Testing a code for membership in a round

The walk decides "the code in `codeA` is reachable in `2 * N` steps". What an enumeration wants
is "the code in `codeT` is", and the two differ by exactly one more step — `codeT = codeA` or
`codeT ∈ codeSucc codeA` is precisely what `Complexity.walkCodeScanner` decides. So the test is
the walk followed by one more step, checking against the third tuple instead of guessing a new
code: the step's guess still writes the scratch and the walk's spare tuple, and leaves `codeA`
and `codeT` alone. -/

/-- **The membership test**: walk, then check the third tuple against where the walk ended. -/
noncomputable def memberTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (cc cnt lim : Fin rr) :
    TM (jj + 2 + rr + 1) :=
  TM.seqTM
    (walkLoopTM rr tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
      L.toWalkLayout.res L.toWalkLayout.cnt L.toWalkLayout.cnt' dc
      L.toWalkLayout.codeA L.toWalkLayout.codeB (stepReg (r := rr) L false)
      (stepReg (r := rr) L true) (stepWidth L) L.toWalkLayout.stepBlocks wc (stepTargets jj rr)
      (auxIdx jj cc) (auxIdx jj cnt) (auxIdx jj lim))
    (stepMachine x L dc false false L.toWalkLayout.codeA L.toWalkLayout.codeT
      L.toWalkLayout.cnt L.toWalkLayout.cnt cc)

/-- Its advancing states: the walk's, then the final step's. -/
noncomputable def memberAdv {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (cc cnt lim : Fin rr) :
    (memberTM x L dc cc cnt lim).Q → Bool :=
  TM.seqAdv
    (TM.binaryForAdv
      (walkPairAdv rr tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
        L.toWalkLayout.res L.toWalkLayout.cnt L.toWalkLayout.cnt' wc dc
        L.toWalkLayout.codeA L.toWalkLayout.codeB (stepReg (r := rr) L false)
        (stepReg (r := rr) L true) (stepWidth L) L.toWalkLayout.stepBlocks (stepTargets jj rr)
        (auxIdx jj cc))
      (auxIdx jj cnt) (auxIdx jj lim))
    (walkStepAdv rr tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
      L.toWalkLayout.res L.toWalkLayout.cnt L.toWalkLayout.cnt wc false dc
      L.toWalkLayout.codeA L.toWalkLayout.codeT (stepReg (r := rr) L false) (stepWidth L)
      L.toWalkLayout.stepBlocks (stepTargets jj rr) (auxIdx jj cc))

/-- **The membership test respects the guess protocol**, so it may sit inside a nondeterministic
assembly. -/
theorem guessProtocol_memberTM {rr : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec) (cc cnt lim : Fin rr) :
    TM.GuessProtocol (memberTM x L dc cc cnt lim) (memberAdv x L dc cc cnt lim) :=
  TM.guessProtocol_seqTM
    (guessProtocol_walkLoopTM rr tm x.length S L.toWalkLayout.par L.toWalkLayout.mv
      L.toWalkLayout.dr L.toWalkLayout.res L.toWalkLayout.cnt L.toWalkLayout.cnt' dc
      L.toWalkLayout.codeA L.toWalkLayout.codeB (stepReg (r := rr) L false)
      (stepReg (r := rr) L true) (stepWidth L) L.toWalkLayout.stepBlocks wc (stepTargets jj rr)
      (auxIdx jj cc) (auxIdx jj cnt) (auxIdx jj lim) (auxIdx_ne_last cc) (auxIdx_ne_last cnt)
      (auxIdx_ne_last lim))
    (guessProtocol_walkStepTM rr tm x.length S L.toWalkLayout.par L.toWalkLayout.mv
      L.toWalkLayout.dr L.toWalkLayout.res L.toWalkLayout.cnt L.toWalkLayout.cnt wc false dc
      L.toWalkLayout.codeA L.toWalkLayout.codeT (stepReg (r := rr) L false) (stepWidth L)
      L.toWalkLayout.stepBlocks (stepTargets jj rr) (auxIdx jj cc) (auxIdx_ne_last cc))

/-! ### The test's contract

The last stage compares the third tuple against where the walk ended, so what it decides is
membership of *that* code — which the registers pin down, because a register tuple holds at most
one code. -/

/-- **A scanned tuple holds at most one code.** -/
theorem holdsCodeScan_inj {x : List Bool} {cols : ℕ → Fin (jj + 1) → Γ}
    {R : CodeRegs kk jj} {a b : Code tm.Q kk x.length S}
    (ha : HoldsCodeScan tm x S cols R a) (hb : HoldsCodeScan tm x S cols R b) : a = b := by
  obtain ⟨hast, hahd, hawk, haot⟩ := ha
  obtain ⟨hbst, hbhd, hbwk, hbot⟩ := hb
  have hst : a.1 = b.1 := by
    refine (qCodec tm.Q).enc_injective (hast.inj hbst ?_)
    rw [(qCodec tm.Q).enc_length, (qCodec tm.Q).enc_length]
  have hhd : a.2.1 = b.2.1 := by
    refine (finCodec (x.length + S + 2)).enc_injective (hahd.inj hbhd ?_)
    rw [(finCodec (x.length + S + 2)).enc_length, (finCodec (x.length + S + 2)).enc_length]
  have hwk : a.2.2.1 = b.2.2.1 := by
    funext i
    exact HoldsWindow.inj (hawk i) (hbwk i)
  have hot : a.2.2.2 = b.2.2.2 := HoldsWindow.inj haot hbot
  exact Prod.ext hst (Prod.ext hhd (Prod.ext hwk hot))

/-- And so at most one code with its tail zeros. -/
theorem holdsCodeTail_inj {x : List Bool} {cols : ℕ → Fin (jj + 1) → Γ}
    {j : ℕ → Fin (jj + 1)} {a b : Code tm.Q kk x.length S}
    (ha : HoldsCodeTail tm x S cols j a) (hb : HoldsCodeTail tm x S cols j b) : a = b :=
  holdsCodeScan_inj ha.1 hb.1

/-- **What the test carries into its last stage**: the walk's chain, and the third tuple still
holding the code under test. -/
def MemberChain {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (cOld : ℕ → Fin (jj + 1)) (g : ℕ → Bool) (s : ℕ)
    (cc : Fin r) (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) (u : Code tm.Q kk x.length S) :
    TM.TapePred (jj + 2 + r + 1) :=
  fun inp work out => WalkChain (r := r) x L cOld g s cc Wa Wt inp work out ∧
    ∀ p, p < kk + 3 → HoldsBits (fun q i => (work (walkReg i)).cells q) 0
      (L.toWalkLayout.codeT p) (codeBlockScan tm x S u p)

/-- **The last stage decides membership.** It is an ordinary walk stage, except that the tuple it
compares against is the third one — which it does not guess, so its bits come from the frame
rather than from `Complexity.exists_bits_guessed`. If the accumulator survives, the code the
stage ends on is one round past a code the walk reached; and since the third tuple holds both
that code and the one under test, they are equal. -/
theorem memberStep_chain (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (g : ℕ → Bool) (s : ℕ) (cc : Fin r) (B : ℕ)
    (hspace : ∀ c, tm.ReachesCfg (tm.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hwin : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x S c)
    (hB1 : 1 ≤ B) (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hwc : wc ≤ walkScanLen tm x.length S) (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ)
    (u : Code tm.Q kk x.length S) :
    (stepMachine x L dc false false L.toWalkLayout.codeA L.toWalkLayout.codeT
        L.toWalkLayout.cnt L.toWalkLayout.cnt cc).HoareTime
      (MemberChain (r := r) x L L.toWalkLayout.codeA g s cc Wa Wt u)
      (fun _ work _ => (work (auxIdx jj cc)).read = Γ.one →
        u ∈ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (s + 1))
      (stepTime x L r B) := by
  intro inp₀ W₀ out₀ hpre
  obtain ⟨⟨htapes, hcode⟩, huBits⟩ := hpre
  obtain ⟨c', t, htle, hreach, hhalt, htapes', hspare, hmono⟩ :=
    walkStep_tapes x L dc g false false L.toWalkLayout.codeA L.toWalkLayout.codeT
      L.toWalkLayout.cnt L.toWalkLayout.cnt s cc B hB1 hB Wa Wt inp₀ out₀ W₀ htapes
  refine ⟨c', t, htle, hreach, hhalt, fun haccOne => ?_⟩
  obtain ⟨a, ha, hinvA⟩ := hcode (hmono haccOne)
  have hcntW : wc ≤ stepWidth L L.toWalkLayout.cntIdx + 1 := by
    rw [stepWidth_scratch L _ L.toWalkLayout.cnt_scratch, L.width_cnt]
    omega
  have hbitsRaw : ∀ p, p < kk + 3 →
      HoldsBits (fun q i => stepCells L false W₀ i q) 0 (L.toWalkLayout.codeT p)
        (codeBlockScan tm x S u p) := by
    intro p hp q hq
    show stepCells L false W₀ (L.toWalkLayout.codeT p) (0 + q + 1) = _
    rw [congrFun (stepCells_codeT L false W₀ htapes.2.1 htapes.2.2.1 p hp) (0 + q + 1)]
    exact huBits p hp q hq
  obtain ⟨c'', t'', -, hreach'', hhalt'', hcond⟩ :=
    walkStep_sound x L dc g false false L.toWalkLayout.codeA L.toWalkLayout.codeT
      L.toWalkLayout.cnt L.toWalkLayout.cnt L.toWalkLayout.cntIdx L.toWalkLayout.cntIdx a s cc B
      hB1 hB (fun p hp => L.toWalkLayout.codeA_ne_res hp)
      (fun p hp => L.toWalkLayout.codeT_ne_res hp) L.toWalkLayout.cnt_ne_res
      L.toWalkLayout.cnt_ne_res L.toWalkLayout.cnt_scratch L.toWalkLayout.cnt_scratch rfl rfl
      hcntW hcntW
      (fun p hp p' hp' hc => L.toWalkLayout.stepIdx_ne_codeA p' p hp' hp
        (L.toWalkLayout.reg_inj _ _ (L.toWalkLayout.stepIdx_lt false p' hp')
          (L.toWalkLayout.codeA_lt p hp) (walkReg_inj hc).symm))
      (fun P => clampIn_deferred x S hspace hwin a s ha P) hwc inp₀ out₀ W₀
      (fun p => codeBlockScan tm x S u p) (fun p _ => codeBlockScan_length tm x S u p)
      hbitsRaw hinvA
  have huTail : HoldsCodeTail tm x S (fun q i => (c'.work (walkReg i)).cells q)
      L.toWalkLayout.codeT u := by
    refine holdsCodeTail_congr tm x S (fun q i => (W₀ (walkReg i)).cells q) _
      L.toWalkLayout.codeT u
      (holdsCodeTail_of_blocks tm x S (fun q i => (W₀ (walkReg i)).cells q)
        L.toWalkLayout.codeT u huBits) ?_
    exact fun p hp q => (htapes'.2.2.2.2.2.2.2.2.2.2 p hp q).trans
      (htapes.2.2.2.2.2.2.2.2.2.2 p hp q).symm
  have heq : c'' = c' := TM.reachesIn_halted_unique hreach'' hreach hhalt'' hhalt
  subst heq
  obtain ⟨-, b, hbStep, hbInv⟩ := hcond haccOne
  have hbu : b = u := holdsCodeTail_inj hbInv.2.2.2.2.1 huTail
  subst hbu
  rcases hbStep with rfl | hsucc
  · exact NTM.reachCodes_subset_succ _ s ha
  · exact (NTM.mem_reachCodes_succ_iff _ s b).mpr (Or.inr ⟨a, ha, hsucc⟩)

/-- **The membership test is sound.** Started on a frame that enters the walk loop, with the
third tuple holding a code `u`, an accepted run witnesses that `u` is reachable in `2 * N + 1`
rounds — which is what an enumeration over a round's codes needs of each candidate. -/
theorem memberTM_sound (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (dc : DirCodec) (g : ℕ → Bool) (cc cnt lim : Fin r) (hcnt : cnt ≠ cc) (hlim : lim ≠ cc)
    (hcl : cnt ≠ lim) (B : ℕ)
    (hspace : ∀ c, tm.ReachesCfg (tm.initCfg x) c → c.WithinDecisionSpace x.length S)
    (hwin : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x S c)
    (hB1 : 1 ≤ B) (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (hwc : wc ≤ walkScanLen tm x.length S) (N : ℕ) (u : Code tm.Q kk x.length S)
    (inp : Tape) (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (hpre : TM.BinaryForFrame (auxIdx jj cnt) (auxIdx jj lim) N
      (WalkChainP x L g cc (fun p q => (work (walkReg (L.toWalkLayout.codeT p))).cells q)) 0
      inp work out)
    (hu : ∀ p, p < kk + 3 → HoldsBits (fun q i => (work (walkReg i)).cells q) 0
      (L.toWalkLayout.codeT p) (codeBlockScan tm x S u p)) :
    ∃ (c' : Cfg (jj + 2 + r + 1) (memberTM x L dc cc cnt lim).Q) (t : ℕ),
      t ≤ TM.binaryForLoopTime (fun _ => stepTime x L r B + 1 + stepTime x L r B) N 0 N + 1
          + stepTime x L r B ∧
      (memberTM x L dc cc cnt lim).reachesIn t
        ⟨(memberTM x L dc cc cnt lim).qstart, inp, work, out⟩ c' ∧
      (memberTM x L dc cc cnt lim).halted c' ∧
      ((c'.work (auxIdx jj cc)).read = Γ.one →
        u ∈ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 1)) := by
  classical
  set Wt : ℕ → ℕ → Γ :=
    fun p q => (work (walkReg (L.toWalkLayout.codeT p))).cells q with hWt
  have hstep : (stepMachine x L dc false false L.toWalkLayout.codeA L.toWalkLayout.codeT
      L.toWalkLayout.cnt L.toWalkLayout.cnt cc).HoareTime
      (fun i w o => MemberChain (r := r) x L L.toWalkLayout.codeA g (2 * N) cc
        (fun c => w (auxIdx jj c)) Wt u i w o)
      (fun _ w _ => (w (auxIdx jj cc)).read = Γ.one →
        u ∈ NTM.reachCodes tm x S (cfgCode x.length S (tm.initCfg x)) (2 * N + 1))
      (stepTime x L r B) := by
    intro inp' work' out' hpre'
    exact memberStep_chain x L dc g (2 * N) cc B hspace hwin hB1 hB hwc
      (fun c => work' (auxIdx jj c)) Wt u inp' work' out' hpre'
  have htrans : ∀ inp' work' out',
      TM.BinaryForFrame (auxIdx jj cnt) (auxIdx jj lim) N (WalkChainP x L g cc Wt) N
        inp' work' out' →
      MemberChain (r := r) x L L.toWalkLayout.codeA g (2 * N) cc
        (fun c => TM.transitionTape (work' (auxIdx jj c))) Wt u (TM.transitionInput inp')
        (fun i => TM.transitionTape (work' i)) (TM.transitionTape out') := by
    intro inp' work' out' hmid
    obtain ⟨hinpT, hworkT, houtT⟩ :=
      walkTapes_transition_eq x L g (2 * N) cc (fun c => work' (auxIdx jj c)) Wt inp' work' out'
        hmid.1.1
    have hWa : (fun c => TM.transitionTape (work' (auxIdx jj c)))
        = fun c => work' (auxIdx jj c) := funext fun c => congrFun hworkT (auxIdx jj c)
    rw [hinpT, houtT, hWa, hworkT]
    refine ⟨hmid.1, fun p hp q hq => ?_⟩
    have hcell := codeT_of_binaryForFrame x L g cc cnt lim Wt N inp' work' out' hmid p hp
      (0 + q + 1)
    rw [hWt] at hcell
    exact hcell.trans (hu p hp q hq)
  exact TM.seqTM_hoareTime _ _
    (walkLoop_chain x L dc g cc cnt lim hcnt hlim hcl B hspace hwin hB1 hB hwc Wt N)
    htrans hstep inp work out hpre

end Complexity
