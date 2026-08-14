/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Composition.Nondeterministic
public import Complexitylib.Models.TuringMachine.Composition.Internal.FirstPhase
public import Complexitylib.Models.TuringMachine.Composition.Internal.Tail
public import Complexitylib.Models.TuringMachine.OutputBounds

/-!
# Deterministic prefix of the nondeterministic composition — proof internals

The branch-`false` projection of `NTM.compositionNTM tmF N` runs
deterministically from the initial configuration through the first
computation, the raw-output rewind, the copy onto the virtual-input tape,
and the virtual-input rewind, stopping at the rewind phase's halt state —
the last configuration before the branch-dependent seam into the placed
retargeted phase. Every step source on the way satisfies
`NTM.BranchesAgreeAt`, so the run is packaged as a `TM.ReachesInVia`
annotated run, ready for `NTM.trace_of_det_prefix`.

The main result is `NTM.compositionNTM_detPrefix_internal`, which also
records the boundary configuration's tape shape: the virtual-input tape
holds `f x` parked at head `1`, the second machine's scratch block and the
output are parked blanks, and every tape is start-invariant with head at
least `1`.
-/


public section

namespace Complexity

namespace NTM

variable {nf ng : ℕ}

/-- The boundary configuration at the end of the deterministic prefix:
    state at the virtual-input rewind's halt, virtual input `y` parked at
    head `1`, second scratch block and output parked blank, and every tape
    start-invariant with positive head. -/
@[expose] def DetPrefixBoundary (tmF : TM nf) (N : NTM ng) (y : List Bool)
    (E : Cfg (TM.compositionTapeCount nf ng) (compositionNTM tmF N).Q) : Prop :=
  E.state = Sum.inr (Sum.inr (Sum.inr (Sum.inl
    (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng)).qhalt))) ∧
  E.work (TM.compositionVirtualInputIdx nf ng) =
    (Tape.init (y.map Γ.ofBool)).move Dir3.right ∧
  (∀ j : Fin ng, E.work (TM.compositionSecondWorkIdx nf ng j) =
    (Tape.init []).move Dir3.right) ∧
  E.output = (Tape.init []).move Dir3.right ∧
  E.input.StartInvariant ∧ 1 ≤ E.input.head ∧
  (∀ i, (E.work i).StartInvariant ∧ 1 ≤ (E.work i).head)

/-- **Deterministic prefix of the composite.** From the initial
    configuration, the branch-`false` projection reaches a
    `DetPrefixBoundary` configuration for `y = f x` in at most
    `4 * TF |x| + 10` steps, with every step source satisfying
    `BranchesAgreeAt`. -/
theorem compositionNTM_detPrefix_internal (tmF : TM nf) (N : NTM ng)
    {f : List Bool → List Bool} {TF : ℕ → ℕ}
    (hF : tmF.ComputesInTime f TF) (x : List Bool) :
    ∃ (E : Cfg (TM.compositionTapeCount nf ng) (compositionNTM tmF N).Q) (t : ℕ),
      t ≤ 4 * TF x.length + 10 ∧
      ((compositionNTM tmF N).det false).ReachesInVia
        (compositionNTM tmF N).BranchesAgreeAt t
        ((compositionNTM tmF N).initCfg x) E ∧
      DetPrefixBoundary tmF N (f x) E := by
  classical
  obtain ⟨C, tA, htA, hreachA, hhaltA, hrawOutput, hrawHead, hvirtual,
      hscratch, hinputInv, hinputHead, hworkBoundary, houtputParked⟩ :=
    TM.compositionFirstTM_boundary_internal (nf := nf) tmF ng hF x
  have hrawVin : (TM.compositionRawOutputIdx nf ng) ≠ (TM.compositionVirtualInputIdx nf ng) :=
      TM.compositionRawOutputIdx_ne_virtualInputIdx nf ng
  have hread_ns : ∀ t : Tape, t.StartInvariant → 1 ≤ t.head → t.read ≠ Γ.start :=
    fun t hinv hh => hinv.2 t.head hh
  have houtInv : (TM.transitionTape C.output).StartInvariant := by
    rw [houtputParked]
    exact Tape.StartInvariant.init_nil.move Dir3.right
  have houtHead : 1 ≤ (TM.transitionTape C.output).head := by
    rw [houtputParked]
    simp [Tape.move]
  -- ── Rewind the (TM.compositionRawOutputIdx nf ng)-output tape. ──
  obtain ⟨c₁, t₁, ht₁, hreach₁, hhalt₁, hc₁Head, hc₁Frame⟩ :=
    TM.rewindWorkTM_hoareTime_frame (TM.compositionRawOutputIdx nf ng) (tA + 1)
      (P := fun inp' work' out' =>
        (work' (TM.compositionRawOutputIdx nf ng)).cells = (TM.transitionTape (C.work
            (TM.compositionRawOutputIdx nf ng))).cells ∧
        inp' = TM.transitionInput C.input ∧
        out' = TM.transitionTape C.output ∧
        ∀ i, i ≠ (TM.compositionRawOutputIdx nf ng) → work' i = TM.transitionTape (C.work i))
      (by
        intro inp₀ work₀ out₀ inp' work' out' hframe hcells _hhead hother hinp'
          houtCells houtHead'
        rcases hframe with ⟨hrawCells₀, hinp₀, hout₀, hwork₀⟩
        have hout' : out' = out₀ := Tape.ext houtHead' houtCells
        exact ⟨hcells.trans hrawCells₀, hinp'.trans hinp₀,
          hout'.trans hout₀, fun i hi => (hother i hi).trans (hwork₀ i hi)⟩)
      (TM.transitionInput C.input) (fun i => TM.transitionTape (C.work i))
      (TM.transitionTape C.output)
      ⟨(hworkBoundary (TM.compositionRawOutputIdx nf ng)).1.1, (hworkBoundary
          (TM.compositionRawOutputIdx nf ng)).1.2, hrawHead,
        hread_ns _ hinputInv hinputHead, hread_ns _ houtInv houtHead, houtHead,
        (fun i hi => ⟨hread_ns _ (hworkBoundary i).1 (hworkBoundary i).2,
          (hworkBoundary i).2⟩),
        ⟨rfl, rfl, rfl, fun _ _ => rfl⟩⟩
  rcases hc₁Frame with ⟨hc₁RawCells, hc₁Input, hc₁Output, hc₁Other⟩
  have hc₁Raw : c₁.work (TM.compositionRawOutputIdx nf ng) =
      { head := 1, cells := (TM.transitionTape (C.work (TM.compositionRawOutputIdx nf ng))).cells }
          :=
    Tape.ext hc₁Head hc₁RawCells
  have hsourceInv : Tape.StartInvariant
      { head := 1, cells := (TM.transitionTape (C.work (TM.compositionRawOutputIdx nf ng))).cells }
          :=
    ⟨(hworkBoundary (TM.compositionRawOutputIdx nf ng)).1.1, fun j hj => (hworkBoundary
        (TM.compositionRawOutputIdx nf ng)).1.2 j hj⟩
  have hsourceOutput : Tape.HasOutput
      { head := 1, cells := (TM.transitionTape (C.work (TM.compositionRawOutputIdx nf ng))).cells }
          (f x) :=
    (Tape.hasOutput_congr (by rfl) (f x)).mpr hrawOutput
  have hc₁WorkStable : ∀ i, (c₁.work i).StartInvariant ∧ 1 ≤ (c₁.work i).head := by
    intro i
    by_cases hi : i = (TM.compositionRawOutputIdx nf ng)
    · subst i
      rw [hc₁Raw]
      exact ⟨hsourceInv, by simp⟩
    · rw [hc₁Other i hi]
      exact hworkBoundary i
  have hc₁InputTr : TM.transitionInput c₁.input = c₁.input := by
    rw [hc₁Input]
    exact TM.transitionInput_eq_self (hread_ns _ hinputInv hinputHead)
  have hc₁OutputTr : TM.transitionTape c₁.output = c₁.output := by
    rw [hc₁Output]
    exact TM.transitionTape_eq_self (hread_ns _ houtInv houtHead)
  have hc₁WorkTr : ∀ i, TM.transitionTape (c₁.work i) = c₁.work i := by
    intro i
    exact TM.transitionTape_eq_self
      (hread_ns _ (hc₁WorkStable i).1 (hc₁WorkStable i).2)
  -- ── Copy the delimited output onto the virtual-input tape. ──
  obtain ⟨c₂, t₂, ht₂, hreach₂, hhalt₂, hc₂RawCells, hc₂RawHead, hc₂RawOutput,
      hc₂VinPrefix, hc₂Vin0, hc₂Frame⟩ :=
    TM.copyWorkToWorkTM_hoareTime_frame_of_hasOutput (TM.compositionRawOutputIdx nf ng)
        (TM.compositionVirtualInputIdx nf ng) hrawVin (f x)
      { head := 1, cells := (TM.transitionTape (C.work (TM.compositionRawOutputIdx nf ng))).cells }
      (P := fun inp' work' out' =>
        inp' = TM.transitionInput C.input ∧
        out' = TM.transitionTape C.output ∧
        ∀ i, i ≠ (TM.compositionRawOutputIdx nf ng) → i ≠ (TM.compositionVirtualInputIdx nf ng) →
            work' i = TM.transitionTape (C.work i))
      (by
        intro inp₀ work₀ out₀ inp' work' out' hframe _hsrcCells _hsrcHead
          _hsrcOutput _hdstPrefix _hdst0 hinp' hout' hother
        rcases hframe with ⟨hinp₀, hout₀, hwork₀⟩
        exact ⟨hinp'.trans hinp₀, hout'.trans hout₀,
          fun i hiRaw hiVin => (hother i hiRaw hiVin).trans (hwork₀ i hiRaw hiVin)⟩)
      (TM.transitionInput c₁.input) (fun i => TM.transitionTape (c₁.work i))
      (TM.transitionTape c₁.output)
      (by
        refine ⟨?_, rfl, hsourceOutput, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · show TM.transitionTape (c₁.work (TM.compositionRawOutputIdx nf ng)) = _
          rw [hc₁WorkTr (TM.compositionRawOutputIdx nf ng), hc₁Raw]
        · show TM.transitionTape (c₁.work (TM.compositionVirtualInputIdx nf ng)) = (Tape.init
            []).move Dir3.right
          rw [hc₁WorkTr (TM.compositionVirtualInputIdx nf ng), hc₁Other
              (TM.compositionVirtualInputIdx nf ng) (Ne.symm hrawVin), hvirtual]
        · rw [hc₁InputTr, hc₁Input]
          exact hread_ns _ hinputInv hinputHead
        · rw [hc₁OutputTr, hc₁Output]
          exact hread_ns _ houtInv houtHead
        · rw [hc₁OutputTr, hc₁Output]
          exact houtHead
        · intro i hiRaw hiVin
          show (TM.transitionTape (c₁.work i)).read ≠ Γ.start ∧
            1 ≤ (TM.transitionTape (c₁.work i)).head
          rw [hc₁WorkTr i]
          exact ⟨hread_ns _ (hc₁WorkStable i).1 (hc₁WorkStable i).2,
            (hc₁WorkStable i).2⟩
        · rw [hc₁InputTr, hc₁Input]
        · rw [hc₁OutputTr, hc₁Output]
        · intro i hiRaw hiVin
          show TM.transitionTape (c₁.work i) = TM.transitionTape (C.work i)
          rw [hc₁WorkTr i, hc₁Other i hiRaw])
  rcases hc₂Frame with ⟨hc₂Input, hc₂Output, hc₂Other⟩
  have hc₂VinCells : (c₂.work (TM.compositionVirtualInputIdx nf ng)).cells = (Tape.init ((f x).map
      Γ.ofBool)).cells :=
    hc₂VinPrefix.cells_eq_init hc₂Vin0
  have hc₂RawInv : (c₂.work (TM.compositionRawOutputIdx nf ng)).StartInvariant := by
    constructor
    · rw [hc₂RawCells]
      exact hsourceInv.1
    · intro j hj
      rw [hc₂RawCells]
      exact hsourceInv.2 j hj
  have hc₂VinInv : (c₂.work (TM.compositionVirtualInputIdx nf ng)).StartInvariant := by
    constructor
    · rw [hc₂VinCells]
      rfl
    · intro j hj
      rw [hc₂VinCells]
      exact Tape.init_ofBool_cells_ne_start (f x) j hj
  have hc₂WorkStable : ∀ i, (c₂.work i).StartInvariant ∧ 1 ≤ (c₂.work i).head := by
    intro i
    by_cases hiRaw : i = (TM.compositionRawOutputIdx nf ng)
    · subst i
      exact ⟨hc₂RawInv, by rw [hc₂RawHead]; omega⟩
    by_cases hiVin : i = (TM.compositionVirtualInputIdx nf ng)
    · subst i
      refine ⟨hc₂VinInv, ?_⟩
      rw [hc₂VinPrefix.1]
      omega
    · rw [hc₂Other i hiRaw hiVin]
      exact hworkBoundary i
  have hc₂InputTr : TM.transitionInput c₂.input = c₂.input := by
    rw [hc₂Input]
    exact TM.transitionInput_eq_self (hread_ns _ hinputInv hinputHead)
  have hc₂OutputTr : TM.transitionTape c₂.output = c₂.output := by
    rw [hc₂Output]
    exact TM.transitionTape_eq_self (hread_ns _ houtInv houtHead)
  have hc₂WorkTr : ∀ i, TM.transitionTape (c₂.work i) = c₂.work i := by
    intro i
    exact TM.transitionTape_eq_self
      (hread_ns _ (hc₂WorkStable i).1 (hc₂WorkStable i).2)
  -- ── Rewind the virtual-input tape. ──
  obtain ⟨c₃, t₃, ht₃, hreach₃, hhalt₃, hc₃Head, hc₃Frame⟩ :=
    TM.rewindWorkTM_hoareTime_frame (TM.compositionVirtualInputIdx nf ng) ((f x).length + 1)
      (P := fun inp' work' out' =>
        (work' (TM.compositionVirtualInputIdx nf ng)).cells = (Tape.init ((f x).map Γ.ofBool)).cells
            ∧
        inp' = TM.transitionInput C.input ∧
        out' = TM.transitionTape C.output ∧
        ∀ i, i ≠ (TM.compositionVirtualInputIdx nf ng) → work' i = c₂.work i)
      (by
        intro inp₀ work₀ out₀ inp' work' out' hframe hcells _hhead hother hinp'
          houtCells houtHead'
        rcases hframe with ⟨hvinCells₀, hinp₀, hout₀, hwork₀⟩
        have hout' : out' = out₀ := Tape.ext houtHead' houtCells
        exact ⟨hcells.trans hvinCells₀, hinp'.trans hinp₀,
          hout'.trans hout₀, fun i hi => (hother i hi).trans (hwork₀ i hi)⟩)
      (TM.transitionInput c₂.input) (fun i => TM.transitionTape (c₂.work i))
      (TM.transitionTape c₂.output)
      (by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · show (TM.transitionTape (c₂.work (TM.compositionVirtualInputIdx nf ng))).cells 0 = Γ.start
          rw [hc₂WorkTr (TM.compositionVirtualInputIdx nf ng)]
          exact hc₂VinInv.1
        · intro j hj
          show (TM.transitionTape (c₂.work (TM.compositionVirtualInputIdx nf ng))).cells j ≠ Γ.start
          rw [hc₂WorkTr (TM.compositionVirtualInputIdx nf ng)]
          exact hc₂VinInv.2 j hj
        · show (TM.transitionTape (c₂.work (TM.compositionVirtualInputIdx nf ng))).head ≤ (f
            x).length + 1
          rw [hc₂WorkTr (TM.compositionVirtualInputIdx nf ng), hc₂VinPrefix.1]
        · rw [hc₂InputTr, hc₂Input]
          exact hread_ns _ hinputInv hinputHead
        · rw [hc₂OutputTr, hc₂Output]
          exact hread_ns _ houtInv houtHead
        · rw [hc₂OutputTr, hc₂Output]
          exact houtHead
        · intro i hi
          show (TM.transitionTape (c₂.work i)).read ≠ Γ.start ∧
            1 ≤ (TM.transitionTape (c₂.work i)).head
          rw [hc₂WorkTr i]
          exact ⟨hread_ns _ (hc₂WorkStable i).1 (hc₂WorkStable i).2,
            (hc₂WorkStable i).2⟩
        · refine ⟨?_, ?_, ?_, ?_⟩
          · show (TM.transitionTape (c₂.work (TM.compositionVirtualInputIdx nf ng))).cells =
              (Tape.init ((f x).map Γ.ofBool)).cells
            rw [hc₂WorkTr (TM.compositionVirtualInputIdx nf ng)]
            exact hc₂VinCells
          · rw [hc₂InputTr, hc₂Input]
          · rw [hc₂OutputTr, hc₂Output]
          · intro i hi
            show TM.transitionTape (c₂.work i) = c₂.work i
            exact hc₂WorkTr i)
  rcases hc₃Frame with ⟨hc₃VinCells, hc₃Input, hc₃Output, hc₃Other⟩
  -- ── Lift the phase runs into the composite as an annotated run. ──
  have hcommA : ∀ {c c' : Cfg (TM.compositionTapeCount nf ng) (TM.compositionFirstTM tmF ng).Q},
      (TM.compositionFirstTM tmF ng).step c = some c' →
      ((compositionNTM tmF N).det false).step ((TM.phase1Wrap (TM.compositionFirstTM tmF ng)
          (TM.compositionTailTM nf ng (N.det false))) c) = some ((TM.phase1Wrap
          (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng (N.det false))) c') :=
    fun {c c'} h => TM.seqTM_phase1_step (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng
        (N.det false)) h
  have hcomm₁ : ∀ {c c' : Cfg (TM.compositionTapeCount nf ng) (TM.rewindWorkTM
      (TM.compositionRawOutputIdx nf ng)).Q},
      (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng)).step c = some c' →
      ((compositionNTM tmF N).det false).step ((fun c => TM.phase2Wrap (TM.compositionFirstTM tmF
          ng) (TM.compositionTailTM nf ng (N.det false)) (TM.phase1Wrap (TM.rewindWorkTM
          (TM.compositionRawOutputIdx nf ng)) (TM.seqTM (TM.copyWorkToWorkTM
          (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM
          (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det
          false)))) c)) c) = some ((fun c => TM.phase2Wrap (TM.compositionFirstTM tmF ng)
          (TM.compositionTailTM nf ng (N.det false)) (TM.phase1Wrap (TM.rewindWorkTM
          (TM.compositionRawOutputIdx nf ng)) (TM.seqTM (TM.copyWorkToWorkTM
          (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM
          (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det
          false)))) c)) c') :=
    fun {c c'} h => TM.seqTM_phase2_step (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng
        (N.det false)) (TM.seqTM_phase1_step (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng))
        (TM.seqTM (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng)
        (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM (TM.rewindWorkTM
        (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det false)))) h)
  have hcomm₂ : ∀ {c c' : Cfg (TM.compositionTapeCount nf ng) (TM.copyWorkToWorkTM
      (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf ng)).Q},
      (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf
          ng)).step c = some c' →
      ((compositionNTM tmF N).det false).step ((fun c => TM.phase2Wrap (TM.compositionFirstTM tmF
          ng) (TM.compositionTailTM nf ng (N.det false)) (TM.phase2Wrap (TM.rewindWorkTM
          (TM.compositionRawOutputIdx nf ng)) (TM.seqTM (TM.copyWorkToWorkTM
          (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM
          (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det
          false)))) (TM.phase1Wrap (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng)
          (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM (TM.rewindWorkTM
          (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det false))) c))) c)
          = some ((fun c => TM.phase2Wrap (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng
          (N.det false)) (TM.phase2Wrap (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng))
          (TM.seqTM (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng)
          (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM (TM.rewindWorkTM
          (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det false))))
          (TM.phase1Wrap (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng)
          (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM (TM.rewindWorkTM
          (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det false))) c))) c')
          :=
    fun {c c'} h => TM.seqTM_phase2_step (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng
        (N.det false)) (TM.seqTM_phase2_step (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng))
        (TM.seqTM (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng)
        (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM (TM.rewindWorkTM
        (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det false))))
        (TM.seqTM_phase1_step (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng)
        (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM (TM.rewindWorkTM
        (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det false))) h))
  have hcomm₃ : ∀ {c c' : Cfg (TM.compositionTapeCount nf ng) (TM.rewindWorkTM
      (TM.compositionVirtualInputIdx nf ng)).Q},
      (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng)).step c = some c' →
      ((compositionNTM tmF N).det false).step ((fun c => TM.phase2Wrap (TM.compositionFirstTM tmF
          ng) (TM.compositionTailTM nf ng (N.det false)) (TM.phase2Wrap (TM.rewindWorkTM
          (TM.compositionRawOutputIdx nf ng)) (TM.seqTM (TM.copyWorkToWorkTM
          (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM
          (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det
          false)))) (TM.phase2Wrap (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng)
          (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM (TM.rewindWorkTM
          (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det false)))
          (TM.phase1Wrap (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
          (TM.compositionSecondTM nf (N.det false)) c)))) c) = some ((fun c => TM.phase2Wrap
          (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng (N.det false)) (TM.phase2Wrap
          (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng)) (TM.seqTM (TM.copyWorkToWorkTM
          (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM
          (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det
          false)))) (TM.phase2Wrap (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng)
          (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM (TM.rewindWorkTM
          (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det false)))
          (TM.phase1Wrap (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
          (TM.compositionSecondTM nf (N.det false)) c)))) c') :=
    fun {c c'} h => TM.seqTM_phase2_step (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng
        (N.det false)) (TM.seqTM_phase2_step (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng))
        (TM.seqTM (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng)
        (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM (TM.rewindWorkTM
        (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det false))))
        (TM.seqTM_phase2_step (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng)
        (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM (TM.rewindWorkTM
        (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det false)))
        (TM.seqTM_phase1_step (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
        (TM.compositionSecondTM nf (N.det false)) h)))
  have hViaA : ((compositionNTM tmF N).det false).ReachesInVia
      (compositionNTM tmF N).BranchesAgreeAt tA
      (TM.phase1Wrap (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng (N.det false))
          ((TM.compositionFirstTM tmF ng).initCfg x)) (TM.phase1Wrap (TM.compositionFirstTM tmF ng)
          (TM.compositionTailTM nf ng (N.det false)) C) :=
    TM.reachesInVia_of_stepCommute (tm₂ := ((compositionNTM tmF N).det false)) (tm₁ :=
        (tmF.compositionFirstTM ng)) (TM.phase1Wrap (TM.compositionFirstTM tmF ng)
        (TM.compositionTailTM nf ng (N.det false)))
      (fun {c _} _ => compositionNTM_branchesAgreeAt_first tmF N _ rfl)
      (fun {c c'} h => hcommA h) hreachA
  have hseam₁ : ((compositionNTM tmF N).det false).ReachesInVia
      (compositionNTM tmF N).BranchesAgreeAt 1
      (TM.phase1Wrap (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng (N.det false)) C)
      (TM.phase2Wrap (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng (N.det false))
        { state := (TM.compositionTailTM nf ng (N.det false)).qstart, input := TM.transitionInput
            C.input,
          work := fun i => TM.transitionTape (C.work i),
          output := TM.transitionTape C.output }) :=
    .step (compositionNTM_branchesAgreeAt_first tmF N _ rfl)
      (TM.seqTM_transition_step (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng (N.det
          false)) hhaltA) .zero
  have hVia₁ : ((compositionNTM tmF N).det false).ReachesInVia
      (compositionNTM tmF N).BranchesAgreeAt t₁
      (TM.phase2Wrap (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng (N.det false))
          (TM.phase1Wrap (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng)) (TM.seqTM
          (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf
          ng)) (TM.seqTM (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
          (TM.compositionSecondTM nf (N.det false))))
        { state := (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng)).qstart, input :=
            TM.transitionInput C.input,
          work := fun i => TM.transitionTape (C.work i),
          output := TM.transitionTape C.output }))
      (TM.phase2Wrap (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng (N.det false))
          (TM.phase1Wrap (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng)) (TM.seqTM
          (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf
          ng)) (TM.seqTM (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
          (TM.compositionSecondTM nf (N.det false)))) c₁)) :=
    TM.reachesInVia_of_stepCommute (tm₂ := ((compositionNTM tmF N).det false)) (tm₁ :=
        (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng)))
      (fun c => TM.phase2Wrap (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng (N.det
          false)) (TM.phase1Wrap (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng)) (TM.seqTM
          (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf
          ng)) (TM.seqTM (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
          (TM.compositionSecondTM nf (N.det false)))) c))
      (fun {c _} _ => compositionNTM_branchesAgreeAt_rewindRaw tmF N _ rfl)
      (fun {c c'} h => hcomm₁ h) hreach₁
  have hseam₂ : ((compositionNTM tmF N).det false).ReachesInVia
      (compositionNTM tmF N).BranchesAgreeAt 1
      (TM.phase2Wrap (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng (N.det false))
          (TM.phase1Wrap (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng)) (TM.seqTM
          (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf
          ng)) (TM.seqTM (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
          (TM.compositionSecondTM nf (N.det false)))) c₁))
      (TM.phase2Wrap (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng (N.det false))
          (TM.phase2Wrap (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng)) (TM.seqTM
          (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf
          ng)) (TM.seqTM (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
          (TM.compositionSecondTM nf (N.det false))))
        { state := (TM.seqTM (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng)
            (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM (TM.rewindWorkTM
            (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det
            false)))).qstart, input := TM.transitionInput c₁.input,
          work := fun i => TM.transitionTape (c₁.work i),
          output := TM.transitionTape c₁.output })) :=
    .step (compositionNTM_branchesAgreeAt_rewindRaw tmF N _ rfl)
      (TM.seqTM_phase2_step (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng (N.det
          false)) (TM.seqTM_transition_step (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng))
          (TM.seqTM (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng)
          (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM (TM.rewindWorkTM
          (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det false))))
          hhalt₁)) .zero
  have hVia₂ : ((compositionNTM tmF N).det false).ReachesInVia
      (compositionNTM tmF N).BranchesAgreeAt t₂
      (TM.phase2Wrap (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng (N.det false))
          (TM.phase2Wrap (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng)) (TM.seqTM
          (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf
          ng)) (TM.seqTM (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
          (TM.compositionSecondTM nf (N.det false)))) (TM.phase1Wrap (TM.copyWorkToWorkTM
          (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM
          (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det
          false)))
        { state := (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng)
            (TM.compositionVirtualInputIdx nf ng)).qstart, input := TM.transitionInput c₁.input,
          work := fun i => TM.transitionTape (c₁.work i),
          output := TM.transitionTape c₁.output })))
      (TM.phase2Wrap (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng (N.det false))
          (TM.phase2Wrap (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng)) (TM.seqTM
          (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf
          ng)) (TM.seqTM (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
          (TM.compositionSecondTM nf (N.det false)))) (TM.phase1Wrap (TM.copyWorkToWorkTM
          (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM
          (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det
          false))) c₂))) :=
    TM.reachesInVia_of_stepCommute (tm₂ := ((compositionNTM tmF N).det false)) (tm₁ :=
        (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf
        ng)))
      (fun c => TM.phase2Wrap (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng (N.det
          false)) (TM.phase2Wrap (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng)) (TM.seqTM
          (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf
          ng)) (TM.seqTM (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
          (TM.compositionSecondTM nf (N.det false)))) (TM.phase1Wrap (TM.copyWorkToWorkTM
          (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM
          (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det
          false))) c)))
      (fun {c _} _ => compositionNTM_branchesAgreeAt_copy tmF N _ rfl)
      (fun {c c'} h => hcomm₂ h) hreach₂
  have hseam₃ : ((compositionNTM tmF N).det false).ReachesInVia
      (compositionNTM tmF N).BranchesAgreeAt 1
      (TM.phase2Wrap (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng (N.det false))
          (TM.phase2Wrap (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng)) (TM.seqTM
          (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf
          ng)) (TM.seqTM (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
          (TM.compositionSecondTM nf (N.det false)))) (TM.phase1Wrap (TM.copyWorkToWorkTM
          (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM
          (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det
          false))) c₂)))
      (TM.phase2Wrap (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng (N.det false))
          (TM.phase2Wrap (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng)) (TM.seqTM
          (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf
          ng)) (TM.seqTM (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
          (TM.compositionSecondTM nf (N.det false)))) (TM.phase2Wrap (TM.copyWorkToWorkTM
          (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM
          (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det
          false)))
        { state := (TM.seqTM (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
            (TM.compositionSecondTM nf (N.det false))).qstart, input := TM.transitionInput c₂.input,
          work := fun i => TM.transitionTape (c₂.work i),
          output := TM.transitionTape c₂.output }))) :=
    .step (compositionNTM_branchesAgreeAt_copy tmF N _ rfl)
      (TM.seqTM_phase2_step (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng (N.det
          false)) (TM.seqTM_phase2_step (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng))
          (TM.seqTM (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng)
          (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM (TM.rewindWorkTM
          (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det false))))
        (TM.seqTM_transition_step (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng)
            (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM (TM.rewindWorkTM
            (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det false)))
            hhalt₂))) .zero
  have hVia₃ : ((compositionNTM tmF N).det false).ReachesInVia
      (compositionNTM tmF N).BranchesAgreeAt t₃
      (TM.phase2Wrap (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng (N.det false))
          (TM.phase2Wrap (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng)) (TM.seqTM
          (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf
          ng)) (TM.seqTM (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
          (TM.compositionSecondTM nf (N.det false)))) (TM.phase2Wrap (TM.copyWorkToWorkTM
          (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM
          (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det
          false)))
        (TM.phase1Wrap (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
            (TM.compositionSecondTM nf (N.det false))
          { state := (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng)).qstart, input :=
              TM.transitionInput c₂.input,
            work := fun i => TM.transitionTape (c₂.work i),
            output := TM.transitionTape c₂.output }))))
      (TM.phase2Wrap (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng (N.det false))
          (TM.phase2Wrap (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng)) (TM.seqTM
          (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf
          ng)) (TM.seqTM (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
          (TM.compositionSecondTM nf (N.det false)))) (TM.phase2Wrap (TM.copyWorkToWorkTM
          (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM
          (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det
          false)))
        (TM.phase1Wrap (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
            (TM.compositionSecondTM nf (N.det false)) c₃)))) :=
    TM.reachesInVia_of_stepCommute (tm₂ := ((compositionNTM tmF N).det false)) (tm₁ :=
        (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng)))
      (fun c => TM.phase2Wrap (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng (N.det
          false)) (TM.phase2Wrap (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng)) (TM.seqTM
          (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf
          ng)) (TM.seqTM (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
          (TM.compositionSecondTM nf (N.det false)))) (TM.phase2Wrap (TM.copyWorkToWorkTM
          (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM
          (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det
          false)))
        (TM.phase1Wrap (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
            (TM.compositionSecondTM nf (N.det false)) c))))
      (fun {c _} h => compositionNTM_branchesAgreeAt_rewindVirtual tmF N _
        (TM.state_ne_qhalt_of_step h) rfl)
      (fun {c c'} h => hcomm₃ h) hreach₃
  -- ── Assemble the run and the boundary description. ──
  refine ⟨TM.phase2Wrap (TM.compositionFirstTM tmF ng) (TM.compositionTailTM nf ng (N.det false))
      (TM.phase2Wrap (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng)) (TM.seqTM
      (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng) (TM.compositionVirtualInputIdx nf ng))
      (TM.seqTM (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf
      (N.det false)))) (TM.phase2Wrap (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng)
      (TM.compositionVirtualInputIdx nf ng)) (TM.seqTM (TM.rewindWorkTM
      (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM nf (N.det false)))
      (TM.phase1Wrap (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng)) (TM.compositionSecondTM
          nf (N.det false)) c₃))), tA + 1 + t₁ + 1 + t₂ + 1 + t₃, ?_, ?_, ?_⟩
  · have hy_le : (f x).length ≤ TF x.length := hF.output_length_le x
    omega
  · exact ((((((hViaA.trans hseam₁).trans hVia₁).trans hseam₂).trans
      hVia₂).trans hseam₃).trans hVia₃)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show Sum.inr (Sum.inr (Sum.inr (Sum.inl c₃.state))) = _
      rw [hhalt₃]
    · show c₃.work (TM.compositionVirtualInputIdx nf ng) = (Tape.init ((f x).map Γ.ofBool)).move
        Dir3.right
      refine Tape.ext ?_ ?_
      · rw [hc₃Head]
        simp [Tape.move]
      · rw [hc₃VinCells]
        simp [Tape.move]
    · intro j
      show c₃.work (TM.compositionSecondWorkIdx nf ng j) =
        (Tape.init []).move Dir3.right
      have hjRaw : TM.compositionSecondWorkIdx nf ng j ≠ (TM.compositionRawOutputIdx nf ng) := by
        intro h
        have := congrArg Fin.val h
        simp only [TM.compositionSecondWorkIdx_val, TM.compositionRawOutputIdx_val] at this
        omega
      have hjVin : TM.compositionSecondWorkIdx nf ng j ≠ (TM.compositionVirtualInputIdx nf ng) := by
        intro h
        have := congrArg Fin.val h
        simp only [TM.compositionSecondWorkIdx_val, TM.compositionVirtualInputIdx_val] at this
        omega
      rw [hc₃Other _ hjVin, hc₂Other _ hjRaw hjVin]
      exact hscratch j
    · show c₃.output = (Tape.init []).move Dir3.right
      rw [hc₃Output, houtputParked]
    · show c₃.input.StartInvariant
      rw [hc₃Input]
      exact hinputInv
    · show 1 ≤ c₃.input.head
      rw [hc₃Input]
      exact hinputHead
    · intro i
      show (c₃.work i).StartInvariant ∧ 1 ≤ (c₃.work i).head
      by_cases hi : i = (TM.compositionVirtualInputIdx nf ng)
      · subst i
        constructor
        · constructor
          · rw [hc₃VinCells]
            rfl
          · intro j hj
            rw [hc₃VinCells]
            exact Tape.init_ofBool_cells_ne_start (f x) j hj
        · omega
      · rw [hc₃Other i hi]
        exact hc₂WorkStable i

end NTM

end Complexity
