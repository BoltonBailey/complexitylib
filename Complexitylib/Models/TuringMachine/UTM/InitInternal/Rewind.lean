import Complexitylib.Models.TuringMachine.UTM.Helpers
import Complexitylib.Models.TuringMachine.UTM.HelpersInternal
import Complexitylib.Models.TuringMachine.UTM.SimConfig.Defs
import Complexitylib.Models.TuringMachine.Hoare.Defs
import Complexitylib.Models.TuringMachine.Hoare

/-!
# UTM Initialization: proof internals

Frame-preserving rewind lemmas used to compose the final rewind phase
of `initTM`.  Each rewind brings one work tape head to cell 1 while
leaving every other tape (input, output, and remaining work tapes)
unchanged and preserving `WorkTapesWF`.

## Main results

- `rewindWorkTM_hoareTime_frame` — general frame-preserving rewind
- `rewindDesc_hoareTime` — rewind work tape 0 with frame
- `rewindScratch_hoareTime` — rewind work tape 3 with frame
- `rewindAll_hoareTime` — compose 4 rewinds (tapes 0,1,2,3)
-/

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Tape helpers
-- ════════════════════════════════════════════════════════════════════════

private theorem tape_move_cells' (t : Tape) (d : Dir3) :
    (t.move d).cells = t.cells := by cases d <;> rfl

private theorem readBackWrite_toΓ_eq' {g : Γ} (h : g ≠ Γ.start) :
    (readBackWrite g).toΓ = g := by cases g <;> simp_all [readBackWrite, Γw.toΓ]

/-- A tape with head ≥ 1 and no ▷ at cells ≥ 1 is unchanged by
    `writeAndMove (readBackWrite t.read).toΓ (idleDir t.read)`. -/
private theorem tape_idle_stable (t : Tape)
    (hhead : t.head ≥ 1)
    (hns : ∀ j, j ≥ 1 → t.cells j ≠ Γ.start) :
    t.writeAndMove (readBackWrite t.read).toΓ (idleDir t.read) = t := by
  have hread : t.read ≠ Γ.start := by
    simp only [Tape.read]; exact hns t.head hhead
  simp only [Tape.writeAndMove, idleDir, hread, ↓reduceIte, Tape.move,
    readBackWrite_toΓ_eq' hread, Tape.write]
  split
  · omega
  · simp only [Tape.read, Function.update_eq_self]

/-- Input tape is unchanged by `move (idleDir t.read)` when head ≥ 1 and
    no ▷ at cells ≥ 1. -/
private theorem input_idle_stable (t : Tape)
    (hhead : t.head ≥ 1)
    (hns : ∀ j, j ≥ 1 → t.cells j ≠ Γ.start) :
    t.move (idleDir t.read) = t := by
  have hread : t.read ≠ Γ.start := by
    simp only [Tape.read]; exact hns t.head hhead
  simp only [idleDir, hread, ↓reduceIte, Tape.move]

-- ════════════════════════════════════════════════════════════════════════
-- Frame-preserving rewind loop
-- ════════════════════════════════════════════════════════════════════════

/-- An "envelope" predicate for the init rewind phase: all tapes are
    well-formed (cell 0 = ▷, cells ≥ 1 ≠ ▷), all heads ≥ 1. -/
def InitEnvelope (inp : Tape) (work : Fin 4 → Tape) (out : Tape) : Prop :=
  inp.cells 0 = Γ.start ∧
  (∀ j, j ≥ 1 → inp.cells j ≠ Γ.start) ∧
  inp.head ≥ 1 ∧
  WorkTapesWF work ∧
  (∀ i, (work i).head ≥ 1) ∧
  out.cells 0 = Γ.start ∧
  (∀ j, j ≥ 1 → out.cells j ≠ Γ.start) ∧
  out.head ≥ 1

/-- Frame-preserving rewind loop: from `moveLeft` state with target tape head
    at position `h`, reach `moveRight` state in `h + 1` steps.
    Target tape: head = 1, cells preserved.
    All other tapes: completely unchanged. -/
private theorem rewindWorkTM_rewind_loop_frame (idx : Fin 4) :
    ∀ (h : ℕ) (c : Cfg 4 (rewindWorkTM idx).Q),
    c.state = RewindPhase.moveLeft →
    (c.work idx).cells 0 = Γ.start →
    (∀ j, j ≥ 1 → (c.work idx).cells j ≠ Γ.start) →
    (c.work idx).head = h →
    -- Frame conditions: other tapes are well-formed with head ≥ 1
    (∀ j : Fin 4, j ≠ idx →
      (c.work j).cells 0 = Γ.start ∧
      (∀ p, p ≥ 1 → (c.work j).cells p ≠ Γ.start) ∧
      (c.work j).head ≥ 1) →
    c.input.cells 0 = Γ.start ∧
    (∀ p, p ≥ 1 → c.input.cells p ≠ Γ.start) ∧
    c.input.head ≥ 1 →
    c.output.cells 0 = Γ.start ∧
    (∀ p, p ≥ 1 → c.output.cells p ≠ Γ.start) ∧
    c.output.head ≥ 1 →
    ∃ c',
      (rewindWorkTM idx).reachesIn (h + 1) c c' ∧
      c'.state = RewindPhase.moveRight ∧
      (c'.work idx).head = 1 ∧
      (c'.work idx).cells = (c.work idx).cells ∧
      (∀ j : Fin 4, j ≠ idx → c'.work j = c.work j) ∧
      c'.input = c.input ∧
      c'.output = c.output := by
  intro h
  induction h with
  | zero =>
    intro c hstate hcell0 _ hhead hframe hinp hout
    have hread : (c.work idx).read = Γ.start := by simp [Tape.read, hhead, hcell0]
    -- The target tape reads ▷, so we go to moveRight and move right
    have hstep : ∃ c', (rewindWorkTM idx).step c = some c' ∧
        c'.state = RewindPhase.moveRight ∧
        (c'.work idx).head = 1 ∧
        (c'.work idx).cells = (c.work idx).cells ∧
        (∀ j : Fin 4, j ≠ idx → c'.work j = c.work j) ∧
        c'.input = c.input ∧
        c'.output = c.output := by
      simp only [TM.step, ↓reduceIte, hstate, rewindWorkTM, hread]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · -- target tape head = 1
        dsimp only []
        simp [Tape.writeAndMove, Tape.move, Tape.write, hhead]
      · -- target tape cells preserved
        dsimp only []
        simp [Tape.writeAndMove, tape_move_cells, Tape.write, hhead]
      · -- non-target work tapes unchanged
        intro j hj
        dsimp only []
        have hj_ne : ¬(j = idx) := hj
        obtain ⟨hc0j, hnsj, hhdj⟩ := hframe j hj
        simp only [↓reduceIte, hj_ne]
        have : (c.work j).read ≠ Γ.start := by
          simp only [Tape.read]; exact hnsj _ hhdj
        exact tape_idle_stable (c.work j) hhdj hnsj
      · -- input unchanged
        obtain ⟨_, hins, hih⟩ := hinp
        exact input_idle_stable c.input hih hins
      · -- output unchanged
        obtain ⟨_, hons, hoh⟩ := hout
        exact tape_idle_stable c.output hoh hons
    obtain ⟨c', hstep', hst', hh', hc', hfr', hinp', hout'⟩ := hstep
    exact ⟨c', .step hstep' .zero, hst', hh', hc', hfr', hinp', hout'⟩
  | succ h ih =>
    intro c hstate hcell0 hnostart hhead hframe hinp hout
    have hread_ne : (c.work idx).read ≠ Γ.start := by
      simp [Tape.read, hhead]; exact hnostart (h + 1) (by omega)
    -- Target tape reads non-▷, so we move left and stay in moveLeft
    have hstep : ∃ c', (rewindWorkTM idx).step c = some c' ∧
        c'.state = RewindPhase.moveLeft ∧
        (c'.work idx).head = h ∧
        (c'.work idx).cells = (c.work idx).cells ∧
        (∀ j : Fin 4, j ≠ idx → c'.work j = c.work j) ∧
        c'.input = c.input ∧
        c'.output = c.output := by
      simp only [TM.step, ↓reduceIte, hstate, rewindWorkTM, hread_ne]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · -- target tape head = h
        dsimp only []
        simp only [↓reduceIte, Tape.writeAndMove, Tape.move]
        rw [readBackWrite_toΓ_eq' hread_ne]
        simp only [Tape.write]; split
        · omega
        · simp [hhead]
      · -- target tape cells preserved
        dsimp only []
        simp only [↓reduceIte, Tape.writeAndMove, tape_move_cells']
        rw [readBackWrite_toΓ_eq' hread_ne]
        simp only [Tape.write]; split
        · rfl
        · exact Function.update_eq_self _ _
      · -- non-target work tapes unchanged
        intro j hj
        dsimp only []
        have hj_ne : ¬(j = idx) := hj
        obtain ⟨hc0j, hnsj, hhdj⟩ := hframe j hj
        simp only [↓reduceIte, hj_ne]
        exact tape_idle_stable (c.work j) hhdj hnsj
      · -- input unchanged
        obtain ⟨_, hins, hih⟩ := hinp
        exact input_idle_stable c.input hih hins
      · -- output unchanged
        obtain ⟨_, hons, hoh⟩ := hout
        exact tape_idle_stable c.output hoh hons
    obtain ⟨c', hstep', hst', hh', hc', hfr', hinp', hout'⟩ := hstep
    have hframe' : ∀ j : Fin 4, j ≠ idx →
        (c'.work j).cells 0 = Γ.start ∧
        (∀ p, p ≥ 1 → (c'.work j).cells p ≠ Γ.start) ∧
        (c'.work j).head ≥ 1 := by
      intro j hj; rw [hfr' j hj]; exact hframe j hj
    obtain ⟨c_mr, hreach, hst_mr, hh_mr, hc_mr, hfr_mr, hinp_mr, hout_mr⟩ :=
      ih c' hst' (by rw [hc']; exact hcell0)
        (by intro j hj; rw [hc']; exact hnostart j hj) hh'
        hframe' (by rw [hinp']; exact hinp) (by rw [hout']; exact hout)
    exact ⟨c_mr, .step hstep' hreach, hst_mr, hh_mr,
      by rw [hc_mr, hc'],
      fun j hj => by rw [hfr_mr j hj, hfr' j hj],
      by rw [hinp_mr, hinp'],
      by rw [hout_mr, hout']⟩

/-- From `moveRight` state, take 1 step to done. All tapes preserved. -/
private theorem rewindWorkTM_moveRight_to_done_frame (idx : Fin 4)
    (c : Cfg 4 (rewindWorkTM idx).Q)
    (hstate : c.state = RewindPhase.moveRight)
    (hread_ne : (c.work idx).read ≠ Γ.start)
    (hframe : ∀ j : Fin 4, j ≠ idx →
      (c.work j).cells 0 = Γ.start ∧
      (∀ p, p ≥ 1 → (c.work j).cells p ≠ Γ.start) ∧
      (c.work j).head ≥ 1)
    (hinp : c.input.cells 0 = Γ.start ∧
      (∀ p, p ≥ 1 → c.input.cells p ≠ Γ.start) ∧
      c.input.head ≥ 1)
    (hout : c.output.cells 0 = Γ.start ∧
      (∀ p, p ≥ 1 → c.output.cells p ≠ Γ.start) ∧
      c.output.head ≥ 1) :
    ∃ c',
      (rewindWorkTM idx).reachesIn 1 c c' ∧
      (rewindWorkTM idx).halted c' ∧
      (c'.work idx).head = (c.work idx).head ∧
      (c'.work idx).cells = (c.work idx).cells ∧
      (∀ j : Fin 4, j ≠ idx → c'.work j = c.work j) ∧
      c'.input = c.input ∧
      c'.output = c.output := by
  have hoDir : idleDir ((c.work idx).read) = Dir3.stay := by
    simp [idleDir, hread_ne]
  have hstep : ∃ c', (rewindWorkTM idx).step c = some c' ∧
      c'.state = RewindPhase.done ∧
      (c'.work idx).head = (c.work idx).head ∧
      (c'.work idx).cells = (c.work idx).cells ∧
      (∀ j : Fin 4, j ≠ idx → c'.work j = c.work j) ∧
      c'.input = c.input ∧
      c'.output = c.output := by
    simp only [TM.step, hstate, rewindWorkTM]
    refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · -- target head preserved
      dsimp only []
      rw [Tape.writeAndMove, hoDir]
      simp [Tape.move, Tape.write]
      split <;> rfl
    · -- target cells preserved
      dsimp only []
      rw [Tape.writeAndMove, hoDir]
      simp only [Tape.move, Tape.write]
      split
      · rfl
      · rw [readBackWrite_toΓ_eq' hread_ne]
        exact Function.update_eq_self _ _
    · -- non-target work tapes unchanged
      intro j hj
      dsimp only []
      obtain ⟨_, hnsj, hhdj⟩ := hframe j hj
      exact tape_idle_stable (c.work j) hhdj hnsj
    · -- input unchanged
      obtain ⟨_, hins, hih⟩ := hinp
      exact input_idle_stable c.input hih hins
    · -- output unchanged
      obtain ⟨_, hons, hoh⟩ := hout
      exact tape_idle_stable c.output hoh hons
  obtain ⟨c', hstep', hst', hhead', hcells', hfr', hinp', hout'⟩ := hstep
  exact ⟨c', .step hstep' .zero, hst', hhead', hcells', hfr', hinp', hout'⟩

-- ════════════════════════════════════════════════════════════════════════
-- Frame-preserving HoareTime for rewindWorkTM
-- ════════════════════════════════════════════════════════════════════════

/-- Frame-preserving HoareTime for `rewindWorkTM idx`:
    Given `InitEnvelope` and a head bound on the target tape,
    the target tape head goes to 1 with cells preserved,
    all other tapes unchanged, and `InitEnvelope` maintained. -/
theorem rewindWorkTM_hoareTime_frame (idx : Fin 4) (B : ℕ) :
    (rewindWorkTM idx).HoareTime
      (fun inp work out =>
        InitEnvelope inp work out ∧
        (work idx).head ≤ B)
      (fun inp work out =>
        InitEnvelope inp work out ∧
        (work idx).head = 1)
      (B + 2) := by
  intro inp work out ⟨henv, hhead_le⟩
  obtain ⟨hic0, hins, hih, hwf, hheads, hoc0, hons, hoh⟩ := henv
  -- Phase 1: rewind loop
  have hframe : ∀ j : Fin 4, j ≠ idx →
      (work j).cells 0 = Γ.start ∧
      (∀ p, p ≥ 1 → (work j).cells p ≠ Γ.start) ∧
      (work j).head ≥ 1 :=
    fun j _ => ⟨hwf.1 j, hwf.2 j, hheads j⟩
  obtain ⟨c_mr, hreach_rw, hst_mr, hhead_mr, hcells_mr, hfr_mr, hinp_mr, hout_mr⟩ :=
    rewindWorkTM_rewind_loop_frame idx (work idx).head
      { state := RewindPhase.moveLeft, input := inp, work := work, output := out }
      rfl (hwf.1 idx) (hwf.2 idx) rfl hframe
      ⟨hic0, hins, hih⟩ ⟨hoc0, hons, hoh⟩
  -- Phase 2: moveRight → done
  have hread_mr : (c_mr.work idx).read ≠ Γ.start := by
    simp [Tape.read, hhead_mr, hcells_mr]; exact hwf.2 idx 1 (by omega)
  have hframe_mr : ∀ j : Fin 4, j ≠ idx →
      (c_mr.work j).cells 0 = Γ.start ∧
      (∀ p, p ≥ 1 → (c_mr.work j).cells p ≠ Γ.start) ∧
      (c_mr.work j).head ≥ 1 := by
    intro j hj; rw [hfr_mr j hj]; exact hframe j hj
  obtain ⟨c_done, hreach_done, hhalt, hhead_done, hcells_done, hfr_done, hinp_done, hout_done⟩ :=
    rewindWorkTM_moveRight_to_done_frame idx c_mr hst_mr hread_mr hframe_mr
      (by rw [hinp_mr]; exact ⟨hic0, hins, hih⟩) (by rw [hout_mr]; exact ⟨hoc0, hons, hoh⟩)
  refine ⟨c_done, ((work idx).head + 1) + 1, by omega,
    reachesIn_trans (rewindWorkTM idx) hreach_rw hreach_done, hhalt, ?_⟩
  -- Simplify all c_mr/c_done references back to originals
  have hinp_eq : c_done.input = inp := by rw [hinp_done, hinp_mr]
  have hout_eq : c_done.output = out := by rw [hout_done, hout_mr]
  have hcells_eq : (c_done.work idx).cells = (work idx).cells := by
    rw [hcells_done, hcells_mr]
  have hwork_eq : ∀ j : Fin 4, j ≠ idx → c_done.work j = work j := by
    intro j hj; rw [hfr_done j hj, hfr_mr j hj]
  -- WorkTapesWF for c_done
  have hwf'1 : ∀ i, (c_done.work i).cells 0 = Γ.start := by
    intro i
    by_cases hi : i = idx
    · subst hi; rw [hcells_eq]; exact hwf.1 _
    · rw [hwork_eq i hi]; exact hwf.1 i
  have hwf'2 : ∀ i j, j ≥ 1 → (c_done.work i).cells j ≠ Γ.start := by
    intro i j hj
    by_cases hi : i = idx
    · subst hi; rw [hcells_eq]; exact hwf.2 _ j hj
    · rw [hwork_eq i hi]; exact hwf.2 i j hj
  have hwf' : WorkTapesWF c_done.work := ⟨hwf'1, hwf'2⟩
  have hheads' : ∀ i, (c_done.work i).head ≥ 1 := by
    intro i
    by_cases hi : i = idx
    · subst hi; rw [hhead_done, hhead_mr]
    · rw [hwork_eq i hi]; exact hheads i
  constructor
  · exact ⟨by rw [hinp_eq]; exact hic0,
           by intro j hj; rw [hinp_eq]; exact hins j hj,
           by rw [hinp_eq]; exact hih,
           hwf', hheads',
           by rw [hout_eq]; exact hoc0,
           by intro j hj; rw [hout_eq]; exact hons j hj,
           by rw [hout_eq]; exact hoh⟩
  · rw [hhead_done, hhead_mr]

-- ════════════════════════════════════════════════════════════════════════
-- Specific rewind instances
-- ════════════════════════════════════════════════════════════════════════

/-- Rewind work tape 0 (desc) with frame preservation. -/
theorem rewindDesc_hoareTime (B : ℕ) :
    (rewindWorkTM (0 : Fin 4)).HoareTime
      (fun inp work out =>
        InitEnvelope inp work out ∧
        (work 0).head ≤ B)
      (fun inp work out =>
        InitEnvelope inp work out ∧
        (work 0).head = 1)
      (B + 2) :=
  rewindWorkTM_hoareTime_frame 0 B

/-- Rewind work tape 3 (scratch) with frame preservation. -/
theorem rewindScratch_hoareTime (B : ℕ) :
    (rewindWorkTM (3 : Fin 4)).HoareTime
      (fun inp work out =>
        InitEnvelope inp work out ∧
        (work 3).head ≤ B)
      (fun inp work out =>
        InitEnvelope inp work out ∧
        (work 3).head = 1)
      (B + 2) :=
  rewindWorkTM_hoareTime_frame 3 B

-- ════════════════════════════════════════════════════════════════════════
-- SeqTransition identity under InitEnvelope
-- ════════════════════════════════════════════════════════════════════════

/-- Under `InitEnvelope`, the seq transition is identity on all tapes. -/
private theorem initEnvelope_seqTrans_id {inp : Tape} {work : Fin 4 → Tape} {out : Tape}
    (henv : InitEnvelope inp work out) :
    seqTransitionInput inp = inp ∧
    (fun i => seqTransitionTape (work i)) = work ∧
    seqTransitionTape out = out := by
  obtain ⟨hic0, hins, hih, hwf, hheads, hoc0, hons, hoh⟩ := henv
  refine ⟨?_, ?_, ?_⟩
  · exact seqTransitionInput_id (by simp [Tape.read]; exact hins inp.head hih)
  · ext i
    apply seqTransitionTape_id
    · intro h
      have := hwf.2 i (work i).head (hheads i)
      rw [Tape.read] at h
      exact this h
    · exact hheads i
  · apply seqTransitionTape_id
    · intro h
      have := hons out.head hoh
      rw [Tape.read] at h
      exact this h
    · exact hoh

/-- `h_trans` obligation for seqTM when `InitEnvelope` is part of the mid predicate. -/
private theorem initEnvelope_h_trans {P : TapePred 4}
    {inp : Tape} {work : Fin 4 → Tape} {out : Tape}
    (hmid : InitEnvelope inp work out ∧ P inp work out) :
    (InitEnvelope (seqTransitionInput inp)
      (fun i => seqTransitionTape (work i))
      (seqTransitionTape out)) ∧
    P (seqTransitionInput inp)
      (fun i => seqTransitionTape (work i))
      (seqTransitionTape out) := by
  obtain ⟨henv, hp⟩ := hmid
  obtain ⟨hi, hw, ho⟩ := initEnvelope_seqTrans_id henv
  rw [hi, hw, ho]
  exact ⟨henv, hp⟩

-- ════════════════════════════════════════════════════════════════════════
-- Compose 4 rewinds
-- ════════════════════════════════════════════════════════════════════════

/-- Enriched frame-preserving rewind: postcondition carries head bounds for
    ALL tapes. Target tape gets head = 1 (≤ anything), non-target tapes
    retain their original bounds since they're completely unchanged. -/
theorem rewindWorkTM_hoareTime_frame_bounds (idx : Fin 4) (bounds : Fin 4 → ℕ) :
    (rewindWorkTM idx).HoareTime
      (fun inp work out =>
        InitEnvelope inp work out ∧
        ∀ i, (work i).head ≤ bounds i)
      (fun inp work out =>
        InitEnvelope inp work out ∧
        (work idx).head = 1 ∧
        ∀ i, i ≠ idx → (work i).head ≤ bounds i)
      (bounds idx + 2) := by
  intro inp work out ⟨henv, hbounds⟩
  obtain ⟨hic0, hins, hih, hwf, hheads, hoc0, hons, hoh⟩ := henv
  have hframe : ∀ j : Fin 4, j ≠ idx →
      (work j).cells 0 = Γ.start ∧
      (∀ p, p ≥ 1 → (work j).cells p ≠ Γ.start) ∧
      (work j).head ≥ 1 :=
    fun j _ => ⟨hwf.1 j, hwf.2 j, hheads j⟩
  obtain ⟨c_mr, hreach_rw, hst_mr, hhead_mr, hcells_mr, hfr_mr, hinp_mr, hout_mr⟩ :=
    rewindWorkTM_rewind_loop_frame idx (work idx).head
      { state := RewindPhase.moveLeft, input := inp, work := work, output := out }
      rfl (hwf.1 idx) (hwf.2 idx) rfl hframe
      ⟨hic0, hins, hih⟩ ⟨hoc0, hons, hoh⟩
  have hread_mr : (c_mr.work idx).read ≠ Γ.start := by
    simp [Tape.read, hhead_mr, hcells_mr]; exact hwf.2 idx 1 (by omega)
  have hframe_mr : ∀ j : Fin 4, j ≠ idx →
      (c_mr.work j).cells 0 = Γ.start ∧
      (∀ p, p ≥ 1 → (c_mr.work j).cells p ≠ Γ.start) ∧
      (c_mr.work j).head ≥ 1 := by
    intro j hj; rw [hfr_mr j hj]; exact hframe j hj
  obtain ⟨c_done, hreach_done, hhalt, hhead_done, hcells_done, hfr_done, hinp_done, hout_done⟩ :=
    rewindWorkTM_moveRight_to_done_frame idx c_mr hst_mr hread_mr hframe_mr
      (by rw [hinp_mr]; exact ⟨hic0, hins, hih⟩) (by rw [hout_mr]; exact ⟨hoc0, hons, hoh⟩)
  -- Derive frame equalities
  have hinp_eq : c_done.input = inp := by rw [hinp_done, hinp_mr]
  have hout_eq : c_done.output = out := by rw [hout_done, hout_mr]
  have hcells_eq : (c_done.work idx).cells = (work idx).cells := by
    rw [hcells_done, hcells_mr]
  have hwork_eq : ∀ j : Fin 4, j ≠ idx → c_done.work j = work j := by
    intro j hj; rw [hfr_done j hj, hfr_mr j hj]
  -- Build postcondition
  have hwf'1 : ∀ i, (c_done.work i).cells 0 = Γ.start := by
    intro i; by_cases hi : i = idx
    · subst hi; rw [hcells_eq]; exact hwf.1 _
    · rw [hwork_eq i hi]; exact hwf.1 i
  have hwf'2 : ∀ i j, j ≥ 1 → (c_done.work i).cells j ≠ Γ.start := by
    intro i j hj; by_cases hi : i = idx
    · subst hi; rw [hcells_eq]; exact hwf.2 _ j hj
    · rw [hwork_eq i hi]; exact hwf.2 i j hj
  have hheads' : ∀ i, (c_done.work i).head ≥ 1 := by
    intro i; by_cases hi : i = idx
    · subst hi; rw [hhead_done, hhead_mr]
    · rw [hwork_eq i hi]; exact hheads i
  have hb_idx := hbounds idx
  refine ⟨c_done, ((work idx).head + 1) + 1, by omega,
    reachesIn_trans (rewindWorkTM idx) hreach_rw hreach_done, hhalt,
    ⟨by rw [hinp_eq]; exact hic0,
     by intro j hj; rw [hinp_eq]; exact hins j hj,
     by rw [hinp_eq]; exact hih,
     ⟨hwf'1, hwf'2⟩, hheads',
     by rw [hout_eq]; exact hoc0,
     by intro j hj; rw [hout_eq]; exact hons j hj,
     by rw [hout_eq]; exact hoh⟩,
    by rw [hhead_done, hhead_mr],
    fun i hi => by rw [hwork_eq i hi]; exact hbounds i⟩


/-- Composition of 4 rewinds via `seqTM_hoareTime`. -/
theorem rewindAll_hoareTime (B0 B1 B2 B3 : ℕ) :
    (seqTM (rewindWorkTM (0 : Fin 4))
      (seqTM (rewindWorkTM (1 : Fin 4))
        (seqTM (rewindWorkTM (2 : Fin 4))
          (rewindWorkTM (3 : Fin 4))))).HoareTime
      (fun inp work out =>
        InitEnvelope inp work out ∧
        (work 0).head ≤ B0 ∧
        (work 1).head ≤ B1 ∧
        (work 2).head ≤ B2 ∧
        (work 3).head ≤ B3)
      (fun inp work out =>
        InitEnvelope inp work out ∧
        ∀ i, (work i).head = 1)
      (B0 + B1 + B2 + B3 + 11) := by
  -- We use `seqTM_hoareTime` three times to compose 4 rewinds.
  -- The key helper is `rewindWorkTM_hoareTime_frame_bounds` which carries
  -- head bounds for all tapes through each rewind.
  --
  -- Intermediate bound functions:
  -- pre:  ![B0, B1, B2, B3]
  -- mid0: ![1,  B1, B2, B3]  (after rewind 0)
  -- mid1: ![1,  1,  B2, B3]  (after rewind 1)
  -- mid2: ![1,  1,  1,  B3]  (after rewind 2)
  -- post: ![1,  1,  1,  1 ]  (after rewind 3)
  let b0 : Fin 4 → ℕ := fun i => match i with | 0 => B0 | 1 => B1 | 2 => B2 | 3 => B3
  let b1 : Fin 4 → ℕ := fun i => match i with | 0 => 1 | 1 => B1 | 2 => B2 | 3 => B3
  let b2 : Fin 4 → ℕ := fun i => match i with | 0 => 1 | 1 => 1 | 2 => B2 | 3 => B3
  let b3 : Fin 4 → ℕ := fun i => match i with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => B3
  -- Intermediate predicates
  let mid0 : TapePred 4 := fun inp work out =>
    InitEnvelope inp work out ∧ ∀ i, (work i).head ≤ b1 i
  let mid1 : TapePred 4 := fun inp work out =>
    InitEnvelope inp work out ∧ ∀ i, (work i).head ≤ b2 i
  let mid2 : TapePred 4 := fun inp work out =>
    InitEnvelope inp work out ∧ ∀ i, (work i).head ≤ b3 i
  -- Build each rewind's HoareTime spec
  have h_rw0 : (rewindWorkTM (0 : Fin 4)).HoareTime
      (fun inp work out => InitEnvelope inp work out ∧ ∀ i, (work i).head ≤ b0 i)
      mid0 (B0 + 2) :=
    (rewindWorkTM_hoareTime_frame_bounds 0 b0).consequence
      (fun _ _ _ h => h)
      (fun _ _ _ ⟨henv', hhead0, hrest⟩ => ⟨henv', fun i => by
        match i with
        | 0 => rw [hhead0]
        | 1 => exact hrest 1 (by decide)
        | 2 => exact hrest 2 (by decide)
        | 3 => exact hrest 3 (by decide)⟩)
      le_rfl
  have h_rw1 : (rewindWorkTM (1 : Fin 4)).HoareTime mid0 mid1 (B1 + 2) :=
    (rewindWorkTM_hoareTime_frame_bounds 1 b1).consequence
      (fun _ _ _ h => h)
      (fun _ _ _ ⟨henv', hhead1, hrest⟩ => ⟨henv', fun i => by
        match i with
        | 0 => exact hrest 0 (by decide)
        | 1 => rw [hhead1]
        | 2 => exact hrest 2 (by decide)
        | 3 => exact hrest 3 (by decide)⟩)
      le_rfl
  have h_rw2 : (rewindWorkTM (2 : Fin 4)).HoareTime mid1 mid2 (B2 + 2) :=
    (rewindWorkTM_hoareTime_frame_bounds 2 b2).consequence
      (fun _ _ _ h => h)
      (fun _ _ _ ⟨henv', hhead2, hrest⟩ => ⟨henv', fun i => by
        match i with
        | 0 => exact hrest 0 (by decide)
        | 1 => exact hrest 1 (by decide)
        | 2 => rw [hhead2]
        | 3 => exact hrest 3 (by decide)⟩)
      le_rfl
  have h_rw3 : (rewindWorkTM (3 : Fin 4)).HoareTime mid2
      (fun inp work out => InitEnvelope inp work out ∧ ∀ i, (work i).head = 1)
      (B3 + 2) :=
    (rewindWorkTM_hoareTime_frame_bounds 3 b3).consequence
      (fun _ _ _ h => h)
      (fun _ work' _ ⟨henv', hhead3, hrest⟩ => ⟨henv', fun i => by
        have hge := henv'.2.2.2.2.1 i
        match i with
        | 0 => have := hrest 0 (by decide); dsimp [b3] at this; omega
        | 1 => have := hrest 1 (by decide); dsimp [b3] at this; omega
        | 2 => have := hrest 2 (by decide); dsimp [b3] at this; omega
        | 3 => exact hhead3⟩)
      le_rfl
  -- Helper for h_trans: seq transition is identity on each mid predicate
  have h_trans_mid0 : ∀ inp work out, mid0 inp work out →
      mid0 (seqTransitionInput inp) (fun i => seqTransitionTape (work i))
        (seqTransitionTape out) := by
    intro inp' work' out' ⟨henv', hp⟩
    obtain ⟨hi, hw, ho⟩ := initEnvelope_seqTrans_id henv'
    rw [hi, hw, ho]; exact ⟨henv', hp⟩
  have h_trans_mid1 : ∀ inp work out, mid1 inp work out →
      mid1 (seqTransitionInput inp) (fun i => seqTransitionTape (work i))
        (seqTransitionTape out) := by
    intro inp' work' out' ⟨henv', hp⟩
    obtain ⟨hi, hw, ho⟩ := initEnvelope_seqTrans_id henv'
    rw [hi, hw, ho]; exact ⟨henv', hp⟩
  have h_trans_mid2 : ∀ inp work out, mid2 inp work out →
      mid2 (seqTransitionInput inp) (fun i => seqTransitionTape (work i))
        (seqTransitionTape out) := by
    intro inp' work' out' ⟨henv', hp⟩
    obtain ⟨hi, hw, ho⟩ := initEnvelope_seqTrans_id henv'
    rw [hi, hw, ho]; exact ⟨henv', hp⟩
  -- Compose using seqTM_hoareTime, then adjust bound
  exact (seqTM_hoareTime _ _ h_rw0 h_trans_mid0
    (seqTM_hoareTime _ _ h_rw1 h_trans_mid1
      (seqTM_hoareTime _ _ h_rw2 h_trans_mid2 h_rw3))).consequence
    (fun inp' work' out' ⟨henv', hb0', hb1', hb2', hb3'⟩ =>
      (⟨henv', fun i => by
        match i with
        | 0 => exact hb0'
        | 1 => exact hb1'
        | 2 => exact hb2'
        | 3 => exact hb3'⟩ :
        InitEnvelope inp' work' out' ∧ ∀ i, (work' i).head ≤ b0 i))
    (fun _ _ _ h => h)
    (by omega)

end TM
