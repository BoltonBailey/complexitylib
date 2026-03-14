import Complexitylib.Models.TuringMachine.UTM.Helpers
import Complexitylib.Models.TuringMachine.Hoare.Defs

/-!
# UTM Helpers: proof internals

Simulation lemmas and HoareTime proofs for the helper machines defined in
`Complexitylib.Models.TuringMachine.UTM.Helpers`.

## Main results

- `writeTM_hoareTime` — HoareTime for `writeTM sym`: writes `sym.toΓ` to output cell 1
- `rewindWorkTM_hoareTime` — HoareTime for `rewindWorkTM idx`: rewinds work tape to cell 1
-/

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- Tape helpers (private, duplicated since they are private in other files)
-- ════════════════════════════════════════════════════════════════════════

private theorem tape_move_cells (t : Tape) (d : Dir3) :
    (t.move d).cells = t.cells := by cases d <;> rfl

private theorem readBackWrite_toΓ_eq {g : Γ} (h : g ≠ Γ.start) :
    (readBackWrite g).toΓ = g := by cases g <;> simp_all [readBackWrite, Γw.toΓ]

-- ════════════════════════════════════════════════════════════════════════
-- writeTM: rewind loop
-- ════════════════════════════════════════════════════════════════════════

/-- Rewind loop for writeTM: from rewind state with output head at position `h`,
    reach goRight state with head = 1 in `h + 1` steps, preserving output cells. -/
private theorem writeTM_rewind_loop (sym : Γw) :
    ∀ (h : ℕ) (c : Cfg n (writeTM sym).Q),
    c.state = WritePhase.rewind →
    c.output.cells 0 = Γ.start →
    (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) →
    c.output.head = h →
    ∃ c',
      (writeTM sym).reachesIn (h + 1) c c' ∧
      c'.state = WritePhase.goRight ∧
      c'.output.head = 1 ∧
      c'.output.cells = c.output.cells := by
  intro h
  induction h with
  | zero =>
    intro c hstate hcell0 _ hhead
    have hread : c.output.read = Γ.start := by simp [Tape.read, hhead, hcell0]
    have hstep : ∃ c', (writeTM sym).step c = some c' ∧
        c'.state = WritePhase.goRight ∧
        c'.output.head = 1 ∧
        c'.output.cells = c.output.cells := by
      simp only [TM.step, ↓reduceIte, hstate, writeTM, hread]
      refine ⟨_, rfl, rfl, ?_, ?_⟩
      · simp [Tape.writeAndMove, Tape.move, Tape.write, hhead]
      · simp [Tape.writeAndMove, tape_move_cells, Tape.write, hhead]
    obtain ⟨c', hstep', hst', hh', hc'⟩ := hstep
    exact ⟨c', .step hstep' .zero, hst', hh', hc'⟩
  | succ h ih =>
    intro c hstate hcell0 hnostart hhead
    have hread_ne : c.output.read ≠ Γ.start := by
      simp [Tape.read, hhead]; exact hnostart (h + 1) (by omega)
    have hstep : ∃ c', (writeTM sym).step c = some c' ∧
        c'.state = WritePhase.rewind ∧
        c'.output.head = h ∧
        c'.output.cells = c.output.cells := by
      simp only [TM.step, ↓reduceIte, hstate, writeTM, hread_ne]
      refine ⟨_, rfl, rfl, ?_, ?_⟩
      · simp only [Tape.writeAndMove, Tape.move]
        rw [readBackWrite_toΓ_eq hread_ne]
        simp only [Tape.write]; split
        · omega
        · simp [hhead]
      · simp only [Tape.writeAndMove, tape_move_cells]
        rw [readBackWrite_toΓ_eq hread_ne]
        simp only [Tape.write]; split
        · rfl
        · exact Function.update_eq_self _ _
    obtain ⟨c', hstep', hst', hh', hc'⟩ := hstep
    obtain ⟨c_go, hreach, hst_go, hh_go, hc_go⟩ := ih c' hst'
      (by rw [hc']; exact hcell0) (by intro j hj; rw [hc']; exact hnostart j hj) hh'
    exact ⟨c_go, .step hstep' hreach, hst_go, hh_go, by rw [hc_go, hc']⟩

-- ════════════════════════════════════════════════════════════════════════
-- writeTM: goRight and write steps
-- ════════════════════════════════════════════════════════════════════════

/-- From goRight state with output head at cell 1, take 2 steps to reach
    done (halted) state with sym written to output cell 1. -/
private theorem writeTM_goRight_to_done (sym : Γw) (c : Cfg n (writeTM sym).Q)
    (hstate : c.state = WritePhase.goRight)
    (hhead : c.output.head = 1)
    (hnostart1 : c.output.cells 1 ≠ Γ.start) :
    ∃ c',
      (writeTM sym).reachesIn 2 c c' ∧
      (writeTM sym).halted c' ∧
      c'.output.cells 1 = sym.toΓ := by
  -- Step 1: goRight → write (writes blank at cell 1, stays at head=1)
  have hoDir : idleDir (c.output.read) = Dir3.stay := by
    simp [idleDir, Tape.read, hhead, hnostart1]
  have hstep1 : ∃ c₁, (writeTM sym).step c = some c₁ ∧
      c₁.state = WritePhase.write ∧
      c₁.output.head = 1 ∧
      c₁.output.cells 1 = Γ.blank := by
    simp only [TM.step, hstate, writeTM]
    refine ⟨_, rfl, rfl, ?_, ?_⟩
    · simp [Tape.writeAndMove, Tape.move, Tape.write, hhead, hoDir]
    · simp [Tape.writeAndMove, Tape.move, Tape.write, hhead, hoDir,
            Function.update_self, Γw.toΓ]
  obtain ⟨c₁, hstep1', hst1, hhead1, hcell1_blank⟩ := hstep1
  -- Step 2: write → done (writes sym at cell 1)
  have hoDir2 : idleDir (c₁.output.read) = Dir3.stay := by
    simp [idleDir, Tape.read, hhead1, hcell1_blank]
  have hstep2 : ∃ c₂, (writeTM sym).step c₁ = some c₂ ∧
      c₂.state = WritePhase.done ∧
      c₂.output.cells 1 = sym.toΓ := by
    simp only [TM.step, hst1, writeTM]
    refine ⟨_, rfl, rfl, ?_⟩
    simp [Tape.writeAndMove, Tape.move, Tape.write, hhead1, hoDir2,
          Function.update_self]
  obtain ⟨c₂, hstep2', hst2, hcells2⟩ := hstep2
  exact ⟨c₂, .step hstep1' (.step hstep2' .zero), hst2, hcells2⟩

-- ════════════════════════════════════════════════════════════════════════
-- writeTM: main HoareTime theorem
-- ════════════════════════════════════════════════════════════════════════

/-- `writeTM sym` writes `sym.toΓ` to output cell 1 and halts.
    Precondition: output tape is well-formed (cell 0 = ▷, cells ≥ 1 ≠ ▷),
    and output head is at most `B`.
    Postcondition: output cell 1 = sym.toΓ.
    Time: B + 3 steps. -/
theorem writeTM_hoareTime (sym : Γw) (B : ℕ) :
    (writeTM (n := n) sym).HoareTime
      (fun _ _ out => out.cells 0 = Γ.start ∧
                      (∀ j, j ≥ 1 → out.cells j ≠ Γ.start) ∧
                      out.head ≤ B)
      (fun _ _ out => out.cells 1 = sym.toΓ)
      (B + 3) := by
  intro inp work out ⟨hcell0, hnostart, hhead_le⟩
  -- Phase 1: rewind to cell 1
  obtain ⟨c_go, hreach_rw, hst_go, hhead_go, hcells_go⟩ :=
    writeTM_rewind_loop sym out.head
      { state := WritePhase.rewind, input := inp, work := work, output := out }
      rfl hcell0 hnostart rfl
  -- Phase 2: write sym and halt
  have hnostart_go : c_go.output.cells 1 ≠ Γ.start := by
    rw [hcells_go]; exact hnostart 1 (by omega)
  obtain ⟨c_done, hreach_wr, hhalt, hwrite⟩ :=
    writeTM_goRight_to_done sym c_go hst_go hhead_go hnostart_go
  refine ⟨c_done, (out.head + 1) + 2, ?_,
    reachesIn_trans (writeTM sym) hreach_rw hreach_wr, hhalt, hwrite⟩
  omega

-- ════════════════════════════════════════════════════════════════════════
-- rewindWorkTM: rewind loop
-- ════════════════════════════════════════════════════════════════════════

/-- Rewind loop for rewindWorkTM: from moveLeft state with work tape `idx`
    head at position `h`, reach moveRight state with head = 1 in `h + 1`
    steps, preserving work tape cells. -/
private theorem rewindWorkTM_rewind_loop (idx : Fin n) :
    ∀ (h : ℕ) (c : Cfg n (rewindWorkTM idx).Q),
    c.state = RewindPhase.moveLeft →
    (c.work idx).cells 0 = Γ.start →
    (∀ j, j ≥ 1 → (c.work idx).cells j ≠ Γ.start) →
    (c.work idx).head = h →
    ∃ c',
      (rewindWorkTM idx).reachesIn (h + 1) c c' ∧
      c'.state = RewindPhase.moveRight ∧
      (c'.work idx).head = 1 ∧
      (c'.work idx).cells = (c.work idx).cells := by
  intro h
  induction h with
  | zero =>
    intro c hstate hcell0 _ hhead
    have hread : (c.work idx).read = Γ.start := by simp [Tape.read, hhead, hcell0]
    have hstep : ∃ c', (rewindWorkTM idx).step c = some c' ∧
        c'.state = RewindPhase.moveRight ∧
        (c'.work idx).head = 1 ∧
        (c'.work idx).cells = (c.work idx).cells := by
      simp only [TM.step, ↓reduceIte, hstate, rewindWorkTM, hread]
      refine ⟨_, rfl, rfl, ?_, ?_⟩
      · dsimp only []
        simp [Tape.writeAndMove, Tape.move, Tape.write, hhead]
      · dsimp only []
        simp [Tape.writeAndMove, tape_move_cells, Tape.write, hhead]
    obtain ⟨c', hstep', hst', hh', hc'⟩ := hstep
    exact ⟨c', .step hstep' .zero, hst', hh', hc'⟩
  | succ h ih =>
    intro c hstate hcell0 hnostart hhead
    have hread_ne : (c.work idx).read ≠ Γ.start := by
      simp [Tape.read, hhead]; exact hnostart (h + 1) (by omega)
    have hstep : ∃ c', (rewindWorkTM idx).step c = some c' ∧
        c'.state = RewindPhase.moveLeft ∧
        (c'.work idx).head = h ∧
        (c'.work idx).cells = (c.work idx).cells := by
      simp only [TM.step, ↓reduceIte, hstate, rewindWorkTM, hread_ne]
      refine ⟨_, rfl, rfl, ?_, ?_⟩
      · dsimp only []
        simp only [↓reduceIte, Tape.writeAndMove, Tape.move]
        rw [readBackWrite_toΓ_eq hread_ne]
        simp only [Tape.write]; split
        · omega
        · simp [hhead]
      · dsimp only []
        simp only [↓reduceIte, Tape.writeAndMove, tape_move_cells]
        rw [readBackWrite_toΓ_eq hread_ne]
        simp only [Tape.write]; split
        · rfl
        · exact Function.update_eq_self _ _
    obtain ⟨c', hstep', hst', hh', hc'⟩ := hstep
    obtain ⟨c_mr, hreach, hst_mr, hh_mr, hc_mr⟩ := ih c' hst'
      (by rw [hc']; exact hcell0) (by intro j hj; rw [hc']; exact hnostart j hj) hh'
    exact ⟨c_mr, .step hstep' hreach, hst_mr, hh_mr, by rw [hc_mr, hc']⟩

-- ════════════════════════════════════════════════════════════════════════
-- rewindWorkTM: moveRight step
-- ════════════════════════════════════════════════════════════════════════

/-- From moveRight state with work tape reading non-▷,
    take 1 step to done (halted) state, preserving work tape head. -/
private theorem rewindWorkTM_moveRight_to_done (idx : Fin n)
    (c : Cfg n (rewindWorkTM idx).Q)
    (hstate : c.state = RewindPhase.moveRight)
    (hread_ne : (c.work idx).read ≠ Γ.start) :
    ∃ c',
      (rewindWorkTM idx).reachesIn 1 c c' ∧
      (rewindWorkTM idx).halted c' ∧
      (c'.work idx).head = (c.work idx).head := by
  have hoDir : idleDir ((c.work idx).read) = Dir3.stay := by
    simp [idleDir, hread_ne]
  have hstep : ∃ c', (rewindWorkTM idx).step c = some c' ∧
      c'.state = RewindPhase.done ∧
      (c'.work idx).head = (c.work idx).head := by
    simp only [TM.step, hstate, rewindWorkTM, allIdle]
    refine ⟨_, rfl, rfl, ?_⟩
    dsimp only []
    rw [Tape.writeAndMove, hoDir]
    simp [Tape.move, Tape.write]
    split <;> rfl
  obtain ⟨c', hstep', hst', hhead'⟩ := hstep
  exact ⟨c', .step hstep' .zero, hst', hhead'⟩

-- ════════════════════════════════════════════════════════════════════════
-- rewindWorkTM: main HoareTime theorem
-- ════════════════════════════════════════════════════════════════════════

/-- `rewindWorkTM idx` rewinds work tape `idx` to cell 1 and halts.
    Precondition: work tape `idx` is well-formed (cell 0 = ▷, cells ≥ 1 ≠ ▷),
    and work tape head is at most `B`.
    Postcondition: work tape `idx` head = 1.
    Time: B + 2 steps. -/
theorem rewindWorkTM_hoareTime (idx : Fin n) (B : ℕ) :
    (rewindWorkTM idx).HoareTime
      (fun _ work _ => (work idx).cells 0 = Γ.start ∧
                       (∀ j, j ≥ 1 → (work idx).cells j ≠ Γ.start) ∧
                       (work idx).head ≤ B)
      (fun _ work _ => (work idx).head = 1)
      (B + 2) := by
  intro inp work out ⟨hcell0, hnostart, hhead_le⟩
  -- Phase 1: rewind to cell 1
  obtain ⟨c_mr, hreach_rw, hst_mr, hhead_mr, hcells_mr⟩ :=
    rewindWorkTM_rewind_loop idx (work idx).head
      { state := RewindPhase.moveLeft, input := inp, work := work, output := out }
      rfl hcell0 hnostart rfl
  -- Phase 2: moveRight → done
  have hread_mr : (c_mr.work idx).read ≠ Γ.start := by
    simp [Tape.read, hhead_mr, hcells_mr]; exact hnostart 1 (by omega)
  obtain ⟨c_done, hreach_mr, hhalt, hhead_done⟩ :=
    rewindWorkTM_moveRight_to_done idx c_mr hst_mr hread_mr
  refine ⟨c_done, ((work idx).head + 1) + 1, ?_,
    reachesIn_trans (rewindWorkTM idx) hreach_rw hreach_mr, hhalt,
    by dsimp only []; rw [hhead_done, hhead_mr]⟩
  omega

end TM
