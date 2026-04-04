import Complexitylib.Models.TuringMachine.Subroutines
import Complexitylib.Models.TuringMachine.Hoare.Defs
import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic

/-!
# TM Subroutines: proof internals

Simulation lemmas and HoareTime proofs for the subroutine machines defined in
`Complexitylib.Models.TuringMachine.Subroutines`.

## Main results

- `writeTM_hoareTime` — writes `sym.toΓ` to output cell 1
- `rewindWorkTM_hoareTime` — rewinds work tape `idx` to cell 1
- `rewindWorkTM_rich_hoareTime` — rewind preserving arbitrary predicate P
-/

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- writeTM: rewind loop
-- ════════════════════════════════════════════════════════════════════════

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

private theorem writeTM_goRight_to_done (sym : Γw) (c : Cfg n (writeTM sym).Q)
    (hstate : c.state = WritePhase.goRight)
    (hhead : c.output.head = 1)
    (hnostart1 : c.output.cells 1 ≠ Γ.start) :
    ∃ c',
      (writeTM sym).reachesIn 2 c c' ∧
      (writeTM sym).halted c' ∧
      c'.output.cells 1 = sym.toΓ := by
  have hoDir : idleDir (c.output.read) = Dir3.stay := by
    simp [idleDir, Tape.read, hhead, hnostart1]
  -- Step 1: goRight → write
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
  -- Step 2: write → done
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
    **Pre**: output tape well-formed (cell 0 = ▷, cells ≥ 1 ≠ ▷), head ≤ B.
    **Post**: output cell 1 = sym.toΓ.
    **Time**: B + 3 steps. -/
theorem writeTM_hoareTime (sym : Γw) (B : ℕ) :
    (writeTM (n := n) sym).HoareTime
      (fun _ _ out => out.cells 0 = Γ.start ∧
                      (∀ j, j ≥ 1 → out.cells j ≠ Γ.start) ∧
                      out.head ≤ B)
      (fun _ _ out => out.cells 1 = sym.toΓ)
      (B + 3) := by
  intro inp work out ⟨hcell0, hnostart, hhead_le⟩
  obtain ⟨c_go, hreach_rw, hst_go, hhead_go, hcells_go⟩ :=
    writeTM_rewind_loop sym out.head
      { state := WritePhase.rewind, input := inp, work := work, output := out }
      rfl hcell0 hnostart rfl
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
      · dsimp only []; simp [Tape.writeAndMove, Tape.move, Tape.write, hhead]
      · dsimp only []; simp [Tape.writeAndMove, tape_move_cells, Tape.write, hhead]
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
      (rewindWorkTM idx).halted c' ∧
      (c'.work idx).head = (c.work idx).head := by
    simp only [TM.step, hstate, rewindWorkTM, allIdle]
    refine ⟨_, rfl, rfl, ?_⟩
    dsimp only []
    rw [Tape.writeAndMove, hoDir]
    simp [Tape.move, Tape.write]
    split <;> rfl
  obtain ⟨c', hstep', hhalt, hhead⟩ := hstep
  exact ⟨c', .step hstep' .zero, hhalt, hhead⟩

-- ════════════════════════════════════════════════════════════════════════
-- rewindWorkTM: main HoareTime theorem
-- ════════════════════════════════════════════════════════════════════════

/-- `rewindWorkTM idx` rewinds work tape `idx` to cell 1 and halts.
    **Pre**: work tape `idx` well-formed (cell 0 = ▷, cells ≥ 1 ≠ ▷), head ≤ B.
    **Post**: work tape `idx` head = 1.
    **Time**: B + 2 steps. -/
theorem rewindWorkTM_hoareTime (idx : Fin n) (B : ℕ) :
    (rewindWorkTM idx).HoareTime
      (fun _ work _ => (work idx).cells 0 = Γ.start ∧
                       (∀ j, j ≥ 1 → (work idx).cells j ≠ Γ.start) ∧
                       (work idx).head ≤ B)
      (fun _ work _ => (work idx).head = 1)
      (B + 2) := by
  intro inp work out ⟨hcell0, hnostart, hhead_le⟩
  obtain ⟨c_mr, hreach_rw, hst_mr, hhead_mr, hcells_mr⟩ :=
    rewindWorkTM_rewind_loop idx (work idx).head
      { state := RewindPhase.moveLeft, input := inp, work := work, output := out }
      rfl hcell0 hnostart rfl
  have hread_mr : (c_mr.work idx).read ≠ Γ.start := by
    simp [Tape.read, hhead_mr, hcells_mr]; exact hnostart 1 (by omega)
  obtain ⟨c_done, hreach_mr, hhalt, hhead_done⟩ :=
    rewindWorkTM_moveRight_to_done idx c_mr hst_mr hread_mr
  refine ⟨c_done, ((work idx).head + 1) + 1, ?_,
    reachesIn_trans (rewindWorkTM idx) hreach_rw hreach_mr, hhalt,
    by dsimp only []; rw [hhead_done, hhead_mr]⟩
  omega

-- ════════════════════════════════════════════════════════════════════════
-- rewindWorkTM: rich HoareTime preserving arbitrary data
-- ════════════════════════════════════════════════════════════════════════

/-- Rich HoareTime for `rewindWorkTM` that preserves an arbitrary predicate P
    through the rewind, provided P depends on cells (not heads) of the target
    tape. This is the key tool for threading invariants (e.g., simulation state,
    encoded data) through rewind steps in `seqTM` compositions.

    The caller provides `hP_preserved` showing that P is stable under:
    - target tape cells unchanged, head set to 1
    - all other work tapes unchanged
    - input and output unchanged -/
theorem rewindWorkTM_rich_hoareTime {n : ℕ} (idx : Fin n) (B_tape : ℕ)
    {P : Tape → (Fin n → Tape) → Tape → Prop}
    (hP_preserved : ∀ (inp : Tape) (work : Fin n → Tape) (out : Tape)
      (inp' : Tape) (work' : Fin n → Tape) (out' : Tape),
      P inp work out →
      (work' idx).cells = (work idx).cells →
      (work' idx).head = 1 →
      (∀ i, i ≠ idx → work' i = work i) →
      inp' = inp →
      out'.cells = out.cells →
      out'.head = out.head →
      P inp' work' out') :
    (rewindWorkTM idx).HoareTime
      (fun inp work out =>
        (work idx).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (work idx).cells j ≠ Γ.start) ∧
        (work idx).head ≤ B_tape ∧
        inp.read ≠ Γ.start ∧
        out.read ≠ Γ.start ∧ out.head ≥ 1 ∧
        (∀ i, i ≠ idx → (work i).read ≠ Γ.start ∧ (work i).head ≥ 1) ∧
        P inp work out)
      (fun inp work out =>
        (work idx).head = 1 ∧
        P inp work out)
      (B_tape + 2) := by
  intro inp work out ⟨hcell0, hnostart, hhead_le, hinp_ns, hout_ns, hout_h, hother_wf, hP⟩
  -- Helper: idle-step identity for stable tapes
  have tape_idle_preserve : ∀ (t : Tape), t.read ≠ Γ.start → t.head ≥ 1 →
      t.writeAndMove (readBackWrite t.read) (idleDir t.read) = t := by
    intro t hns hh
    simp only [Tape.writeAndMove, idleDir, hns, ↓reduceIte, Tape.move, Tape.write]
    split
    · omega
    · simp only [Tape.read] at hns ⊢
      rw [readBackWrite_toΓ_eq hns, Function.update_eq_self]
  -- Rich rewind loop: tracks ALL tapes, not just work tape idx
  suffices h_loop : ∀ (h : ℕ) (c : Cfg n (rewindWorkTM idx).Q),
      c.state = RewindPhase.moveLeft →
      (c.work idx).cells 0 = Γ.start →
      (∀ j, j ≥ 1 → (c.work idx).cells j ≠ Γ.start) →
      (c.work idx).head = h →
      c.input = inp → c.output = out → (∀ i, i ≠ idx → c.work i = work i) →
      ∃ c',
        (rewindWorkTM idx).reachesIn (h + 2) c c' ∧
        (rewindWorkTM idx).halted c' ∧
        (c'.work idx).head = 1 ∧ (c'.work idx).cells = (c.work idx).cells ∧
        c'.input = inp ∧ c'.output = out ∧ (∀ i, i ≠ idx → c'.work i = work i) by
    obtain ⟨c', hreach, hhalt, hh1, hcells, hinp', hout', hw'⟩ :=
      h_loop (work idx).head
        { state := RewindPhase.moveLeft, input := inp, work := work, output := out }
        rfl hcell0 hnostart rfl rfl rfl (fun _ _ => rfl)
    refine ⟨c', _, by omega, hreach, hhalt, hh1, ?_⟩
    exact hP_preserved inp work out c'.input c'.work c'.output hP
      (by rw [hcells]) hh1 hw' hinp'
      (by rw [hout']) (by rw [hout'])
  intro h; induction h with
  | zero =>
    intro c hstate hcell0_c hnostart_c hhead hinp_c hout_c hw_c
    have hread : (c.work idx).read = Γ.start := by simp [Tape.read, hhead, hcell0_c]
    -- Step 1: moveLeft, read ▷ → moveRight
    have hstep1 : ∃ c₁,
        (rewindWorkTM idx).step c = some c₁ ∧
        c₁.state = RewindPhase.moveRight ∧
        (c₁.work idx).head = 1 ∧ (c₁.work idx).cells = (c.work idx).cells ∧
        c₁.input = inp ∧ c₁.output = out ∧ (∀ i, i ≠ idx → c₁.work i = work i) := by
      simp only [TM.step, ↓reduceIte, hstate, rewindWorkTM, hread]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []; simp [Tape.writeAndMove, Tape.move, Tape.write, hhead]
      · dsimp only []; simp [Tape.writeAndMove, tape_move_cells, Tape.write, hhead]
      · dsimp only []; rw [hinp_c]; simp only [idleDir, hinp_ns, ↓reduceIte, Tape.move]
      · dsimp only []; rw [hout_c]; exact tape_idle_preserve out hout_ns hout_h
      · intro i hne; dsimp only []
        simp only [show ¬(i = idx) from hne, ↓reduceIte]
        rw [hw_c i hne]; exact tape_idle_preserve (work i) (hother_wf i hne).1 (hother_wf i hne).2
    obtain ⟨c₁, hstep1', hst1, hh1, hcells1, hinp1, hout1, hw1⟩ := hstep1
    -- Step 2: moveRight → done
    have hread1 : (c₁.work idx).read ≠ Γ.start := by
      simp [Tape.read, hh1, hcells1]; exact hnostart_c 1 (by omega)
    have hstep2 : ∃ c₂,
        (rewindWorkTM idx).step c₁ = some c₂ ∧
        (rewindWorkTM idx).halted c₂ ∧
        (c₂.work idx).head = 1 ∧ (c₂.work idx).cells = (c₁.work idx).cells ∧
        c₂.input = inp ∧ c₂.output = out ∧ (∀ i, i ≠ idx → c₂.work i = work i) := by
      simp only [TM.step, hst1, rewindWorkTM]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        have := tape_idle_preserve (c₁.work idx) hread1 (by omega)
        show ((c₁.work idx).writeAndMove (readBackWrite (c₁.work idx).read)
          (idleDir (c₁.work idx).read)).head = 1
        rw [this]; exact hh1
      · dsimp only []
        have := tape_idle_preserve (c₁.work idx) hread1 (by omega)
        show ((c₁.work idx).writeAndMove (readBackWrite (c₁.work idx).read)
          (idleDir (c₁.work idx).read)).cells = (c₁.work idx).cells
        rw [this]
      · dsimp only []; rw [hinp1]; simp only [idleDir, hinp_ns, ↓reduceIte, Tape.move]
      · dsimp only []; rw [hout1]; exact tape_idle_preserve out hout_ns hout_h
      · intro i hne; dsimp only []
        rw [hw1 i hne]; exact tape_idle_preserve (work i) (hother_wf i hne).1 (hother_wf i hne).2
    obtain ⟨c₂, hstep2', hhalt, hh2, hcells2, hinp2, hout2, hw2⟩ := hstep2
    exact ⟨c₂, .step hstep1' (.step hstep2' .zero), hhalt, hh2,
      by rw [hcells2, hcells1], hinp2, hout2, hw2⟩
  | succ h ih =>
    intro c hstate hcell0_c hnostart_c hhead hinp_c hout_c hw_c
    have hread_ne : (c.work idx).read ≠ Γ.start := by
      simp [Tape.read, hhead]; exact hnostart_c (h + 1) (by omega)
    -- Step: moveLeft, read non-▷ → stay in moveLeft, move left
    have hstep : ∃ c₁,
        (rewindWorkTM idx).step c = some c₁ ∧
        c₁.state = RewindPhase.moveLeft ∧
        (c₁.work idx).head = h ∧ (c₁.work idx).cells = (c.work idx).cells ∧
        c₁.input = inp ∧ c₁.output = out ∧ (∀ i, i ≠ idx → c₁.work i = work i) := by
      simp only [TM.step, ↓reduceIte, hstate, rewindWorkTM, hread_ne]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
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
      · dsimp only []; rw [hinp_c]; simp only [idleDir, hinp_ns, ↓reduceIte, Tape.move]
      · dsimp only []; rw [hout_c]; exact tape_idle_preserve out hout_ns hout_h
      · intro i hne; dsimp only []
        simp only [show ¬(i = idx) from hne, ↓reduceIte]
        rw [hw_c i hne]; exact tape_idle_preserve (work i) (hother_wf i hne).1 (hother_wf i hne).2
    obtain ⟨c₁, hstep', hst1, hh1, hcells1, hinp1, hout1, hw1⟩ := hstep
    obtain ⟨c_f, hreach_f, hhalt_f, hh_f, hcells_f, hinp_f, hout_f, hw_f⟩ :=
      ih c₁ hst1 (by rw [hcells1]; exact hcell0_c)
        (by intro j hj; rw [hcells1]; exact hnostart_c j hj) hh1 hinp1 hout1 hw1
    exact ⟨c_f, .step hstep' hreach_f, hhalt_f, hh_f,
      by rw [hcells_f, hcells1], hinp_f, hout_f, hw_f⟩

end TM
