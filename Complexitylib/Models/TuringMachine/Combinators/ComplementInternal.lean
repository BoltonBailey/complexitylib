import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.Combinators.Internal

/-!
# Complement TM: proof internals

This file provides the simulation lemmas for `TM.complementTM`, showing that
the complement machine correctly flips the output of the original TM.
-/

variable {n : ℕ}

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Tape helpers
-- ════════════════════════════════════════════════════════════════════════

private theorem tape_move_cells (t : Tape) (d : Dir3) :
    (t.move d).cells = t.cells := by cases d <;> rfl

private theorem readBackWrite_toΓ_eq' {g : Γ} (h : g ≠ Γ.start) :
    (readBackWrite g).toΓ = g := by cases g <;> simp_all [readBackWrite, Γw.toΓ]

private theorem tape_write_head (t : Tape) (s : Γ) : (t.write s).head = t.head := by
  simp only [Tape.write]; split <;> rfl

private theorem tape_head_writeAndMove_le (t : Tape) (s : Γ) (d : Dir3) :
    (t.writeAndMove s d).head ≤ t.head + 1 := by
  cases d <;> simp only [Tape.writeAndMove, Tape.move, tape_write_head] <;> omega

-- ════════════════════════════════════════════════════════════════════════
-- Configuration embedding
-- ════════════════════════════════════════════════════════════════════════

private def compCfg (tm : TM n) (c : Cfg n tm.Q) : Cfg n (tm.complementTM.Q) :=
  { state := Sum.inl c.state, input := c.input, work := c.work, output := c.output }

private theorem compCfg_initCfg (tm : TM n) (x : List Bool) :
    compCfg tm (tm.initCfg x) = tm.complementTM.initCfg x := rfl

-- ════════════════════════════════════════════════════════════════════════
-- Phase 1: Simulation
-- ════════════════════════════════════════════════════════════════════════

private theorem complementTM_step_sim (tm : TM n) {c c' : Cfg n tm.Q}
    (hstep : tm.step c = some c') :
    tm.complementTM.step (compCfg tm c) = some (compCfg tm c') := by
  have hne : c.state ≠ tm.qhalt := by intro heq; simp [TM.step, heq] at hstep
  simp only [TM.step, complementTM, compCfg] at hstep ⊢
  have hne2 : (Sum.inl c.state : ComplementQ tm.Q) ≠ Sum.inr .done := nofun
  simp only [hne, hne2, ↓reduceIte, Option.some.injEq] at hstep ⊢
  rw [← hstep]

private theorem complementTM_simulation (tm : TM n) {c c' : Cfg n tm.Q} {t : ℕ}
    (hreach : tm.reachesIn t c c') :
    tm.complementTM.reachesIn t (compCfg tm c) (compCfg tm c') := by
  induction hreach with
  | zero => exact .zero
  | @step _ _ _ _ hstep _ ih => exact .step (complementTM_step_sim tm hstep) ih

-- ════════════════════════════════════════════════════════════════════════
-- Rewind loop (property-based, by induction on head position)
-- ════════════════════════════════════════════════════════════════════════

/-- From rewind state with output head at position `h`, reach flip state
    at cell 1 with output cells preserved, in `h + 1` steps. -/
private theorem rewind_loop (tm : TM n) :
    ∀ (h : ℕ) (c : Cfg n tm.complementTM.Q),
    c.state = Sum.inr ComplementPhase.rewind →
    c.output.cells 0 = Γ.start →
    (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) →
    c.output.head = h →
    ∃ c_flip,
      tm.complementTM.reachesIn (h + 1) c c_flip ∧
      c_flip.state = Sum.inr ComplementPhase.flip ∧
      c_flip.output.head = 1 ∧
      c_flip.output.cells = c.output.cells := by
  intro h
  induction h with
  | zero =>
    intro c hstate hcell0 _ hhead
    -- Head at 0: output reads ▷ → rewind sees start → move right, enter flip
    have hne : c.state ≠ Sum.inr ComplementPhase.done := by rw [hstate]; nofun
    have hread : c.output.read = Γ.start := by simp [Tape.read, hhead, hcell0]
    -- Compute step
    have hstep : ∃ c', tm.complementTM.step c = some c' ∧
        c'.state = Sum.inr ComplementPhase.flip ∧
        c'.output.head = 1 ∧
        c'.output.cells = c.output.cells := by
      simp only [TM.step, ↓reduceIte, hstate, complementTM, hread]
      refine ⟨_, rfl, rfl, ?_, ?_⟩
      · simp [Tape.writeAndMove, Tape.move, Tape.write, hhead]
      · simp [Tape.writeAndMove, tape_move_cells, Tape.write, hhead]
    obtain ⟨c', hstep', hst', hh', hc'⟩ := hstep
    exact ⟨c', .step hstep' .zero, hst', hh', hc'⟩
  | succ h ih =>
    intro c hstate hcell0 hnostart hhead
    have hne : c.state ≠ Sum.inr ComplementPhase.done := by rw [hstate]; nofun
    -- Head at h+1 ≥ 1: output reads non-▷ → move left
    have hread_ne : c.output.read ≠ Γ.start := by
      simp [Tape.read, hhead]; exact hnostart (h + 1) (by omega)
    -- One step: state stays rewind, output head decreases, cells preserved
    have hstep : ∃ c', tm.complementTM.step c = some c' ∧
        c'.state = Sum.inr ComplementPhase.rewind ∧
        c'.output.head = h ∧
        c'.output.cells = c.output.cells := by
      simp only [TM.step, ↓reduceIte, hstate, complementTM, hread_ne]
      refine ⟨_, rfl, rfl, ?_, ?_⟩
      · -- head: writeAndMove ... left → head - 1
        simp only [Tape.writeAndMove, Tape.move]
        rw [readBackWrite_toΓ_eq' hread_ne]
        simp only [Tape.write]; split
        · omega  -- head = 0 contradicts hhead
        · simp [hhead]
      · -- cells preserved: writeAndMove readBackWrite left
        simp only [Tape.writeAndMove, tape_move_cells]
        rw [readBackWrite_toΓ_eq' hread_ne]
        simp only [Tape.write]; split
        · rfl  -- head = 0: no-op
        · exact Function.update_eq_self _ _
    obtain ⟨c', hstep', hst', hh', hc'⟩ := hstep
    obtain ⟨c_flip, hreach, hst_flip, hh_flip, hc_flip⟩ := ih c' hst'
      (by rw [hc']; exact hcell0) (by intro j hj; rw [hc']; exact hnostart j hj) hh'
    exact ⟨c_flip, .step hstep' hreach, hst_flip, hh_flip, by rw [hc_flip, hc']⟩

-- ════════════════════════════════════════════════════════════════════════
-- Combined: halt → rewind → flip → done
-- ════════════════════════════════════════════════════════════════════════

/-- From halted compCfg, reach done state with flipped output.
    Takes ≤ `output.head + 4` steps. -/
private theorem complementTM_rewind_and_flip (tm : TM n)
    (c_halt : Cfg n tm.Q)
    (hhalt : tm.halted c_halt)
    (hcell0 : c_halt.output.cells 0 = Γ.start)
    (hnostart : ∀ j, j ≥ 1 → c_halt.output.cells j ≠ Γ.start) :
    ∃ c_done t_rw,
      tm.complementTM.reachesIn t_rw (compCfg tm c_halt) c_done ∧
      tm.complementTM.halted c_done ∧
      c_done.output.cells 1 = (flipBit (c_halt.output.cells 1)).toΓ ∧
      t_rw ≤ c_halt.output.head + 4 := by
  -- Step 1: halt → rewind (1 step)
  have hne : (compCfg tm c_halt).state ≠ Sum.inr ComplementPhase.done := nofun
  have hstep1 : ∃ c_rw, tm.complementTM.step (compCfg tm c_halt) = some c_rw ∧
      c_rw.state = Sum.inr ComplementPhase.rewind ∧
      c_rw.output.cells = c_halt.output.cells ∧
      c_rw.output.head ≤ c_halt.output.head + 1 := by
    simp only [TM.step, ↓reduceIte, show (compCfg tm c_halt).state = Sum.inl c_halt.state from rfl,
               complementTM, hhalt]
    refine ⟨_, rfl, rfl, ?_, ?_⟩
    · -- cells preserved
      dsimp only [compCfg]
      simp only [Tape.writeAndMove, tape_move_cells]
      by_cases hread : c_halt.output.read = Γ.start
      · have hh0 : c_halt.output.head = 0 := by
          have h := hread; simp only [Tape.read] at h
          by_contra hne; exact hnostart _ (by omega) h
        simp [Tape.write, hh0]
      · rw [readBackWrite_toΓ_eq' hread]
        simp only [Tape.write]; split
        · rfl
        · exact Function.update_eq_self _ _
    · -- head ≤ original + 1
      dsimp only [compCfg]
      exact tape_head_writeAndMove_le _ _ _
  obtain ⟨c_rw, hstep1', hst_rw, hcells_rw, hhead_rw⟩ := hstep1
  -- Step 2: rewind loop (c_rw.output.head + 1 steps)
  have hcell0_rw : c_rw.output.cells 0 = Γ.start := by rw [hcells_rw]; exact hcell0
  have hnostart_rw : ∀ j, j ≥ 1 → c_rw.output.cells j ≠ Γ.start := by
    intro j hj; rw [hcells_rw]; exact hnostart j hj
  obtain ⟨c_flip, hreach_rw, hst_flip, hhead_flip, hcells_flip⟩ :=
    rewind_loop tm c_rw.output.head c_rw hst_rw hcell0_rw hnostart_rw rfl
  -- Step 3: flip (1 step)
  have hne_flip : c_flip.state ≠ Sum.inr ComplementPhase.done := by rw [hst_flip]; nofun
  have hnostart_flip : c_flip.output.read ≠ Γ.start := by
    simp [Tape.read, hhead_flip, hcells_flip, hcells_rw]
    exact hnostart 1 (by omega)
  have hne1 : c_halt.output.cells 1 ≠ Γ.start := hnostart 1 (by omega)
  have hstep3 : ∃ c_done, tm.complementTM.step c_flip = some c_done ∧
      c_done.state = Sum.inr ComplementPhase.done ∧
      c_done.output.cells 1 = (flipBit (c_halt.output.cells 1)).toΓ := by
    simp only [TM.step, hst_flip, complementTM]
    refine ⟨_, rfl, rfl, ?_⟩
    simp only [Tape.writeAndMove, Tape.move, Tape.write, Tape.read, hhead_flip,
               hcells_flip, hcells_rw]
    have hdir2 : idleDir (c_halt.output.cells 1) = Dir3.stay := by
      simp [idleDir, hne1]
    simp [hdir2, Function.update_self]
  obtain ⟨c_done, hstep3', hst_done, hflip⟩ := hstep3
  -- Compose: (head_rw + 1 + 1) + 1 ≤ (head + 1 + 1) + 1 = head + 3 + 1 ≤ head + 4
  refine ⟨c_done, ((c_rw.output.head + 1) + 1) + 1,
    reachesIn_trans tm.complementTM (.step hstep1' hreach_rw) (.step hstep3' .zero),
    hst_done, hflip, by omega⟩

-- ════════════════════════════════════════════════════════════════════════
-- Main theorem
-- ════════════════════════════════════════════════════════════════════════

/-- If `tm` decides `L` in time `f`, then `complementTM tm` decides `Lᶜ`
    in time `2 * f + 4`. -/
theorem complementTM_decidesInTime (tm : TM n) {L : Language} {f : ℕ → ℕ}
    (hdec : tm.DecidesInTime L f) :
    tm.complementTM.DecidesInTime Lᶜ (fun n => 2 * f n + 4) := by
  intro x
  obtain ⟨c', t, hle, hreach, hhalt, hyes, hno⟩ := hdec x
  have hsim := complementTM_simulation tm hreach
  rw [compCfg_initCfg] at hsim
  have ⟨_, hout_head, _⟩ := head_bound_of_reachesIn tm hreach
  have hcell0 := output_cell0_of_reachesIn hreach (by simp [initTape])
  have hnostart := output_noStart_of_reachesIn hreach (by
    intro i hi; simp [initTape]; omega)
  obtain ⟨c_done, t_rw, hreach_rw, hhalt_done, hflip, hle_rw⟩ :=
    complementTM_rewind_and_flip tm c' hhalt hcell0 hnostart
  have htotal := reachesIn_trans tm.complementTM hsim hreach_rw
  refine ⟨c_done, t + t_rw, ?_, htotal, hhalt_done, ?_, ?_⟩
  · show t + t_rw ≤ 2 * f x.length + 4
    have : t_rw ≤ t + 4 := le_trans hle_rw (by omega)
    omega
  · intro hxc; rw [hflip, hno hxc]; simp [flipBit]
  · intro hxc
    simp only [Set.mem_compl_iff, not_not] at hxc
    rw [hflip, hyes hxc]; simp [flipBit]

end TM
