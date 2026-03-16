import Complexitylib.Models.TuringMachine.Combinators

/-!
# Generic proof tools for TM combinators

This file provides reusable proof infrastructure for TM combinator proofs,
eliminating duplication across `SeqInternal`, `IfInternal`, `LoopInternal`,
and `ComplementInternal`.

## Main results

- `simulation_reachesIn` — generic simulation lifting: if a state embedding
  commutes with `step`, then `reachesIn` lifts through the embedding
- `generic_rewind_loop` — generic output-tape rewind: any TM where stepping
  from a "rewind state" moves the output head left (preserving cells), and
  at cell 0 moves right to cell 1 entering a "target state"
- `generic_rewind_loop_full` — same as above, also tracking input/work tapes

## Shared tape stability lemmas

These lemmas were previously duplicated across multiple Internal files.
-/

variable {n : ℕ}

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Shared tape lemmas (deduplicated from Internal files)
-- ════════════════════════════════════════════════════════════════════════

/-- Moving a tape preserves its cells. -/
theorem tape_move_cells (t : Tape) (d : Dir3) :
    (t.move d).cells = t.cells := by cases d <;> rfl

/-- `readBackWrite` recovers the original symbol for non-start symbols. -/
theorem readBackWrite_toΓ_eq {g : Γ} (h : g ≠ Γ.start) :
    (readBackWrite g).toΓ = g := by cases g <;> simp_all [readBackWrite, Γw.toΓ]

/-- Writing to a tape preserves the head position. -/
theorem tape_write_head (t : Tape) (s : Γ) : (t.write s).head = t.head := by
  simp only [Tape.write]; split <;> rfl

/-- A tape with head ≥ 1 and cells ≥ 1 ≠ start is stable under
    `writeAndMove(readBackWrite(read).toΓ, idleDir(read))`. -/
theorem tape_writeAndMove_stable (t : Tape)
    (hhead : t.head ≥ 1) (hns : ∀ j, j ≥ 1 → t.cells j ≠ Γ.start) :
    t.writeAndMove (readBackWrite t.read).toΓ (idleDir t.read) = t := by
  have hne : t.read ≠ Γ.start := by simp only [Tape.read]; exact hns t.head hhead
  rw [readBackWrite_toΓ_eq hne]
  show (t.write t.read).move (idleDir t.read) = t
  simp only [idleDir, hne, ↓reduceIte]
  show (t.write (t.cells t.head)).move .stay = t
  simp only [Tape.write, show ¬(t.head = 0) by omega, ↓reduceIte,
             Function.update_eq_self, Tape.move]

/-- A tape with head ≥ 1 and cells ≥ 1 ≠ start is stable under `move(idleDir(read))`. -/
theorem tape_move_idleDir_stable (t : Tape)
    (hhead : t.head ≥ 1) (hns : ∀ j, j ≥ 1 → t.cells j ≠ Γ.start) :
    t.move (idleDir t.read) = t := by
  have hne : t.read ≠ Γ.start := by simp only [Tape.read]; exact hns t.head hhead
  simp only [idleDir, hne, ↓reduceIte, Tape.move]

/-- `writeAndMove` head bound: head increases by at most 1. -/
theorem tape_head_writeAndMove_le (t : Tape) (s : Γ) (d : Dir3) :
    (t.writeAndMove s d).head ≤ t.head + 1 := by
  cases d <;> simp only [Tape.writeAndMove, Tape.move, tape_write_head] <;> omega

/-- Helper: readBackWrite preserves tape cells when head = 0 or read ≠ start. -/
theorem tape_readBackWrite_preserves (t : Tape) (d : Dir3)
    (h : t.head = 0 ∨ t.read ≠ Γ.start) :
    (t.writeAndMove (readBackWrite t.read).toΓ d).cells = t.cells := by
  simp only [Tape.writeAndMove, tape_move_cells]
  rcases h with hh0 | hne
  · simp only [Tape.write, hh0, ↓reduceIte]
  · rw [readBackWrite_toΓ_eq hne]
    simp only [Tape.write, Tape.read]; split
    · rfl
    · exact Function.update_eq_self _ _

-- ════════════════════════════════════════════════════════════════════════
-- Generic simulation lifting
-- ════════════════════════════════════════════════════════════════════════

/-- If `wrap` commutes with `step` (i.e., one step of `tm` corresponds to
    one step of `tm'` through the embedding), then `reachesIn` lifts. -/
theorem simulation_reachesIn {tm tm' : TM n}
    (wrap : Cfg n tm.Q → Cfg n tm'.Q)
    (h_step : ∀ c c' : Cfg n tm.Q, tm.step c = some c' →
      tm'.step (wrap c) = some (wrap c'))
    {t : ℕ} {c c' : Cfg n tm.Q}
    (hreach : tm.reachesIn t c c') :
    tm'.reachesIn t (wrap c) (wrap c') := by
  induction hreach with
  | zero => exact .zero
  | step hstep _ ih => exact .step (h_step _ _ hstep) ih

-- ════════════════════════════════════════════════════════════════════════
-- Generic output-tape rewind loop
-- ════════════════════════════════════════════════════════════════════════

/-- **Generic rewind loop (output tape only)**.

    For any TM with a designated "rewind state" where:
    - At head > 0: one step stays in rewind, moves head left by 1, preserves cells
    - At head = 0: one step enters target state, moves head to 1, preserves cells

    Then from rewind state with output head at `p`, the machine reaches the
    target state with output head at 1 in exactly `p + 1` steps.

    This captures the common rewind pattern used in `complementTM`, `ifTM`,
    and `loopTM`. -/
theorem generic_rewind_loop (tm : TM n)
    {rewindState targetState : tm.Q}
    (h_step_left : ∀ c : Cfg n tm.Q,
      c.state = rewindState →
      c.output.read ≠ Γ.start →
      c.output.cells 0 = Γ.start →
      (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) →
      ∃ c', tm.step c = some c' ∧
        c'.state = rewindState ∧
        c'.output.head = c.output.head - 1 ∧
        c'.output.cells = c.output.cells)
    (h_step_base : ∀ c : Cfg n tm.Q,
      c.state = rewindState →
      c.output.read = Γ.start →
      c.output.cells 0 = Γ.start →
      (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) →
      ∃ c', tm.step c = some c' ∧
        c'.state = targetState ∧
        c'.output.head = 1 ∧
        c'.output.cells = c.output.cells) :
    ∀ (p : ℕ) (c : Cfg n tm.Q),
    c.state = rewindState →
    c.output.cells 0 = Γ.start →
    (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) →
    c.output.head = p →
    ∃ c_target,
      tm.reachesIn (p + 1) c c_target ∧
      c_target.state = targetState ∧
      c_target.output.head = 1 ∧
      c_target.output.cells = c.output.cells := by
  intro p
  induction p with
  | zero =>
    intro c hstate hcell0 _ hhead
    have hread : c.output.read = Γ.start := by simp [Tape.read, hhead, hcell0]
    obtain ⟨c', hstep, hst, hh, hc⟩ := h_step_base c hstate hread hcell0 (by assumption)
    exact ⟨c', .step hstep .zero, hst, hh, hc⟩
  | succ p ih =>
    intro c hstate hcell0 hnostart hhead
    have hread_ne : c.output.read ≠ Γ.start := by
      simp [Tape.read, hhead]; exact hnostart (p + 1) (by omega)
    obtain ⟨c', hstep, hst, hh, hcells⟩ := h_step_left c hstate hread_ne hcell0 hnostart
    have hh' : c'.output.head = p := by rw [hh, hhead]; omega
    obtain ⟨c_target, hreach, hst_t, hh_t, hcells_t⟩ := ih c' hst
      (by rw [hcells]; exact hcell0)
      (by intro j hj; rw [hcells]; exact hnostart j hj) hh'
    exact ⟨c_target, .step hstep hreach, hst_t, hh_t, by rw [hcells_t, hcells]⟩

/-- **Generic rewind loop (full tape tracking)**.

    Same as `generic_rewind_loop`, but the step hypotheses also guarantee
    that input and work tapes are preserved (given stability conditions:
    head ≥ 1 and cells ≥ 1 ≠ start). The conclusion additionally proves
    `c_target.input = c.input` and `c_target.work = c.work`. -/
theorem generic_rewind_loop_full (tm : TM n)
    {rewindState targetState : tm.Q}
    (h_step_left : ∀ c : Cfg n tm.Q,
      c.state = rewindState →
      c.output.read ≠ Γ.start →
      c.output.cells 0 = Γ.start → (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) →
      c.input.head ≥ 1 → (∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) →
      (∀ i, (c.work i).head ≥ 1) → (∀ i j, j ≥ 1 → (c.work i).cells j ≠ Γ.start) →
      ∃ c', tm.step c = some c' ∧
        c'.state = rewindState ∧
        c'.output.head = c.output.head - 1 ∧
        c'.output.cells = c.output.cells ∧
        c'.input = c.input ∧ c'.work = c.work)
    (h_step_base : ∀ c : Cfg n tm.Q,
      c.state = rewindState →
      c.output.read = Γ.start →
      c.output.cells 0 = Γ.start → (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) →
      c.input.head ≥ 1 → (∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) →
      (∀ i, (c.work i).head ≥ 1) → (∀ i j, j ≥ 1 → (c.work i).cells j ≠ Γ.start) →
      ∃ c', tm.step c = some c' ∧
        c'.state = targetState ∧
        c'.output.head = 1 ∧
        c'.output.cells = c.output.cells ∧
        c'.input = c.input ∧ c'.work = c.work) :
    ∀ (p : ℕ) (c : Cfg n tm.Q),
    c.state = rewindState →
    c.output.cells 0 = Γ.start →
    (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) →
    c.output.head = p →
    c.input.head ≥ 1 → (∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) →
    (∀ i, (c.work i).head ≥ 1) → (∀ i j, j ≥ 1 → (c.work i).cells j ≠ Γ.start) →
    ∃ c_target,
      tm.reachesIn (p + 1) c c_target ∧
      c_target.state = targetState ∧
      c_target.output.head = 1 ∧
      c_target.output.cells = c.output.cells ∧
      c_target.input = c.input ∧
      c_target.work = c.work := by
  intro p
  induction p with
  | zero =>
    intro c hstate hcell0 _ hhead h_ih h_ins h_wh h_wns
    have hread : c.output.read = Γ.start := by simp [Tape.read, hhead, hcell0]
    obtain ⟨c', hstep, hst, hh, hcells, hinp, hwork⟩ :=
      h_step_base c hstate hread hcell0 (by assumption) h_ih h_ins h_wh h_wns
    exact ⟨c', .step hstep .zero, hst, hh, hcells, hinp, hwork⟩
  | succ p ih =>
    intro c hstate hcell0 hnostart hhead h_ih h_ins h_wh h_wns
    have hread_ne : c.output.read ≠ Γ.start := by
      simp [Tape.read, hhead]; exact hnostart (p + 1) (by omega)
    obtain ⟨c', hstep, hst, hh, hcells, hinp, hwork⟩ :=
      h_step_left c hstate hread_ne hcell0 hnostart h_ih h_ins h_wh h_wns
    have hh' : c'.output.head = p := by rw [hh, hhead]; omega
    obtain ⟨c_target, hreach, hst_t, hh_t, hcells_t, hinp_t, hwork_t⟩ := ih c' hst
      (by rw [hcells]; exact hcell0)
      (by intro j hj; rw [hcells]; exact hnostart j hj) hh'
      (by rw [hinp]; exact h_ih) (by rw [hinp]; exact h_ins)
      (by intro i; rw [hwork]; exact h_wh i)
      (by intro i j hj; rw [hwork]; exact h_wns i j hj)
    exact ⟨c_target, .step hstep hreach, hst_t, hh_t,
      by rw [hcells_t, hcells],
      by rw [hinp_t, hinp],
      by rw [hwork_t, hwork]⟩

end TM
