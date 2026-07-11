import Complexitylib.Models.TuringMachine.Combinators

namespace Complexity

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
    (t.move d).cells = t.cells :=
  Tape.move_cells t d

/-- `readBackWrite` recovers the original symbol for non-start symbols. -/
theorem readBackWrite_toΓ_eq {g : Γ} (h : g ≠ Γ.start) :
    (readBackWrite g).toΓ = g := by cases g <;> simp_all [readBackWrite, Γw.toΓ]

/-- Writing to a tape preserves the head position. -/
theorem tape_write_head (t : Tape) (s : Γ) : (t.write s).head = t.head := by
  exact Tape.write_head t s

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
-- Generic tape rewind loop (parameterized by tape accessor)
-- ════════════════════════════════════════════════════════════════════════

/-- **Generic rewind loop (abstract tape accessor)**.

    For any TM with a designated "rewind state" where stepping:
    - At head > 0: stays in rewind, moves head left by 1, preserves cells
    - At head = 0: enters target state, moves head to 1, preserves cells

    Then from rewind state with tape head at `p`, the machine reaches the
    target state with tape head at 1 in exactly `p + 1` steps.

    The `tape` parameter selects which tape to track (output, work, etc.).
    This captures the common rewind pattern used in `complementTM`, `ifTM`,
    `loopTM`, `writeTM`, and `rewindWorkTM`. -/
theorem generic_rewind_loop_tape (tm : TM n) (tape : Cfg n tm.Q → Tape)
    {rewindState targetState : tm.Q}
    (h_step_left : ∀ c : Cfg n tm.Q,
      c.state = rewindState →
      (tape c).read ≠ Γ.start →
      (tape c).cells 0 = Γ.start →
      (∀ j, j ≥ 1 → (tape c).cells j ≠ Γ.start) →
      ∃ c', tm.step c = some c' ∧
        c'.state = rewindState ∧
        (tape c').head = (tape c).head - 1 ∧
        (tape c').cells = (tape c).cells)
    (h_step_base : ∀ c : Cfg n tm.Q,
      c.state = rewindState →
      (tape c).read = Γ.start →
      (tape c).cells 0 = Γ.start →
      (∀ j, j ≥ 1 → (tape c).cells j ≠ Γ.start) →
      ∃ c', tm.step c = some c' ∧
        c'.state = targetState ∧
        (tape c').head = 1 ∧
        (tape c').cells = (tape c).cells) :
    ∀ (p : ℕ) (c : Cfg n tm.Q),
    c.state = rewindState →
    (tape c).cells 0 = Γ.start →
    (∀ j, j ≥ 1 → (tape c).cells j ≠ Γ.start) →
    (tape c).head = p →
    ∃ c_target,
      tm.reachesIn (p + 1) c c_target ∧
      c_target.state = targetState ∧
      (tape c_target).head = 1 ∧
      (tape c_target).cells = (tape c).cells := by
  intro p
  induction p with
  | zero =>
    intro c hstate hcell0 _ hhead
    have hread : (tape c).read = Γ.start := by simp [Tape.read, hhead, hcell0]
    obtain ⟨c', hstep, hst, hh, hc⟩ := h_step_base c hstate hread hcell0 (by assumption)
    exact ⟨c', .step hstep .zero, hst, hh, hc⟩
  | succ p ih =>
    intro c hstate hcell0 hnostart hhead
    have hread_ne : (tape c).read ≠ Γ.start := by
      simp [Tape.read, hhead]; exact hnostart (p + 1) (by omega)
    obtain ⟨c', hstep, hst, hh, hcells⟩ := h_step_left c hstate hread_ne hcell0 hnostart
    have hh' : (tape c').head = p := by rw [hh, hhead]; omega
    obtain ⟨c_target, hreach, hst_t, hh_t, hcells_t⟩ := ih c' hst
      (by rw [hcells]; exact hcell0)
      (by intro j hj; rw [hcells]; exact hnostart j hj) hh'
    exact ⟨c_target, .step hstep hreach, hst_t, hh_t, by rw [hcells_t, hcells]⟩

/-- Specialization of `generic_rewind_loop_tape` for the output tape. -/
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
      c_target.output.cells = c.output.cells :=
  generic_rewind_loop_tape tm (fun c => c.output) h_step_left h_step_base

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

-- ════════════════════════════════════════════════════════════════════════
-- Standard phase-transition tape operations
-- ════════════════════════════════════════════════════════════════════════

/-- The standard tape transformation applied at combinator phase boundaries
    (work tapes and output tape). Writes back the current symbol (preserving
    cells) and stays in place; if at cell 0, `δ_right_of_start` forces a
    right move to cell 1.

    Used by all combinators (`seqTM`, `ifTM`, `loopTM`, `complementTM`)
    at transitions between phases. -/
def transitionTape (t : Tape) : Tape :=
  t.writeAndMove (readBackWrite t.read).toΓ (idleDir t.read)

/-- The standard input-tape transformation at combinator phase boundaries.
    The input tape is read-only (no write), so only the head moves: stay
    in place unless at cell 0, where `δ_right_of_start` forces right. -/
def transitionInput (t : Tape) : Tape :=
  t.move (idleDir t.read)

/-- `transitionTape` preserves cells when cells ≥ 1 ≠ start. -/
theorem transitionTape_cells (t : Tape)
    (hns : ∀ j, j ≥ 1 → t.cells j ≠ Γ.start) :
    (transitionTape t).cells = t.cells := by
  simp only [transitionTape, Tape.writeAndMove, tape_move_cells]
  by_cases hh : t.head = 0
  · simp only [Tape.write, hh, ↓reduceIte]
  · have hge : t.head ≥ 1 := by omega
    rw [readBackWrite_toΓ_eq (by simp only [Tape.read]; exact hns t.head hge)]
    simp only [Tape.write, hh, ↓reduceIte, Tape.read, Function.update_eq_self]

/-- `transitionInput` preserves cells (always, since input has no write). -/
theorem transitionInput_cells (t : Tape) :
    (transitionInput t).cells = t.cells := by
  simp [transitionInput, Tape.move]; split <;> rfl

/-- After `transitionTape`, head ≥ 1 when cell 0 = start. -/
theorem transitionTape_head_ge (t : Tape) (h0 : t.cells 0 = Γ.start) :
    (transitionTape t).head ≥ 1 := by
  unfold transitionTape Tape.writeAndMove
  by_cases hh : t.head = 0
  · simp only [Tape.write, hh, ↓reduceIte, Tape.read, h0, idleDir, Tape.move]; omega
  · cases hdir : idleDir t.read with
    | stay => simp only [Tape.move, Tape.write, hh, ↓reduceIte]; omega
    | right => simp only [Tape.move, Tape.write, hh, ↓reduceIte]; omega
    | left => exfalso; revert hdir; simp only [idleDir]; split <;> simp

/-- After `transitionInput`, head ≥ 1 when cell 0 = start. -/
theorem transitionInput_head_ge (t : Tape) (h0 : t.cells 0 = Γ.start) :
    (transitionInput t).head ≥ 1 := by
  unfold transitionInput
  by_cases hh : t.head = 0
  · simp only [Tape.read, hh, h0, idleDir, ↓reduceIte, Tape.move]; omega
  · cases hdir : idleDir t.read with
    | stay => simp only [Tape.move]; omega
    | right => simp only [Tape.move]; omega
    | left => exfalso; revert hdir; simp only [idleDir]; split <;> simp

/-- Bound on `transitionTape` output head: ≤ original head + 1. -/
theorem transitionTape_head_bound {t : Tape} {p_bound : ℕ}
    (hcell0 : t.cells 0 = Γ.start) (hhead : t.head ≤ p_bound) :
    (transitionTape t).head ≤ p_bound + 1 := by
  unfold transitionTape Tape.writeAndMove
  by_cases hh : t.head = 0
  · simp only [Tape.write, hh, ↓reduceIte, Tape.read, hcell0, idleDir, Tape.move]; omega
  · cases hdir : idleDir t.read with
    | stay => simp only [Tape.move, Tape.write, hh, ↓reduceIte]; omega
    | right => simp only [Tape.move, Tape.write, hh, ↓reduceIte]; omega
    | left => exfalso; revert hdir; simp only [idleDir]; split <;> simp

-- ════════════════════════════════════════════════════════════════════════
-- Frame rules: transitionTape/transitionInput are identity on stable tapes
-- ════════════════════════════════════════════════════════════════════════

/-- **Frame rule**: `transitionTape` is the identity when the tape reads a
    non-▷ symbol. This is the key lemma for threading invariants through
    `seqTM` / `loopTM` / `ifTM` composition: tapes that are "stable"
    (head not at cell 0) pass through phase transitions unchanged. -/
theorem transitionTape_id {t : Tape} (hread : t.read ≠ Γ.start) :
    transitionTape t = t := by
  unfold transitionTape Tape.writeAndMove
  rw [readBackWrite_toΓ_eq hread]
  simp only [idleDir, hread, ↓reduceIte, Tape.move, Tape.write]
  split
  · rfl
  · simp only [Tape.read, Function.update_eq_self]

/-- **Frame rule**: `transitionInput` is the identity when the tape reads a
    non-▷ symbol. -/
theorem transitionInput_id {t : Tape} (hread : t.read ≠ Γ.start) :
    transitionInput t = t := by
  simp only [transitionInput, idleDir, hread, ↓reduceIte, Tape.move]

end TM

end Complexity
