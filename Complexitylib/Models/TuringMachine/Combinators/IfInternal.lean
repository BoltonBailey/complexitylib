import Complexitylib.Models.TuringMachine.Combinators

/-!
# ifTM simulation — proof internals

This file contains the simulation lemmas for `ifTM tmTest tmThen tmElse`.

## Key definitions

- `ifTestWrap` — embed a `tmTest` config into the `ifTM` config space
- `ifThenWrap` — embed a `tmThen` config into the `ifTM` config space
- `ifElseWrap` — embed a `tmElse` config into the `ifTM` config space
-/

variable {n : ℕ}

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Config wrapping
-- ════════════════════════════════════════════════════════════════════════

def ifTestWrap (tmTest : TM n) (tmThen : TM n) (tmElse : TM n)
    (c : Cfg n tmTest.Q) : Cfg n (IfQ tmTest.Q tmThen.Q tmElse.Q) where
  state := Sum.inl c.state
  input := c.input
  work := c.work
  output := c.output

def ifThenWrap (tmTest : TM n) (tmThen : TM n) (tmElse : TM n)
    (c : Cfg n tmThen.Q) : Cfg n (IfQ tmTest.Q tmThen.Q tmElse.Q) where
  state := Sum.inr (Sum.inr (Sum.inl c.state))
  input := c.input
  work := c.work
  output := c.output

def ifElseWrap (tmTest : TM n) (tmThen : TM n) (tmElse : TM n)
    (c : Cfg n tmElse.Q) : Cfg n (IfQ tmTest.Q tmThen.Q tmElse.Q) where
  state := Sum.inr (Sum.inr (Sum.inr c.state))
  input := c.input
  work := c.work
  output := c.output

-- ════════════════════════════════════════════════════════════════════════
-- Sum discrimination helpers
-- ════════════════════════════════════════════════════════════════════════

private theorem ifQ_test_ne_halt {QT QThen QElse : Type} {q : QT} :
    (Sum.inl q : IfQ QT QThen QElse) ≠ Sum.inr (Sum.inl IfPhase.done) := nofun

private theorem ifQ_then_ne_halt {QT QThen QElse : Type} {q : QThen} :
    (Sum.inr (Sum.inr (Sum.inl q)) : IfQ QT QThen QElse) ≠
      Sum.inr (Sum.inl IfPhase.done) := nofun

private theorem ifQ_else_ne_halt {QT QThen QElse : Type} {q : QElse} :
    (Sum.inr (Sum.inr (Sum.inr q)) : IfQ QT QThen QElse) ≠
      Sum.inr (Sum.inl IfPhase.done) := nofun

private theorem ifQ_phase_ne_halt {QT QThen QElse : Type}
    {p : IfPhase} (hp : p ≠ .done) :
    (Sum.inr (Sum.inl p) : IfQ QT QThen QElse) ≠
      Sum.inr (Sum.inl IfPhase.done) :=
  fun h => hp (Sum.inl.inj (Sum.inr.inj h))

-- ════════════════════════════════════════════════════════════════════════
-- Test phase: ifTM simulates tmTest
-- ════════════════════════════════════════════════════════════════════════

/-- One step of `tmTest` corresponds to one step of `ifTM` during the test phase. -/
theorem ifTM_test_step (tmTest tmThen tmElse : TM n) {c c' : Cfg n tmTest.Q}
    (hstep : tmTest.step c = some c') :
    (ifTM tmTest tmThen tmElse).step (ifTestWrap tmTest tmThen tmElse c) =
      some (ifTestWrap tmTest tmThen tmElse c') := by
  have hne : c.state ≠ tmTest.qhalt := by intro heq; simp [step, heq] at hstep
  simp only [step, hne, ↓reduceIte, Option.some.injEq] at hstep
  subst hstep
  show (if (ifTestWrap tmTest tmThen tmElse c).state =
           (ifTM tmTest tmThen tmElse).qhalt then none else some _) = some _
  simp only [ifTestWrap, ifTM, if_neg ifQ_test_ne_halt, if_neg hne]

/-- Multi-step test phase simulation. -/
theorem ifTM_test_simulation (tmTest tmThen tmElse : TM n) {t : ℕ}
    {c_start c_end : Cfg n tmTest.Q}
    (hreach : tmTest.reachesIn t c_start c_end) :
    (ifTM tmTest tmThen tmElse).reachesIn t
      (ifTestWrap tmTest tmThen tmElse c_start)
      (ifTestWrap tmTest tmThen tmElse c_end) := by
  induction hreach with
  | zero => exact .zero
  | step hstep _ ih => exact .step (ifTM_test_step tmTest tmThen tmElse hstep) ih

-- ════════════════════════════════════════════════════════════════════════
-- Then branch: ifTM simulates tmThen
-- ════════════════════════════════════════════════════════════════════════

/-- One step of `tmThen` corresponds to one step of `ifTM` during the then branch. -/
theorem ifTM_then_step (tmTest tmThen tmElse : TM n) {c c' : Cfg n tmThen.Q}
    (hstep : tmThen.step c = some c') :
    (ifTM tmTest tmThen tmElse).step (ifThenWrap tmTest tmThen tmElse c) =
      some (ifThenWrap tmTest tmThen tmElse c') := by
  have hne : c.state ≠ tmThen.qhalt := by intro heq; simp [step, heq] at hstep
  simp only [step, hne, ↓reduceIte, Option.some.injEq] at hstep
  subst hstep
  show (if (ifThenWrap tmTest tmThen tmElse c).state =
           (ifTM tmTest tmThen tmElse).qhalt then none else some _) = some _
  simp only [ifThenWrap, ifTM, if_neg ifQ_then_ne_halt, if_neg hne]

/-- Multi-step then-branch simulation. -/
theorem ifTM_then_simulation (tmTest tmThen tmElse : TM n) {t : ℕ}
    {c_start c_end : Cfg n tmThen.Q}
    (hreach : tmThen.reachesIn t c_start c_end) :
    (ifTM tmTest tmThen tmElse).reachesIn t
      (ifThenWrap tmTest tmThen tmElse c_start)
      (ifThenWrap tmTest tmThen tmElse c_end) := by
  induction hreach with
  | zero => exact .zero
  | step hstep _ ih => exact .step (ifTM_then_step tmTest tmThen tmElse hstep) ih

-- ════════════════════════════════════════════════════════════════════════
-- Else branch: ifTM simulates tmElse
-- ════════════════════════════════════════════════════════════════════════

/-- One step of `tmElse` corresponds to one step of `ifTM` during the else branch. -/
theorem ifTM_else_step (tmTest tmThen tmElse : TM n) {c c' : Cfg n tmElse.Q}
    (hstep : tmElse.step c = some c') :
    (ifTM tmTest tmThen tmElse).step (ifElseWrap tmTest tmThen tmElse c) =
      some (ifElseWrap tmTest tmThen tmElse c') := by
  have hne : c.state ≠ tmElse.qhalt := by intro heq; simp [step, heq] at hstep
  simp only [step, hne, ↓reduceIte, Option.some.injEq] at hstep
  subst hstep
  show (if (ifElseWrap tmTest tmThen tmElse c).state =
           (ifTM tmTest tmThen tmElse).qhalt then none else some _) = some _
  simp only [ifElseWrap, ifTM, if_neg ifQ_else_ne_halt, if_neg hne]

/-- Multi-step else-branch simulation. -/
theorem ifTM_else_simulation (tmTest tmThen tmElse : TM n) {t : ℕ}
    {c_start c_end : Cfg n tmElse.Q}
    (hreach : tmElse.reachesIn t c_start c_end) :
    (ifTM tmTest tmThen tmElse).reachesIn t
      (ifElseWrap tmTest tmThen tmElse c_start)
      (ifElseWrap tmTest tmThen tmElse c_end) := by
  induction hreach with
  | zero => exact .zero
  | step hstep _ ih => exact .step (ifTM_else_step tmTest tmThen tmElse hstep) ih

-- ════════════════════════════════════════════════════════════════════════
-- Halt transitions: branch halt → done
-- ════════════════════════════════════════════════════════════════════════

/-- The tape transformation applied by halt-to-done transitions. Same as
    `seqTransitionTape`/`seqTransitionInput`: preserves cells, moves heads
    at position 0 to position 1. -/
def ifTransitionTape (t : Tape) : Tape :=
  t.writeAndMove (readBackWrite t.read).toΓ (idleDir t.read)

def ifTransitionInput (t : Tape) : Tape :=
  t.move (idleDir t.read)

/-- When `tmThen` halts, one step transitions to `done`. -/
theorem ifTM_then_halt_step (tmTest tmThen tmElse : TM n) {c : Cfg n tmThen.Q}
    (hhalt : c.state = tmThen.qhalt) :
    (ifTM tmTest tmThen tmElse).step (ifThenWrap tmTest tmThen tmElse c) =
      some { state := Sum.inr (Sum.inl IfPhase.done),
             input := ifTransitionInput c.input,
             work := fun i => ifTransitionTape (c.work i),
             output := ifTransitionTape c.output } := by
  show (if (ifThenWrap tmTest tmThen tmElse c).state =
           (ifTM tmTest tmThen tmElse).qhalt then none else some _) = some _
  simp only [ifThenWrap, ifTM, if_neg ifQ_then_ne_halt, hhalt, ↓reduceIte]
  congr 1

/-- When `tmElse` halts, one step transitions to `done`. -/
theorem ifTM_else_halt_step (tmTest tmThen tmElse : TM n) {c : Cfg n tmElse.Q}
    (hhalt : c.state = tmElse.qhalt) :
    (ifTM tmTest tmThen tmElse).step (ifElseWrap tmTest tmThen tmElse c) =
      some { state := Sum.inr (Sum.inl IfPhase.done),
             input := ifTransitionInput c.input,
             work := fun i => ifTransitionTape (c.work i),
             output := ifTransitionTape c.output } := by
  show (if (ifElseWrap tmTest tmThen tmElse c).state =
           (ifTM tmTest tmThen tmElse).qhalt then none else some _) = some _
  simp only [ifElseWrap, ifTM, if_neg ifQ_else_ne_halt, hhalt, ↓reduceIte]
  congr 1

-- ════════════════════════════════════════════════════════════════════════
-- Test phase → rewind transition
-- ════════════════════════════════════════════════════════════════════════

/-- When `tmTest` halts, one step enters the rewindOut phase. -/
theorem ifTM_test_to_rewind (tmTest tmThen tmElse : TM n) {c : Cfg n tmTest.Q}
    (hhalt : c.state = tmTest.qhalt) :
    (ifTM tmTest tmThen tmElse).step (ifTestWrap tmTest tmThen tmElse c) =
      some { state := Sum.inr (Sum.inl IfPhase.rewindOut),
             input := ifTransitionInput c.input,
             work := fun i => ifTransitionTape (c.work i),
             output := ifTransitionTape c.output } := by
  show (if (ifTestWrap tmTest tmThen tmElse c).state =
           (ifTM tmTest tmThen tmElse).qhalt then none else some _) = some _
  simp only [ifTestWrap, ifTM, if_neg ifQ_test_ne_halt, hhalt, ↓reduceIte]
  congr 1

-- ════════════════════════════════════════════════════════════════════════
-- Halting
-- ════════════════════════════════════════════════════════════════════════

theorem ifTM_done_is_halted (tmTest tmThen tmElse : TM n) :
    (ifTM tmTest tmThen tmElse).qhalt = Sum.inr (Sum.inl IfPhase.done) := rfl

/-- The `done` state is halted in `ifTM`. -/
theorem ifTM_halted_done (tmTest tmThen tmElse : TM n)
    (c : Cfg n (IfQ tmTest.Q tmThen.Q tmElse.Q))
    (h : c.state = Sum.inr (Sum.inl IfPhase.done)) :
    (ifTM tmTest tmThen tmElse).halted c := h

-- ════════════════════════════════════════════════════════════════════════
-- Tape helpers
-- ════════════════════════════════════════════════════════════════════════

private theorem tape_move_cells (t : Tape) (d : Dir3) :
    (t.move d).cells = t.cells := by cases d <;> rfl

private theorem readBackWrite_toΓ_eq' {g : Γ} (h : g ≠ Γ.start) :
    (readBackWrite g).toΓ = g := by cases g <;> simp_all [readBackWrite, Γw.toΓ]

-- ════════════════════════════════════════════════════════════════════════
-- Rewind loop
-- ════════════════════════════════════════════════════════════════════════

/-- The full rewind loop: from rewindOut with output head at position `p`,
    reach check state at cell 1 in `p + 1` steps. Output cells are preserved. -/
theorem ifTM_rewind_loop (tmTest tmThen tmElse : TM n) :
    ∀ (p : ℕ) (c : Cfg n (IfQ tmTest.Q tmThen.Q tmElse.Q)),
    c.state = Sum.inr (Sum.inl IfPhase.rewindOut) →
    c.output.cells 0 = Γ.start →
    (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) →
    c.output.head = p →
    ∃ c_check,
      (ifTM tmTest tmThen tmElse).reachesIn (p + 1) c c_check ∧
      c_check.state = Sum.inr (Sum.inl IfPhase.check) ∧
      c_check.output.head = 1 ∧
      c_check.output.cells = c.output.cells := by
  intro p
  induction p with
  | zero =>
    intro c hstate hcell0 _ hhead
    have hne : c.state ≠ (ifTM tmTest tmThen tmElse).qhalt := by rw [hstate]; nofun
    have hread : c.output.read = Γ.start := by simp [Tape.read, hhead, hcell0]
    -- At cell 0: delta gives (.check, .blank, Dir3.right) for output
    have hstep : ∃ c', (ifTM tmTest tmThen tmElse).step c = some c' ∧
        c'.state = Sum.inr (Sum.inl IfPhase.check) ∧
        c'.output.head = 1 ∧
        c'.output.cells = c.output.cells := by
      simp only [TM.step, ↓reduceIte, hstate, ifTM, hread]
      refine ⟨_, rfl, rfl, ?_, ?_⟩
      · simp [Tape.writeAndMove, Tape.move, Tape.write, hhead]
      · simp [Tape.writeAndMove, tape_move_cells, Tape.write, hhead]
    obtain ⟨c', hstep', hst', hh', hc'⟩ := hstep
    exact ⟨c', .step hstep' .zero, hst', hh', hc'⟩
  | succ p ih =>
    intro c hstate hcell0 hnostart hhead
    have hne : c.state ≠ (ifTM tmTest tmThen tmElse).qhalt := by rw [hstate]; nofun
    have hread_ne : c.output.read ≠ Γ.start := by
      simp only [Tape.read, hhead]; exact hnostart (p + 1) (by omega)
    -- Not at cell 0: delta gives (.rewindOut, readBackWrite oHead, Dir3.left) for output
    have hstep : ∃ c', (ifTM tmTest tmThen tmElse).step c = some c' ∧
        c'.state = Sum.inr (Sum.inl IfPhase.rewindOut) ∧
        c'.output.head = p ∧
        c'.output.cells = c.output.cells := by
      simp only [TM.step, ↓reduceIte, hstate, ifTM, hread_ne]
      refine ⟨_, rfl, rfl, ?_, ?_⟩
      · -- head: writeAndMove (readBackWrite ...) left → head - 1
        simp only [Tape.writeAndMove, Tape.move]
        rw [readBackWrite_toΓ_eq' hread_ne]
        simp only [Tape.write, Tape.read]; split
        · omega  -- head = 0 contradicts hread_ne
        · simp [hhead]
      · -- cells: readBackWrite writes back the same symbol
        simp only [Tape.writeAndMove, tape_move_cells]
        rw [readBackWrite_toΓ_eq' hread_ne]
        simp only [Tape.write, Tape.read]; split
        · rfl  -- head = 0: write is no-op
        · exact Function.update_eq_self _ _
    obtain ⟨c', hstep', hst', hh', hcells'⟩ := hstep
    obtain ⟨c_check, hreach, hst_check, hh_check, hcells_check⟩ := ih c' hst'
      (by rw [hcells']; exact hcell0)
      (by intro j hj; rw [hcells']; exact hnostart j hj) hh'
    exact ⟨c_check, .step hstep' hreach, hst_check, hh_check,
      by rw [hcells_check, hcells']⟩

-- ════════════════════════════════════════════════════════════════════════
-- Check step: read output at cell 1, branch to then or else
-- ════════════════════════════════════════════════════════════════════════

/-- Helper: readBackWrite preserves tape cells when head ≥ 1 and cells[≥1] ≠ start,
    or when head = 0. -/
private theorem tape_readBackWrite_preserves (t : Tape) (d : Dir3)
    (h : t.head = 0 ∨ t.read ≠ Γ.start) :
    (t.writeAndMove (readBackWrite t.read).toΓ d).cells = t.cells := by
  simp only [Tape.writeAndMove, tape_move_cells]
  rcases h with hh0 | hne
  · simp only [Tape.write, hh0, ↓reduceIte]
  · rw [readBackWrite_toΓ_eq' hne]
    simp only [Tape.write, Tape.read]; split
    · rfl
    · exact Function.update_eq_self _ _

/-- Check step when output cell 1 = Γ.one: branch to tmThen.
    Requires the nostart invariant on output for cell preservation. -/
theorem ifTM_check_step_then (tmTest tmThen tmElse : TM n)
    (c : Cfg n (IfQ tmTest.Q tmThen.Q tmElse.Q))
    (hstate : c.state = Sum.inr (Sum.inl IfPhase.check))
    (hhead : c.output.head = 1)
    (hcell1 : c.output.cells 1 = Γ.one) :
    ∃ c', (ifTM tmTest tmThen tmElse).step c = some c' ∧
      c'.state = Sum.inr (Sum.inr (Sum.inl tmThen.qstart)) ∧
      c'.output.cells = c.output.cells := by
  have hne : c.state ≠ (ifTM tmTest tmThen tmElse).qhalt := by rw [hstate]; nofun
  have hread : c.output.read = Γ.one := by simp [Tape.read, hhead, hcell1]
  simp only [TM.step, ↓reduceIte, hstate, ifTM, hread]
  refine ⟨_, rfl, rfl, ?_⟩
  -- The goal has `readBackWrite Γ.one` (simp already substituted hread).
  -- We compute directly: readBackWrite Γ.one = .one, .one.toΓ = Γ.one, idleDir Γ.one = .stay
  show (c.output.writeAndMove (readBackWrite Γ.one).toΓ (idleDir Γ.one)).cells = c.output.cells
  simp only [readBackWrite, Γw.toΓ, idleDir, Tape.writeAndMove, tape_move_cells]
  simp only [Tape.write]; split
  · omega  -- 1 = 0 is absurd
  · dsimp only []; rw [hhead, ← hcell1]; exact Function.update_eq_self _ _

/-- Check step when output cell 1 ≠ Γ.one: branch to tmElse.
    Requires the nostart invariant on output for cell preservation. -/
theorem ifTM_check_step_else (tmTest tmThen tmElse : TM n)
    (c : Cfg n (IfQ tmTest.Q tmThen.Q tmElse.Q))
    (hstate : c.state = Sum.inr (Sum.inl IfPhase.check))
    (hhead : c.output.head = 1)
    (hcell1 : c.output.cells 1 ≠ Γ.one)
    (hnostart_out : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', (ifTM tmTest tmThen tmElse).step c = some c' ∧
      c'.state = Sum.inr (Sum.inr (Sum.inr tmElse.qstart)) ∧
      c'.output.cells = c.output.cells := by
  have hne : c.state ≠ (ifTM tmTest tmThen tmElse).qhalt := by rw [hstate]; nofun
  have hread_ne_one : c.output.read ≠ Γ.one := by
    simp [Tape.read, hhead]; exact hcell1
  have hread_ne_start : c.output.read ≠ Γ.start := by
    simp only [Tape.read, hhead]; exact hnostart_out 1 (by omega)
  simp only [TM.step, ↓reduceIte, hstate, ifTM, hread_ne_one]
  refine ⟨_, rfl, rfl, ?_⟩
  apply tape_readBackWrite_preserves
  right; exact hread_ne_start

end TM
