import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic

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

/-- Embed a `tmTest` config into the `ifTM` config space (test phase). -/
def ifTestWrap (tmTest : TM n) (tmThen : TM n) (tmElse : TM n)
    (c : Cfg n tmTest.Q) : Cfg n (IfQ tmTest.Q tmThen.Q tmElse.Q) where
  state := Sum.inl c.state
  input := c.input
  work := c.work
  output := c.output

/-- Embed a `tmThen` config into the `ifTM` config space (then branch). -/
def ifThenWrap (tmTest : TM n) (tmThen : TM n) (tmElse : TM n)
    (c : Cfg n tmThen.Q) : Cfg n (IfQ tmTest.Q tmThen.Q tmElse.Q) where
  state := Sum.inr (Sum.inr (Sum.inl c.state))
  input := c.input
  work := c.work
  output := c.output

/-- Embed a `tmElse` config into the `ifTM` config space (else branch). -/
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
-- Test phase: ifTM simulates tmTest (via generic simulation lifting)
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
      (ifTestWrap tmTest tmThen tmElse c_end) :=
  simulation_reachesIn (tm' := ifTM tmTest tmThen tmElse) (ifTestWrap tmTest tmThen tmElse)
    (fun _ _ => ifTM_test_step tmTest tmThen tmElse) hreach

-- ════════════════════════════════════════════════════════════════════════
-- Then branch: ifTM simulates tmThen (via generic simulation lifting)
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
      (ifThenWrap tmTest tmThen tmElse c_end) :=
  simulation_reachesIn (tm' := ifTM tmTest tmThen tmElse) (ifThenWrap tmTest tmThen tmElse)
    (fun _ _ => ifTM_then_step tmTest tmThen tmElse) hreach

-- ════════════════════════════════════════════════════════════════════════
-- Else branch: ifTM simulates tmElse (via generic simulation lifting)
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
      (ifElseWrap tmTest tmThen tmElse c_end) :=
  simulation_reachesIn (tm' := ifTM tmTest tmThen tmElse) (ifElseWrap tmTest tmThen tmElse)
    (fun _ _ => ifTM_else_step tmTest tmThen tmElse) hreach

-- ════════════════════════════════════════════════════════════════════════
-- Halt transitions: branch halt → done
-- ════════════════════════════════════════════════════════════════════════

/-- When `tmThen` halts, one step transitions to `done`. -/
theorem ifTM_then_halt_step (tmTest tmThen tmElse : TM n) {c : Cfg n tmThen.Q}
    (hhalt : c.state = tmThen.qhalt) :
    (ifTM tmTest tmThen tmElse).step (ifThenWrap tmTest tmThen tmElse c) =
      some { state := Sum.inr (Sum.inl IfPhase.done),
             input := transitionInput c.input,
             work := fun i => transitionTape (c.work i),
             output := transitionTape c.output } := by
  show (if (ifThenWrap tmTest tmThen tmElse c).state =
           (ifTM tmTest tmThen tmElse).qhalt then none else some _) = some _
  simp only [ifThenWrap, ifTM, if_neg ifQ_then_ne_halt, hhalt, ↓reduceIte]
  congr 1

/-- When `tmElse` halts, one step transitions to `done`. -/
theorem ifTM_else_halt_step (tmTest tmThen tmElse : TM n) {c : Cfg n tmElse.Q}
    (hhalt : c.state = tmElse.qhalt) :
    (ifTM tmTest tmThen tmElse).step (ifElseWrap tmTest tmThen tmElse c) =
      some { state := Sum.inr (Sum.inl IfPhase.done),
             input := transitionInput c.input,
             work := fun i => transitionTape (c.work i),
             output := transitionTape c.output } := by
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
             input := transitionInput c.input,
             work := fun i => transitionTape (c.work i),
             output := transitionTape c.output } := by
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
-- Rewind loop (via generic rewind)
-- ════════════════════════════════════════════════════════════════════════

private theorem if_rewind_step_left (tmTest tmThen tmElse : TM n)
    (c : Cfg n (IfQ tmTest.Q tmThen.Q tmElse.Q))
    (hstate : c.state = Sum.inr (Sum.inl IfPhase.rewindOut))
    (hread_ne : c.output.read ≠ Γ.start)
    (_ : c.output.cells 0 = Γ.start) (_ : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', (ifTM tmTest tmThen tmElse).step c = some c' ∧
      c'.state = Sum.inr (Sum.inl IfPhase.rewindOut) ∧
      c'.output.head = c.output.head - 1 ∧
      c'.output.cells = c.output.cells := by
  have hne : c.state ≠ (ifTM tmTest tmThen tmElse).qhalt := by rw [hstate]; nofun
  simp only [TM.step, ↓reduceIte, hstate, ifTM, hread_ne]
  refine ⟨_, rfl, rfl, ?_, ?_⟩
  · simp only [Tape.writeAndMove, Tape.move]
    rw [readBackWrite_toΓ_eq hread_ne]
    simp only [Tape.write, Tape.read]; split
    · omega
    · simp
  · simp only [Tape.writeAndMove, tape_move_cells]
    rw [readBackWrite_toΓ_eq hread_ne]
    simp only [Tape.write, Tape.read]; split
    · rfl
    · exact Function.update_eq_self _ _

private theorem if_rewind_step_base (tmTest tmThen tmElse : TM n)
    (c : Cfg n (IfQ tmTest.Q tmThen.Q tmElse.Q))
    (hstate : c.state = Sum.inr (Sum.inl IfPhase.rewindOut))
    (hread : c.output.read = Γ.start)
    (_ : c.output.cells 0 = Γ.start)
    (hnostart : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', (ifTM tmTest tmThen tmElse).step c = some c' ∧
      c'.state = Sum.inr (Sum.inl IfPhase.check) ∧
      c'.output.head = 1 ∧
      c'.output.cells = c.output.cells := by
  have hne : c.state ≠ (ifTM tmTest tmThen tmElse).qhalt := by rw [hstate]; nofun
  have hhead : c.output.head = 0 := by
    by_contra hne
    exact hnostart c.output.head (by omega) (by simp only [Tape.read] at hread; exact hread)
  simp only [TM.step, ↓reduceIte, hstate, ifTM, hread]
  refine ⟨_, rfl, rfl, ?_, ?_⟩
  · simp [Tape.writeAndMove, Tape.move, Tape.write, hhead]
  · simp [Tape.writeAndMove, tape_move_cells, Tape.write, hhead]

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
      c_check.output.cells = c.output.cells :=
  generic_rewind_loop (ifTM tmTest tmThen tmElse)
    (fun c hst hread hc0 hns => if_rewind_step_left tmTest tmThen tmElse c hst hread hc0 hns)
    (fun c hst hread hc0 hns => if_rewind_step_base tmTest tmThen tmElse c hst hread hc0 hns)

-- ════════════════════════════════════════════════════════════════════════
-- Rewind loop (full tape tracking, via generic rewind)
-- ════════════════════════════════════════════════════════════════════════

private theorem if_rewind_step_left_full (tmTest tmThen tmElse : TM n)
    (c : Cfg n (IfQ tmTest.Q tmThen.Q tmElse.Q))
    (hstate : c.state = Sum.inr (Sum.inl IfPhase.rewindOut))
    (hread_ne : c.output.read ≠ Γ.start)
    (_ : c.output.cells 0 = Γ.start) (_ : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start)
    (h_ih : c.input.head ≥ 1) (h_ins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (h_wh : ∀ i, (c.work i).head ≥ 1) (h_wns : ∀ i j, j ≥ 1 → (c.work i).cells j ≠ Γ.start) :
    ∃ c', (ifTM tmTest tmThen tmElse).step c = some c' ∧
      c'.state = Sum.inr (Sum.inl IfPhase.rewindOut) ∧
      c'.output.head = c.output.head - 1 ∧
      c'.output.cells = c.output.cells ∧
      c'.input = c.input ∧ c'.work = c.work := by
  have hne : c.state ≠ (ifTM tmTest tmThen tmElse).qhalt := by rw [hstate]; nofun
  simp only [TM.step, ↓reduceIte, hstate, ifTM, hread_ne]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [Tape.writeAndMove, Tape.move]
    rw [readBackWrite_toΓ_eq hread_ne]
    simp only [Tape.write, Tape.read]; split
    · omega
    · simp
  · simp only [Tape.writeAndMove, tape_move_cells]
    rw [readBackWrite_toΓ_eq hread_ne]
    simp only [Tape.write, Tape.read]; split
    · rfl
    · exact Function.update_eq_self _ _
  · exact tape_move_idleDir_stable _ h_ih h_ins
  · ext i; exact tape_writeAndMove_stable _ (h_wh i) (h_wns i)

private theorem if_rewind_step_base_full (tmTest tmThen tmElse : TM n)
    (c : Cfg n (IfQ tmTest.Q tmThen.Q tmElse.Q))
    (hstate : c.state = Sum.inr (Sum.inl IfPhase.rewindOut))
    (hread : c.output.read = Γ.start)
    (_ : c.output.cells 0 = Γ.start)
    (hnostart : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start)
    (h_ih : c.input.head ≥ 1) (h_ins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (h_wh : ∀ i, (c.work i).head ≥ 1) (h_wns : ∀ i j, j ≥ 1 → (c.work i).cells j ≠ Γ.start) :
    ∃ c', (ifTM tmTest tmThen tmElse).step c = some c' ∧
      c'.state = Sum.inr (Sum.inl IfPhase.check) ∧
      c'.output.head = 1 ∧
      c'.output.cells = c.output.cells ∧
      c'.input = c.input ∧ c'.work = c.work := by
  have hne : c.state ≠ (ifTM tmTest tmThen tmElse).qhalt := by rw [hstate]; nofun
  have hhead : c.output.head = 0 := by
    by_contra hne
    exact hnostart c.output.head (by omega) (by simp only [Tape.read] at hread; exact hread)
  simp only [TM.step, ↓reduceIte, hstate, ifTM, hread]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [Tape.writeAndMove, Tape.move, Tape.write, hhead]
  · simp [Tape.writeAndMove, tape_move_cells, Tape.write, hhead]
  · exact tape_move_idleDir_stable _ h_ih h_ins
  · ext i; exact tape_writeAndMove_stable _ (h_wh i) (h_wns i)

/-- Extended rewind loop: also tracks that input and work tapes are preserved
    when they satisfy the stability condition (head ≥ 1, cells ≥ 1 ≠ start). -/
theorem ifTM_rewind_loop_full (tmTest tmThen tmElse : TM n) :
    ∀ (p : ℕ) (c : Cfg n (IfQ tmTest.Q tmThen.Q tmElse.Q)),
    c.state = Sum.inr (Sum.inl IfPhase.rewindOut) →
    c.output.cells 0 = Γ.start →
    (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) →
    c.output.head = p →
    c.input.head ≥ 1 → (∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) →
    (∀ i, (c.work i).head ≥ 1) →
    (∀ i j, j ≥ 1 → (c.work i).cells j ≠ Γ.start) →
    ∃ c_check,
      (ifTM tmTest tmThen tmElse).reachesIn (p + 1) c c_check ∧
      c_check.state = Sum.inr (Sum.inl IfPhase.check) ∧
      c_check.output.head = 1 ∧
      c_check.output.cells = c.output.cells ∧
      c_check.input = c.input ∧
      c_check.work = c.work :=
  generic_rewind_loop_full (ifTM tmTest tmThen tmElse)
    (fun c hst hread hc0 hns h_ih h_ins h_wh h_wns =>
      if_rewind_step_left_full tmTest tmThen tmElse c hst hread hc0 hns h_ih h_ins h_wh h_wns)
    (fun c hst hread hc0 hns h_ih h_ins h_wh h_wns =>
      if_rewind_step_base_full tmTest tmThen tmElse c hst hread hc0 hns h_ih h_ins h_wh h_wns)

-- ════════════════════════════════════════════════════════════════════════
-- Check step: read output at cell 1, branch to then or else
-- ════════════════════════════════════════════════════════════════════════

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
  show (c.output.writeAndMove (readBackWrite Γ.one).toΓ (idleDir Γ.one)).cells = c.output.cells
  simp only [readBackWrite, Γw.toΓ, idleDir, Tape.writeAndMove, tape_move_cells]
  simp only [Tape.write]; split
  · omega
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

-- ════════════════════════════════════════════════════════════════════════
-- Check step (full tape tracking)
-- ════════════════════════════════════════════════════════════════════════

/-- Check step to then-branch, tracking all tapes. -/
theorem ifTM_check_step_then_full (tmTest tmThen tmElse : TM n)
    (c : Cfg n (IfQ tmTest.Q tmThen.Q tmElse.Q))
    (hstate : c.state = Sum.inr (Sum.inl IfPhase.check))
    (hhead : c.output.head = 1)
    (hcell1 : c.output.cells 1 = Γ.one)
    (h_ih : c.input.head ≥ 1) (h_ins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (h_wh : ∀ i, (c.work i).head ≥ 1)
    (h_wns : ∀ i j, j ≥ 1 → (c.work i).cells j ≠ Γ.start) :
    ∃ c', (ifTM tmTest tmThen tmElse).step c = some c' ∧
      c'.state = Sum.inr (Sum.inr (Sum.inl tmThen.qstart)) ∧
      c'.output.cells = c.output.cells ∧
      c'.output.head = 1 ∧
      c'.input = c.input ∧ c'.work = c.work := by
  have hne : c.state ≠ (ifTM tmTest tmThen tmElse).qhalt := by rw [hstate]; nofun
  have hread : c.output.read = Γ.one := by simp [Tape.read, hhead, hcell1]
  simp only [TM.step, ↓reduceIte, hstate, ifTM, hread]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · show (c.output.writeAndMove (readBackWrite Γ.one).toΓ (idleDir Γ.one)).cells = c.output.cells
    simp only [readBackWrite, Γw.toΓ, idleDir, Tape.writeAndMove, tape_move_cells]
    simp only [Tape.write]; split
    · omega
    · dsimp only []; rw [hhead, ← hcell1]; exact Function.update_eq_self _ _
  · simp only [readBackWrite, Γw.toΓ, idleDir, Tape.writeAndMove, Tape.move, Tape.write]
    split <;> simp_all
  · exact tape_move_idleDir_stable _ h_ih h_ins
  · ext i; exact tape_writeAndMove_stable _ (h_wh i) (h_wns i)

/-- Check step to else-branch, tracking all tapes. -/
theorem ifTM_check_step_else_full (tmTest tmThen tmElse : TM n)
    (c : Cfg n (IfQ tmTest.Q tmThen.Q tmElse.Q))
    (hstate : c.state = Sum.inr (Sum.inl IfPhase.check))
    (hhead : c.output.head = 1)
    (hcell1 : c.output.cells 1 ≠ Γ.one)
    (hnostart_out : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start)
    (h_ih : c.input.head ≥ 1) (h_ins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (h_wh : ∀ i, (c.work i).head ≥ 1)
    (h_wns : ∀ i j, j ≥ 1 → (c.work i).cells j ≠ Γ.start) :
    ∃ c', (ifTM tmTest tmThen tmElse).step c = some c' ∧
      c'.state = Sum.inr (Sum.inr (Sum.inr tmElse.qstart)) ∧
      c'.output.cells = c.output.cells ∧
      c'.output.head = 1 ∧
      c'.input = c.input ∧ c'.work = c.work := by
  have hne : c.state ≠ (ifTM tmTest tmThen tmElse).qhalt := by rw [hstate]; nofun
  have hread_ne_one : c.output.read ≠ Γ.one := by simp [Tape.read, hhead]; exact hcell1
  have hread_ne_start : c.output.read ≠ Γ.start := by
    simp only [Tape.read, hhead]; exact hnostart_out 1 (by omega)
  simp only [TM.step, ↓reduceIte, hstate, ifTM, hread_ne_one]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · apply tape_readBackWrite_preserves; right; exact hread_ne_start
  · have hstable := tape_writeAndMove_stable c.output (by omega) hnostart_out
    show (c.output.writeAndMove (readBackWrite c.output.read).toΓ
      (idleDir c.output.read)).head = 1
    rw [hstable, hhead]
  · exact tape_move_idleDir_stable _ h_ih h_ins
  · ext i; exact tape_writeAndMove_stable _ (h_wh i) (h_wns i)

end TM
