import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic

/-!
# retargetInput simulation — proof internals

This file contains the simulation lemmas for `retargetInput M`, showing
that `retargetInput M` on a configuration where work tape `k` holds the
"virtual input" `z` faithfully simulates `M` on input `z`.

## Key definitions and lemmas

- `retargetWrap` — embed a config of `M : TM k` into a config of
  `retargetInput M : TM (k+1)`, given a choice of real-input tape.
- `retargetInput_step_commute` — one step of `M` corresponds to one step
  of `retargetInput M` under the wrap (assuming a structural invariant on
  `c.input`: cells ≥ 1 are never `Γ.start`).
- `retargetInput_reachesIn_simulate` — multi-step simulation lifting.
- `retargetInput_decidesVirtual` — user-facing: if `M` decides `L` in
  time `T`, then `retargetInput M` started with `z` on work tape `k`
  reaches a halting configuration within `T(|z|)` steps with the correct
  output.

## The structural invariant

Because `retargetInput M` writes back the read symbol on work tape `k`
(to preserve cells), the simulation only goes through cleanly when the
current write is a no-op. This requires:

  head = 0  OR  read ≠ Γ.start

The second disjunct is equivalent to "cells at positions ≥ 1 never
contain `Γ.start`". This is a *structural* invariant of any DTM run
(since `δ` writes only `Γw`, which excludes `Γ.start`, and writes at
cell 0 are no-ops) — captured by `TapeInvariant` below and preserved
across `TM.step` by `TapeInvariant.step`.
-/

variable {k : ℕ}

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Structural tape invariant (cells 0 = ▷, cells ≥ 1 ≠ ▷)
-- ════════════════════════════════════════════════════════════════════════

/-- Structural invariant on tapes: cell 0 holds `Γ.start` and no other
    cell does. Preserved by any sequence of `Tape.writeAndMove` with
    writes in `Γw` and initial `initTape`. -/
def TapeInvariant (t : Tape) : Prop :=
  t.cells 0 = Γ.start ∧ ∀ j, j ≥ 1 → t.cells j ≠ Γ.start

theorem TapeInvariant.initTape (xs : List Γ) (hxs : ∀ a ∈ xs, a ≠ Γ.start) :
    TapeInvariant (_root_.initTape xs) := by
  refine ⟨rfl, ?_⟩
  intro j hj
  simp only [_root_.initTape, show j ≠ 0 by omega, ↓reduceIte]
  cases h : xs[j - 1]? with
  | none => simp
  | some a =>
    simp only [Option.getD_some]
    exact hxs a (List.mem_of_getElem? h)

theorem TapeInvariant.initTape_ofBool (xs : List Bool) :
    TapeInvariant (_root_.initTape (xs.map Γ.ofBool)) := by
  refine TapeInvariant.initTape _ ?_
  intro a ha
  rw [List.mem_map] at ha
  obtain ⟨b, _, rfl⟩ := ha
  cases b <;> simp [Γ.ofBool]

theorem TapeInvariant.initTape_nil : TapeInvariant (_root_.initTape []) := by
  refine ⟨rfl, ?_⟩
  intro j hj
  simp only [_root_.initTape, show j ≠ 0 by omega, ↓reduceIte]
  simp

/-- The current read symbol is not `Γ.start` when head ≥ 1. -/
theorem TapeInvariant.read_ne_start {t : Tape} (hinv : TapeInvariant t)
    (hhead : t.head ≥ 1) : t.read ≠ Γ.start := by
  simp only [Tape.read]; exact hinv.2 t.head hhead

/-- Writing a `Γw` symbol and moving preserves the invariant. -/
theorem TapeInvariant.writeAndMove {t : Tape} (s : Γw) (d : Dir3)
    (hinv : TapeInvariant t) : TapeInvariant (t.writeAndMove s.toΓ d) := by
  constructor
  · -- cell 0 still = Γ.start
    have hcells : (t.writeAndMove s.toΓ d).cells 0 = t.cells 0 := by
      simp only [Tape.writeAndMove, tape_move_cells, Tape.write]
      by_cases hh : t.head = 0
      · simp [hh]
      · simp only [hh, ↓reduceIte]
        rw [Function.update_of_ne (fun h => hh h.symm)]
    rw [hcells]; exact hinv.1
  · -- cells ≥ 1 still ≠ Γ.start
    intro j hj
    simp only [Tape.writeAndMove, tape_move_cells, Tape.write]
    by_cases hh : t.head = 0
    · simp only [hh, ↓reduceIte]; exact hinv.2 j hj
    · simp only [hh, ↓reduceIte]
      by_cases hji : j = t.head
      · rw [hji, Function.update_self]
        cases s <;> simp [Γw.toΓ]
      · rw [Function.update_of_ne hji]
        exact hinv.2 j hj

/-- `TapeInvariant` is preserved across one DTM step (for every tape). -/
theorem TapeInvariant.step_preserves {n : ℕ} (tm : TM n)
    {c c' : Cfg n tm.Q} (hstep : tm.step c = some c')
    (hinp : TapeInvariant c.input) (hwork : ∀ i, TapeInvariant (c.work i))
    (hout : TapeInvariant c.output) :
    TapeInvariant c'.input ∧ (∀ i, TapeInvariant (c'.work i)) ∧
    TapeInvariant c'.output := by
  simp only [step] at hstep
  split at hstep
  · simp at hstep
  · simp only [Option.some.injEq] at hstep
    subst hstep
    refine ⟨?_, ?_, ?_⟩
    · -- input: only moved, cells unchanged
      constructor
      · show (c.input.move _).cells 0 = _
        rw [tape_move_cells]; exact hinp.1
      · intro j hj
        show (c.input.move _).cells j ≠ _
        rw [tape_move_cells]; exact hinp.2 j hj
    · intro i
      exact TapeInvariant.writeAndMove _ _ (hwork i)
    · exact TapeInvariant.writeAndMove _ _ hout

-- ════════════════════════════════════════════════════════════════════════
-- Config wrapping
-- ════════════════════════════════════════════════════════════════════════

/-- Embed a `Cfg k M.Q` into `Cfg (k+1) (retargetInput M).Q` by:
    - putting `realInput` on the real input tape (ignored by the machine),
    - putting `c.work i` on work tape `i` for `i < k`,
    - putting `c.input` on work tape `k` (the virtual input).
    State and output are shared. -/
def retargetWrap (M : TM k) (realInput : Tape) (c : Cfg k M.Q) :
    Cfg (k + 1) (retargetInput M).Q where
  state := c.state
  input := realInput
  work := fun i =>
    if h : i.val < k then c.work ⟨i.val, h⟩
    else c.input
  output := c.output

@[simp] theorem retargetWrap_state (M : TM k) (realInput : Tape) (c : Cfg k M.Q) :
    (retargetWrap M realInput c).state = c.state := rfl

@[simp] theorem retargetWrap_output (M : TM k) (realInput : Tape) (c : Cfg k M.Q) :
    (retargetWrap M realInput c).output = c.output := rfl

@[simp] theorem retargetWrap_input (M : TM k) (realInput : Tape) (c : Cfg k M.Q) :
    (retargetWrap M realInput c).input = realInput := rfl

theorem retargetWrap_work_lt (M : TM k) (realInput : Tape) (c : Cfg k M.Q)
    (i : Fin (k + 1)) (h : i.val < k) :
    (retargetWrap M realInput c).work i = c.work ⟨i.val, h⟩ := by
  simp [retargetWrap, h]

theorem retargetWrap_work_last (M : TM k) (realInput : Tape) (c : Cfg k M.Q) :
    (retargetWrap M realInput c).work ⟨k, by omega⟩ = c.input := by
  simp [retargetWrap]

-- ════════════════════════════════════════════════════════════════════════
-- Core step commute
-- ════════════════════════════════════════════════════════════════════════

/-- Auxiliary: `writeAndMove` with `readBackWrite` of the current read
    symbol equals `move` when the tape has either head = 0 or read ≠ start. -/
private theorem tape_writeBack_eq_move (t : Tape) (d : Dir3)
    (h : t.head = 0 ∨ t.read ≠ Γ.start) :
    t.writeAndMove (readBackWrite t.read).toΓ d = t.move d := by
  show (t.write (readBackWrite t.read).toΓ).move d = t.move d
  have hwrite : t.write (readBackWrite t.read).toΓ = t := by
    simp only [Tape.write]
    rcases h with hh | hne
    · simp [hh]
    · split
      · rfl
      · rw [readBackWrite_toΓ_eq hne]
        simp [Tape.read, Function.update_eq_self]
  rw [hwrite]

/-- One step of `M` corresponds to one step of `retargetInput M` through
    `retargetWrap`. The real-input tape drifts by `move (idleDir · )`.
    Requires the structural invariant on `c.input` (cells ≥ 1 ≠ start). -/
theorem retargetInput_step_commute (M : TM k) {c c' : Cfg k M.Q}
    (hstep : M.step c = some c') (realInput : Tape)
    (hinp : TapeInvariant c.input) :
    (retargetInput M).step (retargetWrap M realInput c) =
    some (retargetWrap M (realInput.move (idleDir realInput.read)) c') := by
  have hne : c.state ≠ M.qhalt := ne_qhalt_of_step hstep
  -- Extract c' from M.step c.
  simp only [step, hne, ↓reduceIte, Option.some.injEq] at hstep
  subst hstep
  -- Key fact 1: wHeads ⟨k, _⟩ = c.input.read.
  have hwHead_last : ((retargetWrap M realInput c).work ⟨k, by omega⟩).read
      = c.input.read := by
    show (if h : k < k then c.work ⟨k, h⟩ else c.input).read = c.input.read
    simp
  -- Key fact 2: fun i : Fin k => wHeads ⟨i.val, _⟩ equals fun i => (c.work i).read.
  have hinner : (fun i : Fin k =>
      ((retargetWrap M realInput c).work ⟨i.val, by omega⟩).read)
        = (fun i => (c.work i).read) := by
    funext i
    show (if h : i.val < k then c.work ⟨i.val, h⟩ else c.input).read = (c.work i).read
    rw [dif_pos i.isLt]
  -- Unfold step on the LHS.
  simp only [step, show (retargetWrap M realInput c).state = c.state from rfl,
             show (retargetInput M).qhalt = M.qhalt from rfl,
             hne, ↓reduceIte, retargetWrap_input, retargetWrap_output,
             Option.some.injEq]
  -- Unfold retargetInput's δ.
  dsimp only [retargetInput]
  rw [hwHead_last, hinner]
  -- Now show the Cfg equality field-by-field.
  refine Cfg.mk.injEq _ _ _ _ _ _ _ _ |>.mpr ⟨rfl, rfl, ?_, rfl⟩
  funext i
  by_cases hik : i.val < k
  · -- i.val < k: matches M's work tape i.
    -- LHS: ((retargetWrap...).work i).writeAndMove (M.workWrites ⟨i.val, _⟩).toΓ (M.workDirs ⟨i.val, _⟩)
    -- RHS: (retargetWrap... c').work i where c'.work ⟨i.val, _⟩ is the updated tape.
    rw [retargetWrap_work_lt _ _ _ _ hik]
    show (_ : Tape).writeAndMove _ _ = (if h : i.val < k then _ else _)
    rw [dif_pos hik, dif_pos hik, dif_pos hik]
  · -- i.val = k: virtual input case.
    have hik_eq : i.val = k := by have := i.isLt; omega
    have hwork_k : (retargetWrap M realInput c).work i = c.input := by
      show (if h : i.val < k then c.work ⟨i.val, h⟩ else c.input) = c.input
      rw [dif_neg hik]
    have hcond : c.input.head = 0 ∨ c.input.read ≠ Γ.start := by
      by_cases hh : c.input.head = 0
      · left; exact hh
      · right
        show c.input.cells c.input.head ≠ Γ.start
        exact hinp.2 c.input.head (by omega)
    -- Rewrite LHS via hwork_k, then use tape_writeBack_eq_move.
    rw [hwork_k]
    show _ = (if h : i.val < k then _ else _)
    rw [dif_neg hik, dif_neg hik, dif_neg hik]
    exact tape_writeBack_eq_move c.input _ hcond

-- ════════════════════════════════════════════════════════════════════════
-- Multi-step simulation
-- ════════════════════════════════════════════════════════════════════════

/-- Multi-step version: if `M` reaches `c'` in `t` steps, then
    `retargetInput M` reaches *some* config (differing from `retargetWrap`
    only in the real-input tape drift) in the same `t` steps. -/
theorem retargetInput_reachesIn_simulate (M : TM k)
    {c c' : Cfg k M.Q} {t : ℕ} (hreach : M.reachesIn t c c')
    (hinp : TapeInvariant c.input) (hwork : ∀ i, TapeInvariant (c.work i))
    (hout : TapeInvariant c.output) (realInput : Tape) :
    ∃ finalReal : Tape,
      (retargetInput M).reachesIn t
        (retargetWrap M realInput c)
        (retargetWrap M finalReal c') := by
  induction hreach generalizing realInput with
  | zero => exact ⟨realInput, .zero⟩
  | @step c₀ c_mid _ _ hstep hrest ih =>
    obtain ⟨hinp', hwork', hout'⟩ :=
      TapeInvariant.step_preserves M hstep hinp hwork hout
    have hcommute := retargetInput_step_commute M hstep realInput hinp
    obtain ⟨finalReal', hreach'⟩ := ih hinp' hwork' hout'
      (realInput.move (idleDir realInput.read))
    exact ⟨finalReal', .step hcommute hreach'⟩

-- ════════════════════════════════════════════════════════════════════════
-- User-facing: retargetInput M decides on a virtual input
-- ════════════════════════════════════════════════════════════════════════

/-- Initial configuration for `retargetInput M` with virtual input `z` on
    work tape `k` and an arbitrary `realInput` on the (ignored) real
    input tape. Work tapes `0..k-1` are empty; output is empty. -/
def retargetInitCfg (M : TM k) (z : List Bool) (realInput : Tape) :
    Cfg (k + 1) (retargetInput M).Q where
  state := M.qstart
  input := realInput
  work := fun i =>
    if i.val < k then _root_.initTape []
    else _root_.initTape (z.map Γ.ofBool)
  output := _root_.initTape []

theorem retargetInitCfg_eq_wrap (M : TM k) (z : List Bool) (realInput : Tape) :
    retargetInitCfg M z realInput = retargetWrap M realInput (M.initCfg z) := by
  simp only [retargetInitCfg, retargetWrap]
  refine Cfg.mk.injEq _ _ _ _ _ _ _ _ |>.mpr ⟨rfl, rfl, ?_, rfl⟩
  funext i
  by_cases hik : i.val < k
  · simp only [hik, ↓reduceIte, ↓reduceDIte]
  · simp only [hik, ↓reduceIte, ↓reduceDIte]

/-- **User-facing simulation**: if `M` decides `L` in time `T`, then
    `retargetInput M` started with `z` on work tape `k` reaches a halted
    configuration within `T(|z|)` steps whose output cell 1 indicates
    membership of `z` in `L`. -/
theorem retargetInput_decidesVirtual (M : TM k) {L : Language} {T : ℕ → ℕ}
    (hM : M.DecidesInTime L T) (z : List Bool) (realInput : Tape) :
    ∃ c' t, t ≤ T z.length ∧
      (retargetInput M).reachesIn t (retargetInitCfg M z realInput) c' ∧
      (retargetInput M).halted c' ∧
      (z ∈ L → c'.output.cells 1 = Γ.one) ∧
      (z ∉ L → c'.output.cells 1 = Γ.zero) := by
  obtain ⟨c_M, t, ht, hreach, hhalt, hyes, hno⟩ := hM z
  have hinp : TapeInvariant (M.initCfg z).input := by
    exact TapeInvariant.initTape_ofBool z
  have hwork : ∀ i, TapeInvariant ((M.initCfg z).work i) := fun i => by
    exact TapeInvariant.initTape_nil
  have hout : TapeInvariant (M.initCfg z).output := by
    exact TapeInvariant.initTape_nil
  obtain ⟨finalReal, hreachSim⟩ :=
    retargetInput_reachesIn_simulate M hreach hinp hwork hout realInput
  refine ⟨retargetWrap M finalReal c_M, t, ht, ?_, ?_, ?_, ?_⟩
  · rw [retargetInitCfg_eq_wrap]; exact hreachSim
  · show (retargetWrap M finalReal c_M).state = (retargetInput M).qhalt
    show c_M.state = M.qhalt
    exact hhalt
  · intro hz
    show (retargetWrap M finalReal c_M).output.cells 1 = Γ.one
    exact hyes hz
  · intro hz
    show (retargetWrap M finalReal c_M).output.cells 1 = Γ.zero
    exact hno hz

end TM
