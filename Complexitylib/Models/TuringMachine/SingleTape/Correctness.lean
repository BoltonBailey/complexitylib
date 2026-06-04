import Complexitylib.Models.TuringMachine.SingleTape.Delta
import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic

/-!
# Single-tape simulation — correctness internals

The config-level correspondence `Corr` between a `singleTapeSim N` configuration
and an `N` configuration at a macro-step boundary, and the **macro-step
correspondence** `macroStepCorr` (one `N`-step ↦ several simulator steps,
preserving `Corr`). The behavioural lemmas (`SingleTape.lean`) follow by
iterating `macroStepCorr` over `N`'s computation and translating acceptance.

See `docs/A4-SingleTapeSimulation.md`. Proof internals only.
-/

namespace NTM

variable {n : ℕ}

/-- Split a trace into a first `a` steps and a remaining `b` steps, with the
    choice sequence drawn from a single `ℕ`-indexed function `f` (avoiding the
    dependent-`Fin` reindexing pain). Generalizes `trace_succ_eq_trace_one`. -/
theorem trace_add (tm : NTM n) (a b : ℕ) (f : ℕ → Bool) (c : Cfg n tm.Q) :
    tm.trace (a + b) (fun i => f i.val) c =
      tm.trace b (fun i => f (a + i.val)) (tm.trace a (fun i => f i.val) c) := by
  induction a generalizing f c with
  | zero => rw [Nat.zero_add]; simp [NTM.trace]
  | succ a ih =>
    rw [show a + 1 + b = a + b + 1 from by omega]
    by_cases hhalt : c.state = tm.qhalt
    · simp only [NTM.trace, hhalt, if_true]
      exact (tm.trace_halted b _ hhalt).symm
    · simp only [NTM.trace, hhalt, if_false]
      rw [ih (fun j => f (j + 1))]
      congr 1
      funext i
      congr 1
      omega

end NTM

namespace NTM.SingleTape

/-- **Config correspondence.** At a macro-step boundary, the `singleTapeSim N`
    configuration `c1` corresponds to the `N` configuration `c`: same simulated
    state, work head parked at cell 0/1, identical input and output tapes, and
    the single work tape encodes `N`'s `k` work tapes (materialized up to `M`). -/
structure Corr {k : ℕ} (N : NTM k) (M : ℕ)
    (c1 : Cfg 1 (SimQ k N.Q)) (c : Cfg k N.Q) : Prop where
  /-- `c1` is at the `run` phase for `N`'s current state. -/
  state : c1.state = SimQ.run c.state
  /-- The single work head is parked at cell 0 (initial) or cell 1 (post-commit). -/
  headLe : (c1.work 0).head ≤ 1
  /-- Input tapes coincide (input is read-only, carried over verbatim). -/
  inputEq : c1.input = c.input
  /-- Output tapes coincide (the simulator writes output exactly as `N` does). -/
  outputEq : c1.output = c.output
  /-- The single work tape encodes `N`'s `k` work tapes. -/
  inv : SimInvAt k (c1.work 0) c.work M

/-- **Base case.** The initial `singleTapeSim N` configuration corresponds to
    `N`'s initial configuration, materialized to `M = 0` (empty used region). -/
theorem corr_init {k : ℕ} (N : NTM k) (x : List Bool) :
    Corr N 0 ((singleTapeSim N).initCfg x) (N.initCfg x) where
  state := rfl
  headLe := Nat.zero_le 1
  inputEq := rfl
  outputEq := rfl
  inv := simInvAt_init k

/-- Writing back the read symbol preserves whether a cell holds the accept bit
    `1` (`readBackWrite` fixes `0/1/□` and maps `▷ ↦ □`, never producing a
    spurious `1`). -/
theorem readBackWrite_one_iff (g : Γ) :
    ((TM.readBackWrite g : Γw) : Γ) = Γ.one ↔ g = Γ.one := by
  cases g <;> decide

/-- The halt step's output action — `writeAndMove` writing back the read
    symbol — preserves the accept bit at cell 1. -/
theorem accept_bit_preserved (t : Tape) (d : Dir3) :
    (t.writeAndMove ((TM.readBackWrite t.read : Γw) : Γ) d).cells 1 = Γ.one
      ↔ t.cells 1 = Γ.one := by
  have hcells : (t.writeAndMove ((TM.readBackWrite t.read : Γw) : Γ) d).cells
              = (t.write ((TM.readBackWrite t.read : Γw) : Γ)).cells := by
    cases d <;> rfl
  rw [hcells, Tape.write]
  by_cases hh0 : t.head = 0
  · simp [hh0]
  · rw [if_neg hh0]
    simp only [Function.update_apply]
    by_cases h1 : (1 : ℕ) = t.head
    · rw [if_pos h1, Tape.read, ← h1, readBackWrite_one_iff]
    · rw [if_neg h1]

/-- **Halt correspondence.** When `N` has halted, the simulator (parked at
    `run N.qhalt`) takes one step to `SimQ.halt`, preserving the accept bit. -/
theorem haltCorr {k : ℕ} (N : NTM k) {M : ℕ}
    {c1 : Cfg 1 (SimQ k N.Q)} {c : Cfg k N.Q}
    (hcorr : Corr N M c1 c) (hh : c.state = N.qhalt) :
    (singleTapeSim N).halted ((singleTapeSim N).trace 1 (fun _ => false) c1) ∧
    (((singleTapeSim N).trace 1 (fun _ => false) c1).output.cells 1 = Γ.one
      ↔ c.output.cells 1 = Γ.one) := by
  have hst : c1.state = SimQ.run N.qhalt := by rw [hcorr.state, hh]
  refine ⟨?_, ?_⟩
  · show ((singleTapeSim N).trace 1 (fun _ => false) c1).state = (singleTapeSim N).qhalt
    simp only [NTM.trace, singleTapeSim, simDelta, hst, SimQ.run, SimQ.halt, reduceCtorEq,
      ↓reduceIte]
  · have hout : ((singleTapeSim N).trace 1 (fun _ => false) c1).output
        = c1.output.writeAndMove ((TM.readBackWrite c1.output.read : Γw) : Γ)
            (TM.idleDir c1.output.read) := by
      simp only [NTM.trace, singleTapeSim, simDelta, hst, SimQ.run, SimQ.halt, reduceCtorEq,
        ↓reduceIte]
    rw [hout, accept_bit_preserved, hcorr.outputEq]

/-- Per-macro-step sim-step budget at materialization level `M`: a generous bound
    covering the four sweeps over an `≈ 3k·M`-cell region plus the `run`/`commit`
    steps. The `16·(k+1)` constant matches `singleTapeSimTime`. -/
def macroBound (k M : ℕ) : ℕ := 16 * (k + 1) * (M + 1)

theorem macroBound_mono {k M M' : ℕ} (h : M ≤ M') : macroBound k M ≤ macroBound k M' := by
  unfold macroBound
  exact Nat.mul_le_mul_left _ (by omega)

/-! ### Per-phase config transitions (building blocks for `macroStepCorr`)

Each lemma reduces `trace`-of-a-phase to the explicit next configuration; the
full macro-step composes them via `trace_add`. -/

/-- The **run** step (1 sim step): from a `run q` config with `q ≠ N.qhalt`, the
    simulator initialises GATHER (`acc = ▷`, reads `iSym`/`oSym`, sweep at the
    start) and repositions the work head to cell 1. Input/output are advanced by
    `idleDir` (the `▷`-dodge); the work tape's cells are preserved
    (`readBackWrite`). -/
theorem run_step {k : ℕ} (N : NTM k) (q : N.Q) (hq : q ≠ N.qhalt) (b : Bool)
    (c1 : Cfg 1 (SimQ k N.Q)) (hst : c1.state = SimQ.run q) :
    (singleTapeSim N).trace 1 (fun _ => b) c1 =
      { state := SimQ.gather (q, (fun _ => Γ.start), c1.input.read, c1.output.read,
          (0, 0), false, Γ.blank),
        input := c1.input.move (TM.idleDir c1.input.read),
        work := fun i => (c1.work i).writeAndMove
          ((TM.readBackWrite ((c1.work 0).read) : Γw) : Γ) (TM.idleDir ((c1.work 0).read)),
        output := c1.output.writeAndMove
          ((TM.readBackWrite c1.output.read : Γw) : Γ) (TM.idleDir c1.output.read) } := by
  rw [NTM.trace]
  simp only [hst, singleTapeSim, simDelta, runStep, SimQ.run, SimQ.halt, SimQ.gather,
    hq, reduceCtorEq, ↓reduceIte, NTM.trace]

/-- The **commit** step (1 sim step): from a `commit (q', oW, oD, iD, iSym, oSym)`
    config, the simulator applies the deferred output write/move and input move
    (accounting for the `▷`-dodge via the `iSym`/`oSym` guards) and returns to
    `run q'`. The work tape is preserved. -/
theorem commit_step {k : ℕ} (N : NTM k) (q' : N.Q) (oW : Γw) (oD iD : Dir3)
    (iSym oSym : Γ) (b : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.commit (q', oW, oD, iD, iSym, oSym)) :
    (singleTapeSim N).trace 1 (fun _ => b) c1 =
      { state := SimQ.run q',
        input := c1.input.move
          (if iSym = Γ.start then TM.idleDir c1.input.read else safeDir c1.input.read iD),
        work := fun i => (c1.work i).writeAndMove
          ((TM.readBackWrite ((c1.work 0).read) : Γw) : Γ) (TM.idleDir ((c1.work 0).read)),
        output := c1.output.writeAndMove
          ((if oSym = Γ.start then TM.readBackWrite c1.output.read else oW : Γw) : Γ)
          (if oSym = Γ.start then TM.idleDir c1.output.read else safeDir c1.output.read oD) } := by
  rw [NTM.trace]
  simp only [hst, singleTapeSim, simDelta, commitStep, SimQ.commit, SimQ.run, SimQ.halt,
    Sum.inr.injEq, reduceCtorEq, ↓reduceIte, NTM.trace]

/-- One **gather** step (`trace 1`): from a `gather d` config, the result is the
    configuration built from `gatherStep`'s output (the trace step applied to the
    `gather` branch of `simDelta`). The basis of the gather-sweep induction. -/
theorem gather_trace1 {k : ℕ} (N : NTM k) (d : GatherData k N.Q) (b : Bool)
    (c1 : Cfg 1 (SimQ k N.Q)) (hst : c1.state = SimQ.gather d) :
    (singleTapeSim N).trace 1 (fun _ => b) c1 =
      (let r := gatherStep N b d c1.input.read ((c1.work 0).read) c1.output.read
       { state := r.1, input := c1.input.move r.2.2.2.1,
         work := fun i => (c1.work i).writeAndMove (r.2.1 i) (r.2.2.2.2.1 i),
         output := c1.output.writeAndMove r.2.2.1 r.2.2.2.2.2 } : Cfg 1 (SimQ k N.Q)) := by
  rw [NTM.trace]
  simp only [hst, singleTapeSim, simDelta, SimQ.gather, SimQ.halt, Sum.inr.injEq,
    reduceCtorEq, ↓reduceIte, NTM.trace]

/-- A GATHER work step (`readBackWrite`, move right) on a tape reading a non-`▷`
    cell just advances the head by one, leaving contents intact. -/
private theorem work_gather_step (t : Tape) (h : t.read ≠ Γ.start) :
    t.writeAndMove (TM.readBackWrite t.read).toΓ Dir3.right = { t with head := t.head + 1 } := by
  rw [TM.readBackWrite_toΓ_eq h]
  show (t.write t.read).move Dir3.right = { t with head := t.head + 1 }
  unfold Tape.write Tape.read
  split <;> simp [Tape.move, Function.update_eq_self]

/-- Writing a value to a cell (head ≥ 1) and moving right updates that cell and
    advances the head. Used for SCATTER cells that are overwritten. -/
private theorem work_write_right (t : Tape) (s : Γ) (h : 1 ≤ t.head) :
    t.writeAndMove s Dir3.right = ⟨t.head + 1, Function.update t.cells t.head s⟩ := by
  show (t.write s).move Dir3.right = _
  simp only [Tape.write, show ¬(t.head = 0) by omega, ↓reduceIte, Tape.move]

/-- Writing a cell its own current value and moving right just advances the head
    (the write is a no-op). Used for SCATTER cells that aren't overwritten. -/
private theorem work_write_eq (t : Tape) (s : Γ) (h : t.read = s) :
    t.writeAndMove s Dir3.right = { t with head := t.head + 1 } := by
  obtain rfl : s = t.cells t.head := h.symm
  show (t.write (t.cells t.head)).move Dir3.right = { t with head := t.head + 1 }
  unfold Tape.write
  split <;> simp [Tape.move, Function.update_eq_self]

/-- A REWIND work step (`readBackWrite`, move left) on a tape reading a non-`▷`
    cell just retreats the head by one, leaving contents intact. -/
private theorem work_rewind_step (t : Tape) (h : t.read ≠ Γ.start) :
    t.writeAndMove (TM.readBackWrite t.read).toΓ Dir3.left = { t with head := t.head - 1 } := by
  rw [TM.readBackWrite_toΓ_eq h]
  show (t.write t.read).move Dir3.left = { t with head := t.head - 1 }
  unfold Tape.write Tape.read
  split <;> simp [Tape.move, Function.update_eq_self]

/-- A blank-write + move right on a tape at cell `0` lands at cell `1`, contents
    intact (the write at cell `0` is a no-op). The REWIND→SCATTER turn-around. -/
private theorem work_blank_right_at0 (t : Tape) (h : t.head = 0) :
    t.writeAndMove Γw.blank.toΓ Dir3.right = { t with head := 1 } := by
  show (t.write Γw.blank.toΓ).move Dir3.right = { t with head := 1 }
  simp only [Tape.write, h, ↓reduceIte, Tape.move]

/-- An idle (`stay`) move on a tape reading a non-`▷` cell is a no-op. -/
private theorem tape_idle_stay (t : Tape) (h : t.read ≠ Γ.start) :
    t.move (TM.idleDir t.read) = t := by
  simp [TM.idleDir, h, Tape.move]

/-- A `readBackWrite`+idle step on a tape reading a non-`▷` cell is a no-op. -/
private theorem tape_idle_writeMove (t : Tape) (h : t.read ≠ Γ.start) :
    t.writeAndMove (TM.readBackWrite t.read).toΓ (TM.idleDir t.read) = t := by
  rw [TM.readBackWrite_toΓ_eq h]
  simp only [TM.idleDir, h, ↓reduceIte]
  show (t.write t.read).move Dir3.stay = t
  unfold Tape.write Tape.read
  split <;> simp [Tape.move, Function.update_eq_self]

/-- `trace 3` with a constant choice unfolds into three single steps. -/
private theorem trace_three {n : ℕ} (M : NTM n) (bb : Bool) (c : Cfg n M.Q) :
    M.trace 3 (fun _ => bb) c
      = M.trace 1 (fun _ => bb) (M.trace 1 (fun _ => bb) (M.trace 1 (fun _ => bb) c)) := by
  have h1 := M.trace_add 1 2 (fun _ => bb) c
  have h2 := M.trace_add 1 1 (fun _ => bb) (M.trace 1 (fun _ => bb) c)
  simp only [] at h1 h2
  rw [show (3 : ℕ) = 1 + 2 from rfl, h1, show (2 : ℕ) = 1 + 1 from rfl, h2]

/-- GATHER slot-`0` step (head-bit): records whether this tape's head marker is
    present (`rf := wH = one`), advances to slot `1`, leaves contents/heads put. -/
private theorem gather_slot0 {k : ℕ} (N : NTM k) (bb : Bool)
    (q : N.Q) (acc : Fin k → Γ) (iSym oSym : Γ) (pt : Fin (k + 1)) (rf : Bool) (pending : Γ)
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.gather (q, acc, iSym, oSym, (pt, 0), rf, pending))
    (hwb : (c1.work 0).read ≠ Γ.blank) (hws : (c1.work 0).read ≠ Γ.start)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.gather (q, acc, iSym, oSym, (pt, 1),
          decide ((c1.work 0).read = Γ.one), pending),
        input := c1.input, output := c1.output,
        work := fun _ => { c1.work 0 with head := (c1.work 0).head + 1 } } := by
  rw [gather_trace1 N (q, acc, iSym, oSym, (pt, 0), rf, pending) bb c1 hst]
  simp only [gatherStep, advanceSweep, hwb, ↓reduceIte, Fin.reduceEq, Fin.reduceAdd,
    tape_idle_stay c1.input his, tape_idle_writeMove c1.output hos]
  congr 1
  funext x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  exact work_gather_step (c1.work 0) hws

/-- GATHER slot-`1` step (sym-hi): stashes the high code cell into `pending`,
    advances to slot `2`, leaves contents/heads put. -/
private theorem gather_slot1 {k : ℕ} (N : NTM k) (bb : Bool)
    (q : N.Q) (acc : Fin k → Γ) (iSym oSym : Γ) (pt : Fin (k + 1)) (rf : Bool) (pending : Γ)
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.gather (q, acc, iSym, oSym, (pt, 1), rf, pending))
    (hwb : (c1.work 0).read ≠ Γ.blank) (hws : (c1.work 0).read ≠ Γ.start)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.gather (q, acc, iSym, oSym, (pt, 2), rf, (c1.work 0).read),
        input := c1.input, output := c1.output,
        work := fun _ => { c1.work 0 with head := (c1.work 0).head + 1 } } := by
  rw [gather_trace1 N (q, acc, iSym, oSym, (pt, 1), rf, pending) bb c1 hst]
  simp only [gatherStep, advanceSweep, hwb, ↓reduceIte, Fin.reduceEq,
    tape_idle_stay c1.input his, tape_idle_writeMove c1.output hos]
  congr 1
  funext x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  exact work_gather_step (c1.work 0) hws

/-- GATHER slot-`2` step (sym-lo): decodes the symbol and, if this tape's head
    marker was seen (`rf`), records it into `acc`; advances to the next tape's
    slot `0`, leaves contents/heads put. -/
private theorem gather_slot2 {k : ℕ} (N : NTM k) (bb : Bool)
    (q : N.Q) (acc : Fin k → Γ) (iSym oSym : Γ) (pt : Fin (k + 1)) (rf : Bool) (pending : Γ)
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.gather (q, acc, iSym, oSym, (pt, 2), rf, pending))
    (hwb : (c1.work 0).read ≠ Γ.blank) (hws : (c1.work 0).read ≠ Γ.start)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.gather (q,
          (if rf = true then
             (if h : pt.val < k then
                Function.update acc ⟨pt.val, h⟩ (decSymΓ pending (c1.work 0).read) else acc)
           else acc),
          iSym, oSym, (⟨if pt.val + 1 < k then pt.val + 1 else 0, by split <;> omega⟩, 0),
          rf, pending),
        input := c1.input, output := c1.output,
        work := fun _ => { c1.work 0 with head := (c1.work 0).head + 1 } } := by
  rw [gather_trace1 N (q, acc, iSym, oSym, (pt, 2), rf, pending) bb c1 hst]
  simp only [gatherStep, advanceSweep, hwb, ↓reduceIte, Fin.reduceEq,
    tape_idle_stay c1.input his, tape_idle_writeMove c1.output hos]
  congr 1
  funext x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  exact work_gather_step (c1.work 0) hws

/-- Split a constant-choice trace: `trace (a + a') = trace a' ∘ trace a`. -/
private theorem trace_const_add {n : ℕ} (M : NTM n) (a a' : ℕ) (bb : Bool) (c : Cfg n M.Q) :
    M.trace (a + a') (fun _ => bb) c
      = M.trace a' (fun _ => bb) (M.trace a (fun _ => bb) c) := by
  have h := M.trace_add a a' (fun _ => bb) c
  simpa using h

/-- One gather **triple** (`trace 3`): starting at slot `0` of tape `j`'s triple
    in the encoded region (work head at `h`), three GATHER steps read the head-bit
    (`cells h`), sym-hi (`cells (h+1)`), and sym-lo (`cells (h+2)`) cells, advance
    the sweep to the next tape's slot `0`, leave the work tape contents unchanged
    (read-only sweep, head at `h+3`), and — if the head-bit is set — record this
    tape's decoded symbol into `acc`. Input/output stay put (off `▷`, so `idleDir`
    is `stay`). The block/sweep inductions iterate this over the `k` tapes and `M`
    blocks. Code-cell hypotheses (`≠ □`, `≠ ▷`) keep all three steps in the slot
    branch (no sentinel) and make `readBackWrite` cell-preserving. -/
theorem gather_triple {k : ℕ} (N : NTM k) (bb : Bool)
    (q : N.Q) (acc : Fin k → Γ) (iSym oSym : Γ) (rf₀ : Bool) (pending₀ : Γ)
    (j : ℕ) (hj : j < k) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.gather (q, acc, iSym, oSym, (⟨j, by omega⟩, 0), rf₀, pending₀))
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start)
    (hb0 : (c1.work 0).cells ((c1.work 0).head) ≠ Γ.blank)
    (hb1 : (c1.work 0).cells ((c1.work 0).head + 1) ≠ Γ.blank)
    (hb2 : (c1.work 0).cells ((c1.work 0).head + 2) ≠ Γ.blank)
    (hs0 : (c1.work 0).cells ((c1.work 0).head) ≠ Γ.start)
    (hs1 : (c1.work 0).cells ((c1.work 0).head + 1) ≠ Γ.start)
    (hs2 : (c1.work 0).cells ((c1.work 0).head + 2) ≠ Γ.start) :
    (singleTapeSim N).trace 3 (fun _ => bb) c1 =
      { state := SimQ.gather (q,
          (if (c1.work 0).cells ((c1.work 0).head) = Γ.one then
             Function.update acc ⟨j, hj⟩ (decSymΓ ((c1.work 0).cells ((c1.work 0).head + 1))
               ((c1.work 0).cells ((c1.work 0).head + 2)))
           else acc),
          iSym, oSym, (⟨if j + 1 < k then j + 1 else 0, by split <;> omega⟩, 0),
          decide ((c1.work 0).cells ((c1.work 0).head) = Γ.one),
          (c1.work 0).cells ((c1.work 0).head + 1)),
        input := c1.input, output := c1.output,
        work := fun _ => { c1.work 0 with head := (c1.work 0).head + 3 } } := by
  have e0 : (singleTapeSim N).trace 1 (fun _ => bb) c1 = _ :=
    gather_slot0 N bb q acc iSym oSym ⟨j, by omega⟩ rf₀ pending₀ c1 hst hb0 hs0 his hos
  have e1 : (singleTapeSim N).trace 1 (fun _ => bb)
      ((singleTapeSim N).trace 1 (fun _ => bb) c1) = _ :=
    gather_slot1 N bb q acc iSym oSym ⟨j, by omega⟩ (decide ((c1.work 0).read = Γ.one)) pending₀
      ((singleTapeSim N).trace 1 (fun _ => bb) c1)
      (by rw [e0]) (by rw [e0]; exact hb1) (by rw [e0]; exact hs1)
      (by rw [e0]; exact his) (by rw [e0]; exact hos)
  have e2 : (singleTapeSim N).trace 1 (fun _ => bb)
      ((singleTapeSim N).trace 1 (fun _ => bb) ((singleTapeSim N).trace 1 (fun _ => bb) c1)) = _ :=
    gather_slot2 N bb q acc iSym oSym ⟨j, by omega⟩ (decide ((c1.work 0).read = Γ.one))
      (((singleTapeSim N).trace 1 (fun _ => bb) c1).work 0).read
      ((singleTapeSim N).trace 1 (fun _ => bb) ((singleTapeSim N).trace 1 (fun _ => bb) c1))
      (by rw [e1]) (by rw [e1, e0]; exact hb2) (by rw [e1, e0]; exact hs2)
      (by rw [e1, e0]; exact his) (by rw [e1, e0]; exact hos)
  rw [trace_three, e2, e1, e0]
  simp only [Tape.read, decide_eq_true_eq, dif_pos hj]; rfl

/-- **GATHER one block (`trace (3*m)`).** Sweeping the `k`-tape block `b` (`1 ≤ b
    ≤ M`) starting at tape `0`, slot `0` (work head at `blockStart k b`): after
    `m ≤ k` triples the work head is at `blockStart k b + 3*m`, the sweep is at
    tape `(if m < k then m else 0)` slot `0`, and `acc` has recorded the read
    symbol of every tape `j < m` whose head sits in block `b` (others untouched).
    The `rf`/`pending` leftovers from the last triple are existential — the next
    block's slot-`0`/`1` steps overwrite them. Proved by induction on `m`, each
    step one `gather_triple` with the cell facts from `SimInvAt`. -/
theorem gather_block_aux {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (b M : ℕ)
    (hb1 : 1 ≤ b) (hbM : b ≤ M) (q : N.Q) (iSym oSym : Γ) (acc₀ : Fin k → Γ)
    (c1 : Cfg 1 (SimQ k N.Q)) (rf₀ : Bool) (pending₀ : Γ)
    (hst : c1.state = SimQ.gather (q, acc₀, iSym, oSym, (⟨0, by omega⟩, 0), rf₀, pending₀))
    (hhead : (c1.work 0).head = blockStart k b)
    (hinv : SimInvAt k (c1.work 0) c.work M)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start)
    (m : ℕ) (hm : m ≤ k) :
    ∃ (rf' : Bool) (pending' : Γ),
      (singleTapeSim N).trace (3 * m) (fun _ => bb) c1 =
        { state := SimQ.gather (q,
            (fun j => if j.val < m ∧ (c.work j).head = b then (c.work j).read else acc₀ j),
            iSym, oSym, (⟨if m < k then m else 0, by split <;> omega⟩, 0), rf', pending'),
          input := c1.input, output := c1.output,
          work := fun _ => { c1.work 0 with head := blockStart k b + 3 * m } } := by
  induction m with
  | zero =>
    refine ⟨rf₀, pending₀, ?_⟩
    have h0 : (singleTapeSim N).trace (3 * 0) (fun _ => bb) c1 = c1 := by
      simp only [Nat.mul_zero]; rfl
    rw [h0]
    obtain ⟨cst, cin, cwk, cout⟩ := c1
    simp only [Nat.not_lt_zero, false_and, ↓reduceIte, ite_self, Nat.mul_zero,
      Nat.add_zero] at hst hhead ⊢
    subst hst
    refine Cfg.mk.injEq .. |>.mpr ⟨rfl, rfl, ?_, rfl⟩
    funext x
    obtain rfl : x = 0 := Subsingleton.elim x 0
    rw [← hhead]
  | succ m ih =>
    obtain ⟨rfm, pendingm, hmeq⟩ := ih (by omega)
    have hmk : m < k := by omega
    have hbit := hinv.headBit b hb1 hbM ⟨m, hmk⟩
    have hsym := hinv.sym b hb1 hbM ⟨m, hmk⟩
    have hc0 : (c1.work 0).cells (blockStart k b + 3 * m)
        = if (c.work ⟨m, hmk⟩).head = b then Γ.one else Γ.zero := by
      rw [show blockStart k b + 3 * m = headBitCell k b ⟨m, hmk⟩ from by simp [headBitCell]]
      exact hbit
    have hc1 : (c1.work 0).cells (blockStart k b + 3 * m + 1)
        = (encSymΓ ((c.work ⟨m, hmk⟩).cells b)).1 := by
      rw [show blockStart k b + 3 * m + 1 = symCell k b ⟨m, hmk⟩ from by simp [symCell]]
      exact hsym.1
    have hc2 : (c1.work 0).cells (blockStart k b + 3 * m + 2)
        = (encSymΓ ((c.work ⟨m, hmk⟩).cells b)).2 := by
      rw [show blockStart k b + 3 * m + 2 = symCell k b ⟨m, hmk⟩ + 1 from by simp [symCell]]
      exact hsym.2
    refine ⟨decide ((c1.work 0).cells (blockStart k b + 3 * m) = Γ.one),
            (c1.work 0).cells (blockStart k b + 3 * m + 1), ?_⟩
    rw [show 3 * (m + 1) = 3 * m + 3 from by omega, trace_const_add,
        gather_triple N bb q
          (fun j => if ↑j < m ∧ (c.work j).head = b then (c.work j).read else acc₀ j)
          iSym oSym rfm pendingm m hmk
          ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1)
          (by rw [hmeq]; simp only [if_pos hmk])
          (by rw [hmeq]; exact his)
          (by rw [hmeq]; exact hos)
          (by rw [hmeq]; show (c1.work 0).cells (blockStart k b + 3 * m) ≠ Γ.blank; rw [hc0]; split <;> decide)
          (by rw [hmeq]; show (c1.work 0).cells (blockStart k b + 3 * m + 1) ≠ Γ.blank; rw [hc1]; exact (encSymΓ_ne_blank _).1)
          (by rw [hmeq]; show (c1.work 0).cells (blockStart k b + 3 * m + 2) ≠ Γ.blank; rw [hc2]; exact (encSymΓ_ne_blank _).2)
          (by rw [hmeq]; show (c1.work 0).cells (blockStart k b + 3 * m) ≠ Γ.start; rw [hc0]; split <;> decide)
          (by rw [hmeq]; show (c1.work 0).cells (blockStart k b + 3 * m + 1) ≠ Γ.start; rw [hc1]; exact (encSymΓ_ne_start _).1)
          (by rw [hmeq]; show (c1.work 0).cells (blockStart k b + 3 * m + 2) ≠ Γ.start; rw [hc2]; exact (encSymΓ_ne_start _).2)]
    rw [hmeq]
    dsimp only
    rw [hc0, hc1, hc2, decSymΓ_encSymΓ (hinv.noStart ⟨m, hmk⟩ b hb1)]
    refine (Cfg.mk.injEq ..).mpr ⟨?_, rfl, rfl, rfl⟩
    congr 3
    funext j
    by_cases hjm : j = (⟨m, hmk⟩ : Fin k)
    · subst hjm
      by_cases hb : (c.work ⟨m, hmk⟩).head = b
      · simp only [hb, ↓reduceIte, Function.update_self, and_true]
        rw [if_pos (Nat.lt_succ_self m), Tape.read, hb]
      · simp only [hb, ↓reduceIte, reduceCtorEq, Nat.lt_irrefl, and_false]
    · have hjv : (j : ℕ) ≠ m := fun h => hjm (Fin.ext h)
      by_cases hjb : (c.work j).head = b
      · by_cases hlt : (↑j : ℕ) < m
        · by_cases hb : (c.work ⟨m, hmk⟩).head = b <;>
            simp [hb, hjb, hlt, Function.update_of_ne hjm, show (↑j : ℕ) < m + 1 from by omega]
        · by_cases hb : (c.work ⟨m, hmk⟩).head = b <;>
            simp [hb, hjb, hlt, Function.update_of_ne hjm, show ¬(↑j : ℕ) < m + 1 from by omega]
      · by_cases hb : (c.work ⟨m, hmk⟩).head = b <;>
          simp [hb, hjb, Function.update_of_ne hjm]

/-- **GATHER full sweep (`trace (3*k*B)`).** Sweeping the first `B ≤ M` blocks
    (starting at block `1`, tape `0`, slot `0`, work head `blockStart k 1`, `acc`
    all `▷`): after `B` blocks the work head is at `blockStart k (B+1)`, the sweep
    is back at tape `0` slot `0`, and `acc` records the read symbol of every tape
    whose head sits in blocks `[1, B]` (and `▷` otherwise). Proved by induction on
    `B`, each step one `gather_block_aux` at block `B+1`. At `B = M` (with
    `heads_le`) every head is covered, so `acc` is exactly the per-tape reads. -/
theorem gather_sweep_aux {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (M : ℕ)
    (q : N.Q) (iSym oSym : Γ) (c1 : Cfg 1 (SimQ k N.Q)) (rf₀ : Bool) (pending₀ : Γ)
    (hst : c1.state =
      SimQ.gather (q, (fun _ => Γ.start), iSym, oSym, (⟨0, by omega⟩, 0), rf₀, pending₀))
    (hhead : (c1.work 0).head = blockStart k 1)
    (hinv : SimInvAt k (c1.work 0) c.work M)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start)
    (B : ℕ) (hB : B ≤ M) :
    ∃ (rf' : Bool) (pending' : Γ),
      (singleTapeSim N).trace (3 * k * B) (fun _ => bb) c1 =
        { state := SimQ.gather (q,
            (fun j => if 1 ≤ (c.work j).head ∧ (c.work j).head ≤ B then (c.work j).read
                      else Γ.start),
            iSym, oSym, (⟨0, by omega⟩, 0), rf', pending'),
          input := c1.input, output := c1.output,
          work := fun _ => { c1.work 0 with head := blockStart k (B + 1) } } := by
  induction B with
  | zero =>
    refine ⟨rf₀, pending₀, ?_⟩
    have h0 : (singleTapeSim N).trace (3 * k * 0) (fun _ => bb) c1 = c1 := by
      simp only [Nat.mul_zero]; rfl
    rw [h0]
    obtain ⟨cst, cin, cwk, cout⟩ := c1
    subst hst
    refine (Cfg.mk.injEq ..).mpr ⟨?_, rfl, ?_, rfl⟩
    · congr 3
      funext j
      rw [if_neg (by omega)]
    · funext x
      obtain rfl : x = 0 := Subsingleton.elim x 0
      show cwk 0 = { cwk 0 with head := blockStart k 1 }
      rw [← hhead]
  | succ B ih =>
    obtain ⟨rfB, pendingB, hBeq⟩ := ih (by omega)
    obtain ⟨rf', pending', hstep⟩ := gather_block_aux N bb c (B + 1) M (by omega) hB q iSym oSym
      (fun j => if 1 ≤ (c.work j).head ∧ (c.work j).head ≤ B then (c.work j).read else Γ.start)
      ((singleTapeSim N).trace (3 * k * B) (fun _ => bb) c1) rfB pendingB
      (by rw [hBeq]) (by rw [hBeq]) (by rw [hBeq]; exact hinv.cells_congr rfl)
      (by rw [hBeq]; exact his) (by rw [hBeq]; exact hos) k (le_refl k)
    refine ⟨rf', pending', ?_⟩
    rw [show 3 * k * (B + 1) = 3 * k * B + 3 * k from Nat.mul_succ (3 * k) B,
        trace_const_add, hstep, hBeq]
    dsimp only
    simp only [lt_self_iff_false, ↓reduceIte]
    rw [blockStart_succ k (B + 1) (by omega), blockWidth]
    refine (Cfg.mk.injEq ..).mpr ⟨?_, rfl, rfl, rfl⟩
    congr 3
    funext j
    simp only [j.isLt, true_and]
    by_cases hjb : (c.work j).head = B + 1
    · simp only [hjb, ↓reduceIte, le_refl, and_true]
      rw [if_pos (by omega)]
    · rw [if_neg hjb]
      by_cases hr : 1 ≤ (c.work j).head ∧ (c.work j).head ≤ B
      · rw [if_pos hr, if_pos (by omega)]
      · rw [if_neg hr, if_neg (by omega)]

/-- One **GATHER sentinel** step (`trace 1`): reading the `□` that ends the used
    region fires `N.δ` (the one meaningful use of the choice `bb`) and hands the
    write/move actions to REWIND, turning the work head leftward. -/
theorem gather_sentinel {k : ℕ} (N : NTM k) (bb : Bool) (q : N.Q) (acc : Fin k → Γ)
    (iSym oSym : Γ) (pos : SweepPos k) (rf : Bool) (pending : Γ) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.gather (q, acc, iSym, oSym, pos, rf, pending))
    (hblank : (c1.work 0).read = Γ.blank) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.rewind ((N.δ bb q iSym acc oSym).1,
          (fun i => ((N.δ bb q iSym acc oSym).2.1 i, (N.δ bb q iSym acc oSym).2.2.2.2.1 i)),
          ((N.δ bb q iSym acc oSym).2.2.1, (N.δ bb q iSym acc oSym).2.2.2.2.2),
          (N.δ bb q iSym acc oSym).2.2.2.1, iSym, oSym, (fun j => decide (acc j = Γ.start))),
        input := c1.input.move (TM.idleDir c1.input.read),
        work := fun i => (c1.work i).writeAndMove Γw.blank.toΓ Dir3.left,
        output := c1.output.writeAndMove (TM.readBackWrite c1.output.read).toΓ
          (TM.idleDir c1.output.read) } := by
  rw [gather_trace1 N (q, acc, iSym, oSym, pos, rf, pending) bb c1 hst]
  simp only [gatherStep, hblank, ↓reduceIte]; rfl

/-- The sweep accumulator at `B = M` is exactly the per-tape reads: a head in
    `[1, M]` had its symbol recorded; a head at `0` reads `▷`, which is also the
    `▷` default the sweep leaves. Uses `heads_le` (every head `≤ M`) and
    `head0_read` (a head at `0` reads `▷`). -/
theorem gather_acc_eq {k : ℕ} {t : Tape} {w : Fin k → Tape} {M : ℕ}
    (hinv : SimInvAt k t w M) :
    (fun j => if 1 ≤ (w j).head ∧ (w j).head ≤ M then (w j).read else Γ.start)
      = (fun j : Fin k => (w j).read) := by
  funext j
  by_cases h1 : 1 ≤ (w j).head
  · rw [if_pos ⟨h1, hinv.heads_le j⟩]
  · rw [if_neg (fun h => h1 h.1), hinv.head0_read j (by omega)]

/-- One **rewind** step (`trace 1`): from a `rewind d` config, the result is the
    configuration built from `rewindStep`'s output. Basis of the rewind sweep. -/
theorem rewind_trace1 {k : ℕ} (N : NTM k) (d : RewindData k N.Q) (b : Bool)
    (c1 : Cfg 1 (SimQ k N.Q)) (hst : c1.state = SimQ.rewind d) :
    (singleTapeSim N).trace 1 (fun _ => b) c1 =
      (let r := rewindStep d c1.input.read ((c1.work 0).read) c1.output.read
       { state := r.1, input := c1.input.move r.2.2.2.1,
         work := fun i => (c1.work i).writeAndMove (r.2.1 i) (r.2.2.2.2.1 i),
         output := c1.output.writeAndMove r.2.2.1 r.2.2.2.2.2 } : Cfg 1 (SimQ k N.Q)) := by
  rw [NTM.trace]
  simp only [hst, singleTapeSim, simDelta, SimQ.rewind, SimQ.halt, Sum.inr.injEq,
    reduceCtorEq, ↓reduceIte, NTM.trace]

/-- **REWIND full sweep (`trace (p+1)`).** From a `rewind` config with the work
    head at cell `p` (every cell in `[1,p]` a non-`▷` code cell, cell `0` the `▷`),
    the leftward sweep carries the `δ` results untouched back to cell `0`, then
    turns around into SCATTER sweep-1 at cell `1` (empty stay/left carries). Proved
    by induction on `p` (one `rewindStep` per cell), contents preserved throughout. -/
theorem rewind_sweep {k : ℕ} (N : NTM k) (bb : Bool)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (initRC : Fin k → Bool) (c1 : Cfg 1 (SimQ k N.Q)) (p : ℕ)
    (hst : c1.state = SimQ.rewind (q', wact, oWoD, iD, iSym, oSym, initRC))
    (hhead : (c1.work 0).head = p)
    (hcell0 : (c1.work 0).cells 0 = Γ.start)
    (hne : ∀ p', 1 ≤ p' → p' ≤ p → (c1.work 0).cells p' ≠ Γ.start)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace (p + 1) (fun _ => bb) c1 =
      { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, (0, 0), initRC,
          (fun _ => false), false, false),
        input := c1.input,
        work := fun _ => { c1.work 0 with head := 1 },
        output := c1.output } := by
  induction p generalizing c1 with
  | zero =>
    have hread : (c1.work 0).read = Γ.start := by rw [Tape.read, hhead]; exact hcell0
    rw [rewind_trace1 N (q', wact, oWoD, iD, iSym, oSym, initRC) bb c1 hst]
    simp only [rewindStep, hread, ↓reduceIte, tape_idle_stay c1.input his,
      tape_idle_writeMove c1.output hos]
    congr 1
    funext x
    obtain rfl : x = 0 := Subsingleton.elim x 0
    exact work_blank_right_at0 (c1.work 0) hhead
  | succ p ih =>
    have hread : (c1.work 0).read ≠ Γ.start := by
      rw [Tape.read, hhead]; exact hne (p + 1) (by omega) (le_refl _)
    have e1 : (singleTapeSim N).trace 1 (fun _ => bb) c1 =
        { state := SimQ.rewind (q', wact, oWoD, iD, iSym, oSym, initRC),
          input := c1.input,
          work := fun _ => { c1.work 0 with head := (c1.work 0).head - 1 },
          output := c1.output } := by
      rw [rewind_trace1 N (q', wact, oWoD, iD, iSym, oSym, initRC) bb c1 hst]
      simp only [rewindStep, hread, ↓reduceIte, tape_idle_stay c1.input his,
        tape_idle_writeMove c1.output hos]
      congr 1
      funext x; obtain rfl : x = 0 := Subsingleton.elim x 0
      exact work_rewind_step (c1.work 0) hread
    rw [show p + 1 + 1 = 1 + (p + 1) from by omega, trace_const_add, e1]
    exact ih _ rfl (by simp [hhead]) hcell0
      (fun p' hp1 hp2 => hne p' hp1 (by omega)) his hos

/-- **Intermediate work tape after SCATTER sweep-1** (before sweep-2 relocates the
    left-movers). For tape `t` with old tape `ct` and `N.δ` action `(w, d)`: the
    new symbol `w` is written at the old head position; the head-bit is placed at
    the new position for `stay`/`right` movers, but is **left at the old position**
    for left-movers — SCATTER sweep-2 moves those one block left. A head reading
    `▷` (position 0) is forced `right` by `δ_right_of_start`, so it lands at
    position 1 (the `▷` symbol write is a no-op at cell 0). Thus `head` here is
    `ct.head + 1` for right-movers and `ct.head` for stay/left-movers. -/
def scatterInterWork (ct : Tape) (wd : Γw × Dir3) : Tape where
  head := if wd.2 = Dir3.right then ct.head + 1 else ct.head
  cells := (ct.write wd.1.toΓ).cells

/-- `scatterInterWork` only rewrites the old head cell: every other cell is
    unchanged. (The new symbol is written at the old head position.) -/
theorem scatterInterWork_cells_of_ne (ct : Tape) (wd : Γw × Dir3) {c : ℕ}
    (h : c ≠ ct.head) : (scatterInterWork ct wd).cells c = ct.cells c := by
  show (ct.write wd.1.toΓ).cells c = ct.cells c
  unfold Tape.write
  split
  · rfl
  · exact Function.update_of_ne h _ _

/-- `scatterInterWork` preserves cell `0` (the `▷` marker): writing at the head
    never touches cell `0` (it's either a no-op there, or the head is `≥ 1`). -/
theorem scatterInterWork_cells_zero (ct : Tape) (wd : Γw × Dir3) :
    (scatterInterWork ct wd).cells 0 = ct.cells 0 := by
  show (ct.write wd.1.toΓ).cells 0 = ct.cells 0
  unfold Tape.write
  split
  · rfl
  · exact Function.update_of_ne (by omega) _ _

/-- `scatterInterWork` keeps every cell `≥ 1` non-`▷`: untouched cells inherit it
    from `ct`, and the rewritten head cell holds a writable symbol (`Γw`, which
    excludes `▷`). The `noStart` precondition for the post-sweep `SimInvAt (M+1)`. -/
theorem scatterInterWork_cells_ne_start (ct : Tape) (wd : Γw × Dir3) {p : ℕ}
    (hp : 1 ≤ p) (hns : ct.cells p ≠ Γ.start) :
    (scatterInterWork ct wd).cells p ≠ Γ.start := by
  by_cases hph : p = ct.head
  · rw [hph]
    show (ct.write wd.1.toΓ).cells ct.head ≠ Γ.start
    unfold Tape.write
    rw [if_neg (show ¬ ct.head = 0 by omega)]
    show Function.update ct.cells ct.head wd.1.toΓ ct.head ≠ Γ.start
    rw [Function.update_self]
    cases wd.1 <;> decide
  · rw [scatterInterWork_cells_of_ne ct wd hph]; exact hns

/-- `scatterInterWork`'s head stays within the materialized region after growth:
    a right-mover advances by one (to `≤ M+1`), others stay. The `heads_le`
    precondition for the post-sweep `SimInvAt (M+1)`. -/
theorem scatterInterWork_head_le (ct : Tape) (wd : Γw × Dir3) {M : ℕ}
    (h : ct.head ≤ M) : (scatterInterWork ct wd).head ≤ M + 1 := by
  show (if wd.2 = Dir3.right then ct.head + 1 else ct.head) ≤ M + 1
  split <;> omega

/-- `scatterInterWork`'s head value: a right-mover advances by one, every other
    move keeps the old head position. (The `head` half of the intermediate
    encoding's head-bit.) -/
theorem scatterInterWork_head (ct : Tape) (wd : Γw × Dir3) :
    (scatterInterWork ct wd).head = if wd.2 = Dir3.right then ct.head + 1 else ct.head :=
  rfl

/-- `scatterInterWork` writes the new symbol at the old head position (when the
    head is `≥ 1`, where `write` is not a no-op). The `sym` half of the
    intermediate encoding at the head's block. -/
theorem scatterInterWork_cells_at_head (ct : Tape) (wd : Γw × Dir3)
    (hh : 1 ≤ ct.head) : (scatterInterWork ct wd).cells ct.head = wd.1.toΓ := by
  show (ct.write wd.1.toΓ).cells ct.head = wd.1.toΓ
  unfold Tape.write
  rw [if_neg (show ¬ ct.head = 0 by omega)]
  show Function.update ct.cells ct.head wd.1.toΓ ct.head = wd.1.toΓ
  rw [Function.update_self]

/-- The SCATTER head triples write the symbol via the **writable** codec
    (`encSymW s`), but the `scatterInterWork` target reads it via the
    full-alphabet codec applied to the written cell (`encSymΓ s.toΓ`). They
    agree (both route through `encSym`): this matches a head triple's two symbol
    writes to the intermediate encoding at the head's block. -/
theorem encSymW_toΓ_eq_encSymΓ (s : Γw) :
    (encSymW s).1.toΓ = (encSymΓ s.toΓ).1 ∧ (encSymW s).2.toΓ = (encSymΓ s.toΓ).2 := by
  cases s <;> exact ⟨rfl, rfl⟩

/-- **Mid-sweep invariant for SCATTER sweep-1**, at block boundary `b`: the work
    tape `t` holds the **intermediate** encoding (`scatterInterWork`) on blocks
    `[1, b)` already swept, and the **old** encoding (`w`) on blocks `[b, M]` not
    yet reached, with the `▷` at cell 0 and the sentinel region blank beyond block
    `M`. (The in-flight `rightCarry` lives in the SCATTER state, not the tape.) The
    block step advances this `b → b+1`; at `b = 1` it's the REWIND output (all old),
    at `b = M+1` the whole region is intermediate-encoded. -/
structure Scatter1MidInv {k : ℕ} (t : Tape) (w : Fin k → Tape)
    (wact : Fin k → Γw × Dir3) (M b : ℕ) : Prop where
  /-- Cell 0 is the global start marker `▷`. -/
  cell0 : t.cells 0 = Γ.start
  /-- Blocks `[1, b)` already swept: intermediate (`scatterInterWork`) encoding. -/
  donePart : ∀ p, 1 ≤ p → p < b → ∀ j : Fin k,
    t.cells (headBitCell k p j)
        = (if (scatterInterWork (w j) (wact j)).head = p then Γ.one else Γ.zero) ∧
      t.cells (symCell k p j) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells p)).1 ∧
      t.cells (symCell k p j + 1) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells p)).2
  /-- Blocks `[b, M]` not yet reached: the old encoding (`SimInvAt M`). -/
  oldPart : ∀ p, b ≤ p → p ≤ M → ∀ j : Fin k,
    t.cells (headBitCell k p j) = (if (w j).head = p then Γ.one else Γ.zero) ∧
      t.cells (symCell k p j) = (encSymΓ ((w j).cells p)).1 ∧
      t.cells (symCell k p j + 1) = (encSymΓ ((w j).cells p)).2
  /-- The sentinel region (block `M+1` onward) is blank. -/
  sentinel : ∀ c : ℕ, blockStart k (M + 1) ≤ c → t.cells c = Γ.blank

/-- **Base case** of the mid-sweep invariant: the REWIND output (whole region
    still old-encoded, `SimInvAt M`) is `Scatter1MidInv` at `b = 1` (no swept
    blocks yet). -/
theorem scatter1MidInv_init {k : ℕ} {t : Tape} {w : Fin k → Tape}
    (wact : Fin k → Γw × Dir3) {M : ℕ} (h : SimInvAt k t w M) :
    Scatter1MidInv t w wact M 1 where
  cell0 := h.cell0
  donePart := fun _ _ hp2 _ => absurd hp2 (by omega)
  oldPart := fun p hp1 hpM j =>
    ⟨h.headBit p hp1 hpM j, (h.sym p hp1 hpM j).1, (h.sym p hp1 hpM j).2⟩
  sentinel := h.sentinel

/-- **Final case** of the mid-sweep invariant: once all `M` blocks are swept
    (`b = M+1`), the whole materialized region is intermediate-encoded — exactly
    the `SimInvAt M`-style facts for `scatterInterWork (w j) (wact j)` on `[1, M]`. -/
theorem Scatter1MidInv.done {k : ℕ} {t : Tape} {w : Fin k → Tape}
    {wact : Fin k → Γw × Dir3} {M : ℕ} (h : Scatter1MidInv t w wact M (M + 1))
    (p : ℕ) (hp1 : 1 ≤ p) (hpM : p ≤ M) (j : Fin k) :
    t.cells (headBitCell k p j)
        = (if (scatterInterWork (w j) (wact j)).head = p then Γ.one else Γ.zero) ∧
      t.cells (symCell k p j) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells p)).1 ∧
      t.cells (symCell k p j + 1) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells p)).2 :=
  h.donePart p hp1 (by omega) j

/-- **Within-block partial invariant** for the SCATTER sweep-1 block step: like
    `Scatter1MidInv` at boundary `b`, but block `b` itself is split — its first
    `m` tapes are already intermediate-encoded (`scatterInterWork`), the rest still
    old. The tape-by-tape block step advances `m → m+1`; `… b 0` is `Scatter1MidInv
    … b` and `… b k` is `Scatter1MidInv … (b+1)` (see `ofMid`/`toMidSucc`). -/
structure Scatter1BlockInv {k : ℕ} (t : Tape) (w : Fin k → Tape)
    (wact : Fin k → Γw × Dir3) (M b m : ℕ) : Prop where
  /-- Cell 0 is the global start marker `▷`. -/
  cell0 : t.cells 0 = Γ.start
  /-- Blocks `[1, b)`: intermediate (`scatterInterWork`) encoding. -/
  donePart : ∀ p, 1 ≤ p → p < b → ∀ j : Fin k,
    t.cells (headBitCell k p j)
        = (if (scatterInterWork (w j) (wact j)).head = p then Γ.one else Γ.zero) ∧
      t.cells (symCell k p j) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells p)).1 ∧
      t.cells (symCell k p j + 1) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells p)).2
  /-- Block `b`, tapes `[0, m)`: already intermediate-encoded. -/
  doneTape : ∀ j : Fin k, (j : ℕ) < m →
    t.cells (headBitCell k b j)
        = (if (scatterInterWork (w j) (wact j)).head = b then Γ.one else Γ.zero) ∧
      t.cells (symCell k b j) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells b)).1 ∧
      t.cells (symCell k b j + 1) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells b)).2
  /-- Block `b`, tapes `[m, k)`: still old. -/
  oldTape : ∀ j : Fin k, m ≤ (j : ℕ) →
    t.cells (headBitCell k b j) = (if (w j).head = b then Γ.one else Γ.zero) ∧
      t.cells (symCell k b j) = (encSymΓ ((w j).cells b)).1 ∧
      t.cells (symCell k b j + 1) = (encSymΓ ((w j).cells b)).2
  /-- Blocks `(b, M]`: still old. -/
  oldPart : ∀ p, b < p → p ≤ M → ∀ j : Fin k,
    t.cells (headBitCell k p j) = (if (w j).head = p then Γ.one else Γ.zero) ∧
      t.cells (symCell k p j) = (encSymΓ ((w j).cells p)).1 ∧
      t.cells (symCell k p j + 1) = (encSymΓ ((w j).cells p)).2
  /-- The sentinel region (block `M+1` onward) is blank. -/
  sentinel : ∀ c : ℕ, blockStart k (M + 1) ≤ c → t.cells c = Γ.blank

/-- Entering block `b` (no tapes processed yet): `Scatter1MidInv … b` is the block
    invariant at `m = 0`. The block-`b` old facts come from `oldPart` at `p = b`. -/
theorem Scatter1BlockInv.ofMid {k : ℕ} {t : Tape} {w : Fin k → Tape}
    {wact : Fin k → Γw × Dir3} {M b : ℕ} (hbM : b ≤ M)
    (h : Scatter1MidInv t w wact M b) : Scatter1BlockInv t w wact M b 0 where
  cell0 := h.cell0
  donePart := h.donePart
  doneTape := fun _ hj => absurd hj (by omega)
  oldTape := fun j _ => h.oldPart b (le_refl b) hbM j
  oldPart := fun p hp hpM j => h.oldPart p (by omega) hpM j
  sentinel := h.sentinel

/-- Leaving block `b` (all `k` tapes processed): `Scatter1BlockInv … b k` is
    `Scatter1MidInv … (b+1)`. The new `donePart` at `p = b` is the just-finished
    `doneTape` (every `j : Fin k` satisfies `j < k`). -/
theorem Scatter1BlockInv.toMidSucc {k : ℕ} {t : Tape} {w : Fin k → Tape}
    {wact : Fin k → Γw × Dir3} {M b : ℕ}
    (h : Scatter1BlockInv t w wact M b k) : Scatter1MidInv t w wact M (b + 1) where
  cell0 := h.cell0
  donePart := fun p hp1 hpb j => by
    rcases Nat.lt_or_ge p b with hlt | hge
    · exact h.donePart p hp1 hlt j
    · obtain rfl : p = b := by omega
      exact h.doneTape j j.isLt
  oldPart := fun p hp hpM j => h.oldPart p (by omega) hpM j
  sentinel := h.sentinel

/-- **Block-step cell bookkeeping (pure).** Advancing the within-block invariant
    one tape: if a new tape `t'` agrees with `t` everywhere except block `b` tape
    `m`'s three cells, which now hold the **intermediate** (`scatterInterWork`)
    encoding, and `t` satisfies `Scatter1BlockInv … b m`, then `t'` satisfies
    `Scatter1BlockInv … b (m+1)`. All other queried cells are untouched (block `b`
    tape `m`'s triple sits at `[blockStart b + 3m, +2]`, disjoint from every other
    `(p,j)` triple, cell 0 and the sentinel region). The five SCATTER triples each
    discharge the three value hypotheses; this lemma does the disjointness once. -/
theorem scatter1_blockinv_step {k : ℕ} {t t' : Tape} {w : Fin k → Tape}
    {wact : Fin k → Γw × Dir3} {M b m : ℕ} (hb1 : 1 ≤ b) (hbM : b ≤ M) (hmk : m < k)
    (hbm : Scatter1BlockInv t w wact M b m)
    (hbit : t'.cells (headBitCell k b ⟨m, hmk⟩)
        = if (scatterInterWork (w ⟨m, hmk⟩) (wact ⟨m, hmk⟩)).head = b then Γ.one else Γ.zero)
    (hs1 : t'.cells (symCell k b ⟨m, hmk⟩)
        = (encSymΓ ((scatterInterWork (w ⟨m, hmk⟩) (wact ⟨m, hmk⟩)).cells b)).1)
    (hs2 : t'.cells (symCell k b ⟨m, hmk⟩ + 1)
        = (encSymΓ ((scatterInterWork (w ⟨m, hmk⟩) (wact ⟨m, hmk⟩)).cells b)).2)
    (hpres : ∀ c, c ≠ headBitCell k b ⟨m, hmk⟩ → c ≠ symCell k b ⟨m, hmk⟩ →
        c ≠ symCell k b ⟨m, hmk⟩ + 1 → t'.cells c = t.cells c) :
    Scatter1BlockInv t' w wact M b (m + 1) where
  cell0 := by
    rw [hpres 0 (by simp only [headBitCell]; have := one_le_blockStart k b; omega)
      (by simp only [symCell]; have := one_le_blockStart k b; omega)
      (by simp only [symCell]; have := one_le_blockStart k b; omega)]
    exact hbm.cell0
  donePart := fun p hp1 hpb j => by
    have key : blockStart k p + 3 * (j : ℕ) + 2 < blockStart k b + 3 * m := by
      have hA := headBitCell_add_three_le k p j hp1
      have hB := blockStart_le k (show p + 1 ≤ b by omega)
      simp only [headBitCell] at hA; omega
    rw [hpres (headBitCell k p j) (by simp only [headBitCell]; omega)
          (by simp only [headBitCell, symCell]; omega) (by simp only [headBitCell, symCell]; omega),
        hpres (symCell k p j) (by simp only [headBitCell, symCell]; omega)
          (by simp only [symCell]; omega) (by simp only [symCell]; omega),
        hpres (symCell k p j + 1) (by simp only [headBitCell, symCell]; omega)
          (by simp only [symCell]; omega) (by simp only [symCell]; omega)]
    exact hbm.donePart p hp1 hpb j
  doneTape := fun j hj => by
    rcases Nat.lt_or_ge (j : ℕ) m with hlt | hge
    · have key : blockStart k b + 3 * (j : ℕ) + 2 < blockStart k b + 3 * m := by omega
      rw [hpres (headBitCell k b j) (by simp only [headBitCell]; omega)
            (by simp only [headBitCell, symCell]; omega) (by simp only [headBitCell, symCell]; omega),
          hpres (symCell k b j) (by simp only [headBitCell, symCell]; omega)
            (by simp only [symCell]; omega) (by simp only [symCell]; omega),
          hpres (symCell k b j + 1) (by simp only [headBitCell, symCell]; omega)
            (by simp only [symCell]; omega) (by simp only [symCell]; omega)]
      exact hbm.doneTape j hlt
    · have hjm : (j : ℕ) = m := by omega
      obtain rfl : j = ⟨m, hmk⟩ := Fin.ext hjm
      exact ⟨hbit, hs1, hs2⟩
  oldTape := fun j hj => by
    have key : blockStart k b + 3 * m + 2 < blockStart k b + 3 * (j : ℕ) := by omega
    rw [hpres (headBitCell k b j) (by simp only [headBitCell]; omega)
          (by simp only [headBitCell, symCell]; omega) (by simp only [headBitCell, symCell]; omega),
        hpres (symCell k b j) (by simp only [headBitCell, symCell]; omega)
          (by simp only [symCell]; omega) (by simp only [symCell]; omega),
        hpres (symCell k b j + 1) (by simp only [headBitCell, symCell]; omega)
          (by simp only [symCell]; omega) (by simp only [symCell]; omega)]
    exact hbm.oldTape j (by omega)
  oldPart := fun p hp hpM j => by
    have key : blockStart k b + 3 * m + 2 < blockStart k p := by
      have hC := blockStart_le k (show b + 1 ≤ p by omega)
      have hD := blockStart_succ k b hb1
      have hbw : blockWidth k = 3 * k := rfl
      omega
    rw [hpres (headBitCell k p j) (by simp only [headBitCell]; have := j.isLt; omega)
          (by simp only [headBitCell, symCell]; have := j.isLt; omega)
          (by simp only [headBitCell, symCell]; have := j.isLt; omega),
        hpres (symCell k p j) (by simp only [headBitCell, symCell]; have := j.isLt; omega)
          (by simp only [symCell]; have := j.isLt; omega) (by simp only [symCell]; have := j.isLt; omega),
        hpres (symCell k p j + 1) (by simp only [headBitCell, symCell]; have := j.isLt; omega)
          (by simp only [symCell]; have := j.isLt; omega) (by simp only [symCell]; have := j.isLt; omega)]
    exact hbm.oldPart p hp hpM j
  sentinel := fun c hc => by
    have key : blockStart k b + 3 * m + 2 < blockStart k (M + 1) := by
      have hE := blockStart_le k (show b + 1 ≤ M + 1 by omega)
      have hD := blockStart_succ k b hb1
      have hbw : blockWidth k = 3 * k := rfl
      omega
    rw [hpres c (by simp only [headBitCell]; omega) (by simp only [symCell]; omega)
          (by simp only [symCell]; omega)]
    exact hbm.sentinel c hc

/-- **SCATTER sweep-1 design plan.** The sweep starts (from REWIND) at cell 1,
    `pos (0,0)`, `rightCarry = initRC` (= heads that were at position 0, forced
    right), all other flags empty. It sweeps right over the `M` old blocks then
    materializes block `M+1`, in `3*k*(M+1) + 1` steps, ending in SCATTER sweep-2.

    The correctness invariant (mid-sweep, head at block `b`): cells of blocks
    `< b` hold the **intermediate** encoding (`scatterInterWork`), cells of blocks
    `≥ b` (in the old region) still hold the **old** encoding (`SimInvAt M`), and
    `rightCarry t` flags a head that moved right out of block `b-1` and is pending
    deposit at block `b`. Suggested decomposition mirrors GATHER:
    `triple → block (incoming rc → outgoing rc) → sweep over M blocks → materialize
    block M+1 → turnaround`. The post-sweep tape is `SimInvAt (M+1)` for
    `fun t => scatterInterWork (c.work t) (wact t)`, with `isLeftMover t = decide
    ((wact t).2 = .left)`; SCATTER sweep-2 then finishes the left-movers to reach
    `SimInvAt (M+1)` for `c'`. (Proof: the research-grade core, in progress.) -/
theorem scatter1_sweep_PLAN : True := trivial

/-- **SCATTER sweep-1 — target (the crux, proof in progress).** From the
    REWIND-produced `scatter1` config (cell 1, `pos (0,0)`, `rightCarry` marking
    the position-0 heads, all else empty, encoding the old `c.work` at `M`), the
    sweep runs `3*k*(M+1) + 1` steps and lands in SCATTER sweep-2 with the work
    tape encoding the **intermediate** configuration (`scatterInterWork` — new
    symbols everywhere, right/stay heads relocated, left-movers parked at the old
    spot) materialized to `M+1`, recording the left-movers in `isLeftMover`. The
    work tape is existential (its exact head position is incidental — sweep-2
    consumes it). This is the research-grade core; the proof will decompose as
    `triple → block (rightCarry in→out) → M-block sweep → materialize → turnaround`. -/
theorem scatter1_sweep {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (M : ℕ)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, (0, 0),
        (fun j => decide ((c.work j).read = Γ.start)), (fun _ => false), false, false))
    (hhead : (c1.work 0).head = blockStart k 1)
    (hinv : SimInvAt k (c1.work 0) c.work M)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    ∃ wfin : Fin 1 → Tape,
      (singleTapeSim N).trace (3 * k * (M + 1) + 1) (fun _ => bb) c1 =
        { state := SimQ.scatter2 (q', oWoD, iD, iSym, oSym, (⟨k - 1, by omega⟩, 2),
            (fun t => decide ((wact t).2 = Dir3.left)), (fun _ => false)),
          input := c1.input, work := wfin, output := c1.output }
      ∧ SimInvAt k (wfin 0) (fun t => scatterInterWork (c.work t) (wact t)) (M + 1) := by
  sorry

/-- One **scatter sweep-1** step (`trace 1`): from a `scatter1 d` config, the
    result is the configuration built from `scatter1Step`'s output. Basis of the
    SCATTER sweep-1 correctness (the phase that writes `N`'s new configuration and
    materializes a fresh block). -/
theorem scatter1_trace1 {k : ℕ} (N : NTM k) (d : Scatter1Data k N.Q) (b : Bool)
    (c1 : Cfg 1 (SimQ k N.Q)) (hst : c1.state = SimQ.scatter1 d) :
    (singleTapeSim N).trace 1 (fun _ => b) c1 =
      (let r := scatter1Step d c1.input.read ((c1.work 0).read) c1.output.read
       { state := r.1, input := c1.input.move r.2.2.2.1,
         work := fun i => (c1.work i).writeAndMove (r.2.1 i) (r.2.2.2.2.1 i),
         output := c1.output.writeAndMove r.2.2.1 r.2.2.2.2.2 } : Cfg 1 (SimQ k N.Q)) := by
  rw [NTM.trace]
  simp only [hst, singleTapeSim, simDelta, SimQ.scatter1, SimQ.halt, Sum.inr.injEq,
    reduceCtorEq, ↓reduceIte, NTM.trace]

/-- A SCATTER sweep-1 **non-sentinel step** (`trace 1`): on any cell other than the
    `□` sentinel, the work head writes `scatter1Step`'s computed symbol and moves
    right (input/output idle), landing in `scatter1Step`'s next state. The case
    logic (head-bit handling, symbol writes, marker carries) stays packaged inside
    `scatter1Step` for the sweep induction to unfold per cell. -/
theorem scatter1_step_right {k : ℕ} (N : NTM k) (d : Scatter1Data k N.Q) (b : Bool)
    (c1 : Cfg 1 (SimQ k N.Q)) (hst : c1.state = SimQ.scatter1 d)
    (hwb : (c1.work 0).read ≠ Γ.blank)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => b) c1 =
      { state := (scatter1Step d c1.input.read ((c1.work 0).read) c1.output.read).1,
        input := c1.input,
        work := fun i => (c1.work i).writeAndMove
          ((scatter1Step d c1.input.read ((c1.work 0).read) c1.output.read).2.1 i).toΓ Dir3.right,
        output := c1.output } := by
  rw [scatter1_trace1 N d b c1 hst]
  have hwd : (scatter1Step d c1.input.read ((c1.work 0).read) c1.output.read).2.2.2.2.1
      = fun _ => Dir3.right := by
    funext i
    show (if (c1.work 0).read = Γ.blank ∧ _ then Dir3.left else Dir3.right) = Dir3.right
    rw [if_neg (fun h => hwb h.1)]
  simp only [show (scatter1Step d c1.input.read ((c1.work 0).read) c1.output.read).2.2.2.1
      = TM.idleDir c1.input.read from rfl,
    show (scatter1Step d c1.input.read ((c1.work 0).read) c1.output.read).2.2.1
      = TM.readBackWrite c1.output.read from rfl,
    show (scatter1Step d c1.input.read ((c1.work 0).read) c1.output.read).2.2.2.2.2
      = TM.idleDir c1.output.read from rfl,
    hwd, tape_idle_stay c1.input his, tape_idle_writeMove c1.output hos]; rfl

/-- A SCATTER sweep-1 **materialize step** (`trace 1`): at the `□` sentinel, before
    the new block is complete (`¬(mat ∧ pos = (0,0))`), the head writes the fresh
    cell's value (`scatter1Step`'s symbol — a head-bit per `rightCarry` at slot 0,
    `□` otherwise) and moves right, growing the region by one cell. Same shape as
    `scatter1_step_right`; the work direction is right because the turn-around
    guard is false. -/
theorem scatter1_materialize {k : ℕ} (N : NTM k) (b : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (pos : SweepPos k) (rightCarry isLeftMover : Fin k → Bool) (writeFlag mat : Bool)
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, pos, rightCarry, isLeftMover, writeFlag, mat))
    (hnt : ¬(mat = true ∧ pos = (0, 0)))
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => b) c1 =
      (let d := (q', wact, oWoD, iD, iSym, oSym, pos, rightCarry, isLeftMover, writeFlag, mat)
       { state := (scatter1Step d c1.input.read ((c1.work 0).read) c1.output.read).1,
         input := c1.input,
         work := fun i => (c1.work i).writeAndMove
           ((scatter1Step d c1.input.read ((c1.work 0).read) c1.output.read).2.1 i).toΓ Dir3.right,
         output := c1.output } : Cfg 1 (SimQ k N.Q)) := by
  rw [scatter1_trace1 N
    (q', wact, oWoD, iD, iSym, oSym, pos, rightCarry, isLeftMover, writeFlag, mat) b c1 hst]
  have hwd : (scatter1Step
      (q', wact, oWoD, iD, iSym, oSym, pos, rightCarry, isLeftMover, writeFlag, mat)
      c1.input.read ((c1.work 0).read) c1.output.read).2.2.2.2.1 = fun _ => Dir3.right := by
    funext i
    show (if (c1.work 0).read = Γ.blank ∧ mat = true ∧ pos = (0, 0) then Dir3.left
          else Dir3.right) = Dir3.right
    rw [if_neg (fun h => hnt h.2)]
  simp only [show (scatter1Step
        (q', wact, oWoD, iD, iSym, oSym, pos, rightCarry, isLeftMover, writeFlag, mat)
        c1.input.read ((c1.work 0).read) c1.output.read).2.2.2.1
      = TM.idleDir c1.input.read from rfl,
    show (scatter1Step
        (q', wact, oWoD, iD, iSym, oSym, pos, rightCarry, isLeftMover, writeFlag, mat)
        c1.input.read ((c1.work 0).read) c1.output.read).2.2.1
      = TM.readBackWrite c1.output.read from rfl,
    show (scatter1Step
        (q', wact, oWoD, iD, iSym, oSym, pos, rightCarry, isLeftMover, writeFlag, mat)
        c1.input.read ((c1.work 0).read) c1.output.read).2.2.2.2.2
      = TM.idleDir c1.output.read from rfl,
    hwd, tape_idle_stay c1.input his, tape_idle_writeMove c1.output hos]

/-- SCATTER sweep-1 **materialize slot-0** step: at the `□` sentinel, slot `0` of
    a fresh block-tape, deposit the head-bit (`one` if `rightCarry t`, else `zero`),
    clear that carry, set `mat`, and advance to slot 1. The right-movers carried out
    of the last old block land here. -/
theorem scatter1_mat_slot0 {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (t : ℕ) (ht : t < k) (rc ilm : Fin k → Bool) (mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨t, by omega⟩, 0), rc, ilm, false, mat))
    (hblank : (c1.work 0).read = Γ.blank) (hh : 1 ≤ (c1.work 0).head)
    (hnt : ¬(mat = true ∧ ((⟨t, by omega⟩, 0) : SweepPos k) = (0, 0)))
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, (⟨t, by omega⟩, 1),
          Function.update rc ⟨t, ht⟩ false, ilm, false, true),
        input := c1.input,
        work := fun _ => ⟨(c1.work 0).head + 1, Function.update (c1.work 0).cells (c1.work 0).head
          (if rc ⟨t, ht⟩ then Γw.one else Γw.zero).toΓ⟩,
        output := c1.output } := by
  rw [scatter1_materialize N bb q' wact oWoD iD iSym oSym (⟨t, by omega⟩, 0) rc ilm false mat c1 hst
    hnt his hos]
  simp only [scatter1Step, hblank, ↓reduceIte, if_neg hnt, dif_pos ht, advanceSweep, Fin.reduceEq,
    Fin.isValue]
  congr 1
  funext i
  obtain rfl : i = 0 := Subsingleton.elim i 0
  exact work_write_right (c1.work 0) _ hh

/-- SCATTER sweep-1 **materialize symbol** step: at the `□` sentinel, slot `1` or `2`
    of a fresh block-tape, write the blank-symbol code cell (`Γw.zero`) and advance.
    `rightCarry`/`isLeftMover` untouched; the new block's symbols are all `□`. -/
theorem scatter1_mat_sym {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (t : ℕ) (ht : t < k) (s : Fin 3) (hs : s ≠ 0) (rc ilm : Fin k → Bool) (wf : Bool)
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨t, by omega⟩, s), rc, ilm, wf, true))
    (hblank : (c1.work 0).read = Γ.blank) (hh : 1 ≤ (c1.work 0).head)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, advanceSweep k (⟨t, by omega⟩, s),
          rc, ilm, false, true),
        input := c1.input,
        work := fun _ => ⟨(c1.work 0).head + 1,
          Function.update (c1.work 0).cells (c1.work 0).head Γw.zero.toΓ⟩,
        output := c1.output } := by
  have hpos : (((⟨t, by omega⟩, s) : SweepPos k) = (0, 0)) = False :=
    eq_false (fun h => hs (congrArg Prod.snd h))
  have hnt : ¬(true = true ∧ ((⟨t, by omega⟩, s) : SweepPos k) = (0, 0)) := by
    rintro ⟨-, h⟩; exact hs (congrArg Prod.snd h)
  rw [scatter1_materialize N bb q' wact oWoD iD iSym oSym (⟨t, by omega⟩, s) rc ilm wf true c1 hst
    hnt his hos]
  simp only [scatter1Step, hblank, hpos, and_false, hs, ↓reduceIte, Fin.isValue]
  congr 1
  funext i
  obtain rfl : i = 0 := Subsingleton.elim i 0
  exact work_write_right (c1.work 0) _ hh

/-- SCATTER sweep-1 **materialize triple** (`trace 3`): materialize one fresh
    block-tape (3 blank cells) — deposit the head-bit (`one` iff `rightCarry t`),
    then two blank-symbol cells (`□`), clearing `rightCarry t` and setting `mat`. The
    work head advances by 3 to the next tape's slot 0. -/
theorem scatter1_mat_triple {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (t : ℕ) (ht : t < k) (rc ilm : Fin k → Bool) (mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨t, by omega⟩, 0), rc, ilm, false, mat))
    (hh : 1 ≤ (c1.work 0).head)
    (hb0 : (c1.work 0).cells ((c1.work 0).head) = Γ.blank)
    (hb1 : (c1.work 0).cells ((c1.work 0).head + 1) = Γ.blank)
    (hb2 : (c1.work 0).cells ((c1.work 0).head + 2) = Γ.blank)
    (hnt : ¬(mat = true ∧ ((⟨t, by omega⟩, 0) : SweepPos k) = (0, 0)))
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 3 (fun _ => bb) c1 =
      { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
          (⟨if t + 1 < k then t + 1 else 0, by split <;> omega⟩, 0),
          Function.update rc ⟨t, ht⟩ false, ilm, false, true),
        input := c1.input,
        work := fun _ => ⟨(c1.work 0).head + 3,
          Function.update (Function.update (Function.update (c1.work 0).cells
            (c1.work 0).head (if rc ⟨t, ht⟩ then Γw.one else Γw.zero).toΓ)
            ((c1.work 0).head + 1) Γw.zero.toΓ)
            ((c1.work 0).head + 2) Γw.zero.toΓ⟩,
        output := c1.output } := by
  have e0 := scatter1_mat_slot0 N bb q' wact oWoD iD iSym oSym t ht rc ilm mat c1 hst
    (by rw [Tape.read]; exact hb0) hh hnt his hos
  have e1 := scatter1_mat_sym N bb q' wact oWoD iD iSym oSym t ht 1 (by decide)
    (Function.update rc ⟨t, ht⟩ false) ilm false ((singleTapeSim N).trace 1 (fun _ => bb) c1)
    (by rw [e0]) (by rw [e0]; simp only [Tape.read]; rw [Function.update_of_ne (by omega)]; exact hb1)
    (by rw [e0]; show 1 ≤ (c1.work 0).head + 1; omega)
    (by rw [e0]; exact his) (by rw [e0]; exact hos)
  have e2 := scatter1_mat_sym N bb q' wact oWoD iD iSym oSym t ht 2 (by decide)
    (Function.update rc ⟨t, ht⟩ false) ilm false
    ((singleTapeSim N).trace 1 (fun _ => bb) ((singleTapeSim N).trace 1 (fun _ => bb) c1))
    (by rw [e1]; simp only [advanceSweep, Fin.isValue, Fin.reduceEq, Fin.reduceAdd, ↓reduceIte])
    (by rw [e1, e0]; simp only [Tape.read];
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hb2)
    (by rw [e1, e0]; show 1 ≤ (c1.work 0).head + 1 + 1; omega)
    (by rw [e1, e0]; exact his) (by rw [e1, e0]; exact hos)
  rw [trace_three, e2, e1, e0]
  simp only [advanceSweep, Fin.isValue, ↓reduceIte]

/-- SCATTER sweep-1 **no-head slot-0** step: at a head-bit cell with no head
    (`wH = zero`) and no incoming carry (`rc t = false`), write `zero` (preserving
    the cell) and advance to slot 1. The common case for tapes without a head in
    this block. -/
theorem scatter1_nohead_slot0 {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (j : ℕ) (hj : j < k) (rc ilm : Fin k → Bool) (mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, false, mat))
    (hz : (c1.work 0).read = Γ.zero) (hrc : rc ⟨j, hj⟩ = false)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.scatter1
          (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 1), rc, ilm, false, mat),
        input := c1.input,
        work := fun _ => { c1.work 0 with head := (c1.work 0).head + 1 },
        output := c1.output } := by
  rw [scatter1_trace1 N
    (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, false, mat) bb c1 hst]
  simp only [scatter1Step, hz, reduceCtorEq, ↓reduceIte, advanceSweep, Fin.reduceEq, Fin.reduceAdd,
    dif_pos hj, hrc, Bool.false_eq_true, false_and, tape_idle_stay c1.input his,
    tape_idle_writeMove c1.output hos]
  congr 1
  funext x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  exact work_write_eq (c1.work 0) Γw.zero.toΓ hz

/-- SCATTER sweep-1 **no-head symbol** step (slot 1 or 2 with `writeFlag = false`):
    the symbol cell is preserved (`readBackWrite`) and the sweep advances. -/
theorem scatter1_nohead_sym {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (pt : Fin (k + 1)) (s : Fin 3) (hs : s ≠ 0) (rc ilm : Fin k → Bool) (mat : Bool)
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (pt, s), rc, ilm, false, mat))
    (hwb : (c1.work 0).read ≠ Γ.blank) (hws : (c1.work 0).read ≠ Γ.start)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.scatter1
          (q', wact, oWoD, iD, iSym, oSym, advanceSweep k (pt, s), rc, ilm, false, mat),
        input := c1.input,
        work := fun _ => { c1.work 0 with head := (c1.work 0).head + 1 },
        output := c1.output } := by
  rw [scatter1_trace1 N (q', wact, oWoD, iD, iSym, oSym, (pt, s), rc, ilm, false, mat) bb c1 hst]
  simp only [scatter1Step, hwb, hs, ↓reduceIte, Bool.false_eq_true, ite_self,
    tape_idle_stay c1.input his, tape_idle_writeMove c1.output hos]
  congr 1
  funext x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  exact work_gather_step (c1.work 0) hws

/-- SCATTER sweep-1 **no-head triple** (`trace 3`): a tape with no head in this
    block (head-bit `zero`) and no incoming carry (`rc = false`) is passed through
    untouched — its three cells are preserved and the sweep advances to the next
    tape, carries/markers unchanged. The common per-tape case in a block. -/
theorem scatter1_nohead_triple {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (j : ℕ) (hj : j < k) (rc ilm : Fin k → Bool) (mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, false, mat))
    (hrc : rc ⟨j, hj⟩ = false)
    (hz0 : (c1.work 0).cells ((c1.work 0).head) = Γ.zero)
    (hb1 : (c1.work 0).cells ((c1.work 0).head + 1) ≠ Γ.blank)
    (hb2 : (c1.work 0).cells ((c1.work 0).head + 2) ≠ Γ.blank)
    (hs1 : (c1.work 0).cells ((c1.work 0).head + 1) ≠ Γ.start)
    (hs2 : (c1.work 0).cells ((c1.work 0).head + 2) ≠ Γ.start)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 3 (fun _ => bb) c1 =
      { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
          (⟨if j + 1 < k then j + 1 else 0, by split <;> omega⟩, 0), rc, ilm, false, mat),
        input := c1.input,
        work := fun _ => { c1.work 0 with head := (c1.work 0).head + 3 },
        output := c1.output } := by
  have e0 := scatter1_nohead_slot0 N bb q' wact oWoD iD iSym oSym j hj rc ilm mat c1 hst
    (by rw [Tape.read]; exact hz0) hrc his hos
  have e1 := scatter1_nohead_sym N bb q' wact oWoD iD iSym oSym ⟨j, by omega⟩ 1 (by decide)
    rc ilm mat ((singleTapeSim N).trace 1 (fun _ => bb) c1)
    (by rw [e0]) (by rw [e0]; exact hb1) (by rw [e0]; exact hs1)
    (by rw [e0]; exact his) (by rw [e0]; exact hos)
  have e2 := scatter1_nohead_sym N bb q' wact oWoD iD iSym oSym ⟨j, by omega⟩ 2 (by decide)
    rc ilm mat ((singleTapeSim N).trace 1 (fun _ => bb) ((singleTapeSim N).trace 1 (fun _ => bb) c1))
    (by rw [e1]; simp only [advanceSweep, Fin.reduceEq, Fin.reduceAdd, ↓reduceIte])
    (by rw [e1, e0]; exact hb2) (by rw [e1, e0]; exact hs2)
    (by rw [e1, e0]; exact his) (by rw [e1, e0]; exact hos)
  rw [trace_three, e2, e1, e0]
  simp only [advanceSweep, ↓reduceIte]

/-- SCATTER sweep-1 **head slot-0, stay** step: at a head-bit cell with a head
    (`wH = one`) whose `δ` action is `stay`, keep the bit (`one`, preserving the
    cell), set `writeFlag` (so the symbol cells get the new symbol), advance. -/
theorem scatter1_head_slot0_stay {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (j : ℕ) (hj : j < k) (rc ilm : Fin k → Bool) (wf mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, wf, mat))
    (hone : (c1.work 0).read = Γ.one) (hstay : (wact ⟨j, hj⟩).2 = Dir3.stay)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.scatter1
          (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 1), rc, ilm, true, mat),
        input := c1.input,
        work := fun _ => { c1.work 0 with head := (c1.work 0).head + 1 },
        output := c1.output } := by
  rw [scatter1_trace1 N
    (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, wf, mat) bb c1 hst]
  simp only [scatter1Step, hone, reduceCtorEq, ↓reduceIte, advanceSweep, Fin.reduceEq,
    Fin.reduceAdd, dif_pos hj, hstay, tape_idle_stay c1.input his,
    tape_idle_writeMove c1.output hos]
  congr 1
  funext x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  exact work_write_eq (c1.work 0) Γw.one.toΓ hone

/-- SCATTER sweep-1 **head slot-0, left** step: a head whose `δ` action is `left`
    keeps its bit here for now (`one`, cell preserved) and is recorded in
    `isLeftMover` (sweep-2 moves it one block left); `writeFlag` is set, advance. -/
theorem scatter1_head_slot0_left {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (j : ℕ) (hj : j < k) (rc ilm : Fin k → Bool) (wf mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, wf, mat))
    (hone : (c1.work 0).read = Γ.one) (hleft : (wact ⟨j, hj⟩).2 = Dir3.left)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 1), rc,
          Function.update ilm ⟨j, hj⟩ true, true, mat),
        input := c1.input,
        work := fun _ => { c1.work 0 with head := (c1.work 0).head + 1 },
        output := c1.output } := by
  rw [scatter1_trace1 N
    (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, wf, mat) bb c1 hst]
  simp only [scatter1Step, hone, reduceCtorEq, ↓reduceIte, advanceSweep, Fin.reduceEq,
    Fin.reduceAdd, dif_pos hj, hleft, tape_idle_stay c1.input his,
    tape_idle_writeMove c1.output hos]
  congr 1
  funext x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  exact work_write_eq (c1.work 0) Γw.one.toΓ hone

/-- SCATTER sweep-1 **head slot-0, right** step: a head whose `δ` action is `right`
    leaves this cell (`zero` — the bit is cleared, changing the cell), carries the
    head one block right via `rightCarry`, sets `writeFlag`, and advances. -/
theorem scatter1_head_slot0_right {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (j : ℕ) (hj : j < k) (rc ilm : Fin k → Bool) (wf mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, wf, mat))
    (hone : (c1.work 0).read = Γ.one) (hright : (wact ⟨j, hj⟩).2 = Dir3.right)
    (hh : 1 ≤ (c1.work 0).head)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 1),
          Function.update rc ⟨j, hj⟩ true, ilm, true, mat),
        input := c1.input,
        work := fun _ => ⟨(c1.work 0).head + 1,
          Function.update (c1.work 0).cells (c1.work 0).head Γw.zero.toΓ⟩,
        output := c1.output } := by
  rw [scatter1_trace1 N
    (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, wf, mat) bb c1 hst]
  simp only [scatter1Step, hone, reduceCtorEq, ↓reduceIte, advanceSweep, Fin.reduceEq,
    Fin.reduceAdd, dif_pos hj, hright, tape_idle_stay c1.input his,
    tape_idle_writeMove c1.output hos]
  congr 1
  funext x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  exact work_write_right (c1.work 0) Γw.zero.toΓ hh

/-- SCATTER sweep-1 **head sym-hi** step (slot 1, `writeFlag = true`): overwrite the
    high symbol cell with the new symbol's high bit; `writeFlag` stays set. -/
theorem scatter1_head_sym1 {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (j : ℕ) (hj : j < k) (rc ilm : Fin k → Bool) (mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 1), rc, ilm, true, mat))
    (hwb : (c1.work 0).read ≠ Γ.blank) (hh : 1 ≤ (c1.work 0).head)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.scatter1
          (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 2), rc, ilm, true, mat),
        input := c1.input,
        work := fun _ => ⟨(c1.work 0).head + 1, Function.update (c1.work 0).cells
          (c1.work 0).head (encSymW (wact ⟨j, hj⟩).1).1.toΓ⟩,
        output := c1.output } := by
  rw [scatter1_trace1 N
    (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 1), rc, ilm, true, mat) bb c1 hst]
  simp only [scatter1Step, hwb, ↓reduceIte, advanceSweep, Fin.reduceEq, Fin.reduceAdd,
    dif_pos hj, tape_idle_stay c1.input his, tape_idle_writeMove c1.output hos]
  congr 1
  funext x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  exact work_write_right (c1.work 0) (encSymW (wact ⟨j, hj⟩).1).1.toΓ hh

/-- SCATTER sweep-1 **head sym-lo** step (slot 2, `writeFlag = true`): overwrite the
    low symbol cell with the new symbol's low bit; `writeFlag` is reset, advancing
    to the next tape. -/
theorem scatter1_head_sym2 {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (j : ℕ) (hj : j < k) (rc ilm : Fin k → Bool) (mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 2), rc, ilm, true, mat))
    (hwb : (c1.work 0).read ≠ Γ.blank) (hh : 1 ≤ (c1.work 0).head)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
          (⟨if j + 1 < k then j + 1 else 0, by split <;> omega⟩, 0), rc, ilm, false, mat),
        input := c1.input,
        work := fun _ => ⟨(c1.work 0).head + 1, Function.update (c1.work 0).cells
          (c1.work 0).head (encSymW (wact ⟨j, hj⟩).1).2.toΓ⟩,
        output := c1.output } := by
  rw [scatter1_trace1 N
    (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 2), rc, ilm, true, mat) bb c1 hst]
  simp only [scatter1Step, hwb, ↓reduceIte, advanceSweep, Fin.reduceEq,
    dif_pos hj, tape_idle_stay c1.input his, tape_idle_writeMove c1.output hos]
  congr 1
  funext x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  exact work_write_right (c1.work 0) (encSymW (wact ⟨j, hj⟩).1).2.toΓ hh

/-- SCATTER sweep-1 **head stay triple** (`trace 3`): a tape whose head is in this
    block (head-bit `one`) and stays put writes its new symbol into the two symbol
    cells, keeps its head-bit, and advances; carries/markers unchanged. -/
theorem scatter1_head_stay_triple {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (j : ℕ) (hj : j < k) (rc ilm : Fin k → Bool) (mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, false, mat))
    (hone : (c1.work 0).cells ((c1.work 0).head) = Γ.one)
    (hstay : (wact ⟨j, hj⟩).2 = Dir3.stay) (hh : 1 ≤ (c1.work 0).head)
    (hb1 : (c1.work 0).cells ((c1.work 0).head + 1) ≠ Γ.blank)
    (hb2 : (c1.work 0).cells ((c1.work 0).head + 2) ≠ Γ.blank)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 3 (fun _ => bb) c1 =
      { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
          (⟨if j + 1 < k then j + 1 else 0, by split <;> omega⟩, 0), rc, ilm, false, mat),
        input := c1.input,
        work := fun _ => ⟨(c1.work 0).head + 3,
          Function.update (Function.update (c1.work 0).cells
            ((c1.work 0).head + 1) (encSymW (wact ⟨j, hj⟩).1).1.toΓ)
            ((c1.work 0).head + 2) (encSymW (wact ⟨j, hj⟩).1).2.toΓ⟩,
        output := c1.output } := by
  have e0 := scatter1_head_slot0_stay N bb q' wact oWoD iD iSym oSym j hj rc ilm false mat c1 hst
    (by rw [Tape.read]; exact hone) hstay his hos
  have e1 := scatter1_head_sym1 N bb q' wact oWoD iD iSym oSym j hj rc ilm mat
    ((singleTapeSim N).trace 1 (fun _ => bb) c1) (by rw [e0])
    (by rw [e0]; exact hb1) (by rw [e0]; show 1 ≤ (c1.work 0).head + 1; omega)
    (by rw [e0]; exact his) (by rw [e0]; exact hos)
  have e2 := scatter1_head_sym2 N bb q' wact oWoD iD iSym oSym j hj rc ilm mat
    ((singleTapeSim N).trace 1 (fun _ => bb) ((singleTapeSim N).trace 1 (fun _ => bb) c1))
    (by rw [e1])
    (by rw [e1, e0]; simp only [Tape.read]; rw [Function.update_of_ne (by omega)]; exact hb2)
    (by rw [e1, e0]; show 1 ≤ (c1.work 0).head + 1 + 1; omega)
    (by rw [e1, e0]; exact his) (by rw [e1, e0]; exact hos)
  rw [trace_three, e2, e1, e0]

/-- SCATTER sweep-1 **head left triple** (`trace 3`): like the stay triple (writes
    the new symbol, keeps the head-bit here), but records the tape in `isLeftMover`
    so sweep-2 will move its bit one block left. -/
theorem scatter1_head_left_triple {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (j : ℕ) (hj : j < k) (rc ilm : Fin k → Bool) (mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, false, mat))
    (hone : (c1.work 0).cells ((c1.work 0).head) = Γ.one)
    (hleft : (wact ⟨j, hj⟩).2 = Dir3.left) (hh : 1 ≤ (c1.work 0).head)
    (hb1 : (c1.work 0).cells ((c1.work 0).head + 1) ≠ Γ.blank)
    (hb2 : (c1.work 0).cells ((c1.work 0).head + 2) ≠ Γ.blank)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 3 (fun _ => bb) c1 =
      { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
          (⟨if j + 1 < k then j + 1 else 0, by split <;> omega⟩, 0), rc,
          Function.update ilm ⟨j, hj⟩ true, false, mat),
        input := c1.input,
        work := fun _ => ⟨(c1.work 0).head + 3,
          Function.update (Function.update (c1.work 0).cells
            ((c1.work 0).head + 1) (encSymW (wact ⟨j, hj⟩).1).1.toΓ)
            ((c1.work 0).head + 2) (encSymW (wact ⟨j, hj⟩).1).2.toΓ⟩,
        output := c1.output } := by
  have e0 := scatter1_head_slot0_left N bb q' wact oWoD iD iSym oSym j hj rc ilm false mat c1 hst
    (by rw [Tape.read]; exact hone) hleft his hos
  have e1 := scatter1_head_sym1 N bb q' wact oWoD iD iSym oSym j hj rc
    (Function.update ilm ⟨j, hj⟩ true) mat ((singleTapeSim N).trace 1 (fun _ => bb) c1) (by rw [e0])
    (by rw [e0]; exact hb1) (by rw [e0]; show 1 ≤ (c1.work 0).head + 1; omega)
    (by rw [e0]; exact his) (by rw [e0]; exact hos)
  have e2 := scatter1_head_sym2 N bb q' wact oWoD iD iSym oSym j hj rc
    (Function.update ilm ⟨j, hj⟩ true) mat
    ((singleTapeSim N).trace 1 (fun _ => bb) ((singleTapeSim N).trace 1 (fun _ => bb) c1))
    (by rw [e1])
    (by rw [e1, e0]; simp only [Tape.read]; rw [Function.update_of_ne (by omega)]; exact hb2)
    (by rw [e1, e0]; show 1 ≤ (c1.work 0).head + 1 + 1; omega)
    (by rw [e1, e0]; exact his) (by rw [e1, e0]; exact hos)
  rw [trace_three, e2, e1, e0]

/-- SCATTER sweep-1 **head right triple** (`trace 3`): a head moving right clears its
    head-bit here (`zero`), writes its new symbol into the two symbol cells, and
    carries the head one block right via `rightCarry`; three cell writes total. -/
theorem scatter1_head_right_triple {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (j : ℕ) (hj : j < k) (rc ilm : Fin k → Bool) (mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, false, mat))
    (hone : (c1.work 0).cells ((c1.work 0).head) = Γ.one)
    (hright : (wact ⟨j, hj⟩).2 = Dir3.right) (hh : 1 ≤ (c1.work 0).head)
    (hb1 : (c1.work 0).cells ((c1.work 0).head + 1) ≠ Γ.blank)
    (hb2 : (c1.work 0).cells ((c1.work 0).head + 2) ≠ Γ.blank)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 3 (fun _ => bb) c1 =
      { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
          (⟨if j + 1 < k then j + 1 else 0, by split <;> omega⟩, 0),
          Function.update rc ⟨j, hj⟩ true, ilm, false, mat),
        input := c1.input,
        work := fun _ => ⟨(c1.work 0).head + 3,
          Function.update (Function.update (Function.update (c1.work 0).cells
            (c1.work 0).head Γw.zero.toΓ)
            ((c1.work 0).head + 1) (encSymW (wact ⟨j, hj⟩).1).1.toΓ)
            ((c1.work 0).head + 2) (encSymW (wact ⟨j, hj⟩).1).2.toΓ⟩,
        output := c1.output } := by
  have e0 := scatter1_head_slot0_right N bb q' wact oWoD iD iSym oSym j hj rc ilm false mat c1 hst
    (by rw [Tape.read]; exact hone) hright hh his hos
  have e1 := scatter1_head_sym1 N bb q' wact oWoD iD iSym oSym j hj (Function.update rc ⟨j, hj⟩ true)
    ilm mat ((singleTapeSim N).trace 1 (fun _ => bb) c1) (by rw [e0])
    (by rw [e0]; simp only [Tape.read]; rw [Function.update_of_ne (by omega)]; exact hb1)
    (by rw [e0]; show 1 ≤ (c1.work 0).head + 1; omega)
    (by rw [e0]; exact his) (by rw [e0]; exact hos)
  have e2 := scatter1_head_sym2 N bb q' wact oWoD iD iSym oSym j hj (Function.update rc ⟨j, hj⟩ true)
    ilm mat ((singleTapeSim N).trace 1 (fun _ => bb) ((singleTapeSim N).trace 1 (fun _ => bb) c1))
    (by rw [e1])
    (by rw [e1, e0]; simp only [Tape.read];
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hb2)
    (by rw [e1, e0]; show 1 ≤ (c1.work 0).head + 1 + 1; omega)
    (by rw [e1, e0]; exact his) (by rw [e1, e0]; exact hos)
  rw [trace_three, e2, e1, e0]

/-- SCATTER sweep-1 **deposit slot-0** step: at a head-bit cell with no head
    (`wH = zero`) but an incoming carry (`rc t = true` — a head moved right into
    this block), deposit the head-bit (write `one`, clearing the carry); the symbol
    cells are not overwritten (`writeFlag` stays false). -/
theorem scatter1_deposit_slot0 {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (j : ℕ) (hj : j < k) (rc ilm : Fin k → Bool) (mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, false, mat))
    (hz : (c1.work 0).read = Γ.zero) (hrc : rc ⟨j, hj⟩ = true) (hh : 1 ≤ (c1.work 0).head)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 1),
          Function.update rc ⟨j, hj⟩ false, ilm, false, mat),
        input := c1.input,
        work := fun _ => ⟨(c1.work 0).head + 1,
          Function.update (c1.work 0).cells (c1.work 0).head Γw.one.toΓ⟩,
        output := c1.output } := by
  rw [scatter1_trace1 N
    (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, false, mat) bb c1 hst]
  simp only [scatter1Step, hz, reduceCtorEq, ↓reduceIte, advanceSweep, Fin.reduceEq,
    Fin.reduceAdd, dif_pos hj, hrc, tape_idle_stay c1.input his,
    tape_idle_writeMove c1.output hos]
  congr 1
  funext x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  exact work_write_right (c1.work 0) Γw.one.toΓ hh

/-- SCATTER sweep-1 **deposit triple** (`trace 3`): a no-head tape with an incoming
    carry gets its head-bit deposited (write `one`), symbols preserved, carry
    cleared, advance. The right-mover landing case. -/
theorem scatter1_deposit_triple {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (j : ℕ) (hj : j < k) (rc ilm : Fin k → Bool) (mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, false, mat))
    (hz0 : (c1.work 0).cells ((c1.work 0).head) = Γ.zero)
    (hrc : rc ⟨j, hj⟩ = true) (hh : 1 ≤ (c1.work 0).head)
    (hb1 : (c1.work 0).cells ((c1.work 0).head + 1) ≠ Γ.blank)
    (hb2 : (c1.work 0).cells ((c1.work 0).head + 2) ≠ Γ.blank)
    (hs1 : (c1.work 0).cells ((c1.work 0).head + 1) ≠ Γ.start)
    (hs2 : (c1.work 0).cells ((c1.work 0).head + 2) ≠ Γ.start)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 3 (fun _ => bb) c1 =
      { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
          (⟨if j + 1 < k then j + 1 else 0, by split <;> omega⟩, 0),
          Function.update rc ⟨j, hj⟩ false, ilm, false, mat),
        input := c1.input,
        work := fun _ => ⟨(c1.work 0).head + 3,
          Function.update (c1.work 0).cells (c1.work 0).head Γw.one.toΓ⟩,
        output := c1.output } := by
  have e0 := scatter1_deposit_slot0 N bb q' wact oWoD iD iSym oSym j hj rc ilm mat c1 hst
    (by rw [Tape.read]; exact hz0) hrc hh his hos
  have e1 := scatter1_nohead_sym N bb q' wact oWoD iD iSym oSym ⟨j, by omega⟩ 1 (by decide)
    (Function.update rc ⟨j, hj⟩ false) ilm mat ((singleTapeSim N).trace 1 (fun _ => bb) c1)
    (by rw [e0])
    (by rw [e0]; simp only [Tape.read]; rw [Function.update_of_ne (by omega)]; exact hb1)
    (by rw [e0]; simp only [Tape.read]; rw [Function.update_of_ne (by omega)]; exact hs1)
    (by rw [e0]; exact his) (by rw [e0]; exact hos)
  have e2 := scatter1_nohead_sym N bb q' wact oWoD iD iSym oSym ⟨j, by omega⟩ 2 (by decide)
    (Function.update rc ⟨j, hj⟩ false) ilm mat
    ((singleTapeSim N).trace 1 (fun _ => bb) ((singleTapeSim N).trace 1 (fun _ => bb) c1))
    (by rw [e1]; simp only [advanceSweep, Fin.reduceEq, Fin.reduceAdd, ↓reduceIte])
    (by rw [e1, e0]; simp only [Tape.read]; rw [Function.update_of_ne (by omega)]; exact hb2)
    (by rw [e1, e0]; simp only [Tape.read]; rw [Function.update_of_ne (by omega)]; exact hs2)
    (by rw [e1, e0]; exact his) (by rw [e1, e0]; exact hos)
  rw [trace_three, e2, e1, e0]
  simp only [advanceSweep, ↓reduceIte]

/-- The **SCATTER sweep-1 → sweep-2 turn-around** (`trace 1`): once the freshly
    materialized block is complete (`mat`, back at tape `0` slot `0`, reading the
    `□` past it), the sweep turns leftward into sweep-2 at the last block's last
    cell. -/
theorem scatter1_turnaround {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (rightCarry isLeftMover : Fin k → Bool) (writeFlag : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (0, 0), rightCarry, isLeftMover, writeFlag, true))
    (hblank : (c1.work 0).read = Γ.blank) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.scatter2
          (q', oWoD, iD, iSym, oSym, (⟨k - 1, by omega⟩, 2), isLeftMover, fun _ => false),
        input := c1.input.move (TM.idleDir c1.input.read),
        work := fun i => (c1.work i).writeAndMove Γw.blank.toΓ Dir3.left,
        output := c1.output.writeAndMove (TM.readBackWrite c1.output.read).toΓ
          (TM.idleDir c1.output.read) } := by
  rw [scatter1_trace1 N
    (q', wact, oWoD, iD, iSym, oSym, (0, 0), rightCarry, isLeftMover, writeFlag, true) bb c1 hst]
  simp only [scatter1Step, hblank, ↓reduceIte, and_self]; rfl

/-- **SCATTER block step — no-head tape.** Tape `m` has no head in block `b`
    (`(c.work m).head ≠ b`) and no incoming carry (`¬((c.work m).head = b-1 ∧ right)`,
    so `rc m = false`): its three cells are unchanged — which already IS the
    intermediate encoding, since the head neither sits at nor moves into `b`.
    Advances the within-block invariant `b m → b (m+1)` with `rc`/`ilm` unchanged. -/
theorem scatter1_tape_nohead {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (b M : ℕ)
    (hb1 : 1 ≤ b) (hbM : b ≤ M) (m : ℕ) (hmk : m < k)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (rc ilm : Fin k → Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨m, by omega⟩, 0), rc, ilm, false, false))
    (hhead : (c1.work 0).head = headBitCell k b ⟨m, hmk⟩)
    (hbm : Scatter1BlockInv (c1.work 0) c.work wact M b m)
    (hhd : (c.work ⟨m, hmk⟩).head ≠ b)
    (hndep : ¬((c.work ⟨m, hmk⟩).head = b - 1 ∧ (wact ⟨m, hmk⟩).2 = Dir3.right))
    (hrc : rc ⟨m, hmk⟩ = decide ((c.work ⟨m, hmk⟩).head = b - 1 ∧ (wact ⟨m, hmk⟩).2 = Dir3.right))
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    ∃ wt : Tape,
      (singleTapeSim N).trace 3 (fun _ => bb) c1 =
        { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
            (⟨if m + 1 < k then m + 1 else 0, by split <;> omega⟩, 0), rc, ilm, false, false),
          input := c1.input, work := fun _ => wt, output := c1.output }
      ∧ wt.head = headBitCell k b ⟨m, hmk⟩ + 3
      ∧ Scatter1BlockInv wt c.work wact M b (m + 1) := by
  have hot := hbm.oldTape ⟨m, hmk⟩ (le_refl m)
  have hsym : symCell k b ⟨m, hmk⟩ = headBitCell k b ⟨m, hmk⟩ + 1 := by
    simp only [symCell, headBitCell]
  have hsym2 : symCell k b ⟨m, hmk⟩ + 1 = headBitCell k b ⟨m, hmk⟩ + 2 := by
    simp only [symCell, headBitCell]
  have hrcf : rc ⟨m, hmk⟩ = false := by rw [hrc]; exact decide_eq_false hndep
  have hscat : (scatterInterWork (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩)).head ≠ b := by
    rw [scatterInterWork_head]
    split_ifs with hdir
    · intro hb; exact hndep ⟨by omega, hdir⟩
    · exact hhd
  have hcb : (scatterInterWork (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩)).cells b
      = (c.work ⟨m, hmk⟩).cells b :=
    scatterInterWork_cells_of_ne (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩) (Ne.symm hhd)
  have htriple := scatter1_nohead_triple N bb q' wact oWoD iD iSym oSym m hmk rc ilm false c1 hst
    hrcf
    (by rw [hhead]; exact hot.1.trans (if_neg hhd))
    (by rw [hhead, ← hsym, hot.2.1]; exact (encSymΓ_ne_blank _).1)
    (by rw [hhead, ← hsym2, hot.2.2]; exact (encSymΓ_ne_blank _).2)
    (by rw [hhead, ← hsym, hot.2.1]; exact (encSymΓ_ne_start _).1)
    (by rw [hhead, ← hsym2, hot.2.2]; exact (encSymΓ_ne_start _).2)
    his hos
  refine ⟨{ c1.work 0 with head := (c1.work 0).head + 3 }, htriple, ?_, ?_⟩
  · show (c1.work 0).head + 3 = headBitCell k b ⟨m, hmk⟩ + 3
    rw [hhead]
  · apply scatter1_blockinv_step hb1 hbM hmk hbm
    · show (c1.work 0).cells (headBitCell k b ⟨m, hmk⟩) = _
      rw [hot.1, if_neg hhd, if_neg hscat]
    · show (c1.work 0).cells (symCell k b ⟨m, hmk⟩) = _
      rw [hcb]; exact hot.2.1
    · show (c1.work 0).cells (symCell k b ⟨m, hmk⟩ + 1) = _
      rw [hcb]; exact hot.2.2
    · intro c _ _ _; rfl

/-- **SCATTER block step — deposit (right-mover landing).** Tape `m` has no head
    in block `b` but an incoming carry: its head moved right out of `b-1`
    (`(c.work m).head = b-1 ∧ dir = right`, so `rc m = true`). The deposit writes
    the head-bit `one` at `(b,m)` (clearing the carry); symbols stay (the new
    symbol was written back at `b-1`). The intermediate head IS at `b`
    (`scatterInterWork.head = (b-1)+1 = b`). Advances `b m → b (m+1)`, clearing
    `rc m`. -/
theorem scatter1_tape_deposit {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (b M : ℕ)
    (hb1 : 1 ≤ b) (hbM : b ≤ M) (m : ℕ) (hmk : m < k)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (rc ilm : Fin k → Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨m, by omega⟩, 0), rc, ilm, false, false))
    (hhead : (c1.work 0).head = headBitCell k b ⟨m, hmk⟩)
    (hbm : Scatter1BlockInv (c1.work 0) c.work wact M b m)
    (hdep : (c.work ⟨m, hmk⟩).head = b - 1 ∧ (wact ⟨m, hmk⟩).2 = Dir3.right)
    (hrc : rc ⟨m, hmk⟩ = true)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    ∃ wt : Tape,
      (singleTapeSim N).trace 3 (fun _ => bb) c1 =
        { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
            (⟨if m + 1 < k then m + 1 else 0, by split <;> omega⟩, 0),
            Function.update rc ⟨m, hmk⟩ false, ilm, false, false),
          input := c1.input, work := fun _ => wt, output := c1.output }
      ∧ wt.head = headBitCell k b ⟨m, hmk⟩ + 3
      ∧ Scatter1BlockInv wt c.work wact M b (m + 1) := by
  obtain ⟨hdh, hdr⟩ := hdep
  have hhd : (c.work ⟨m, hmk⟩).head ≠ b := by omega
  have hot := hbm.oldTape ⟨m, hmk⟩ (le_refl m)
  have hsym : symCell k b ⟨m, hmk⟩ = headBitCell k b ⟨m, hmk⟩ + 1 := by
    simp only [symCell, headBitCell]
  have hsym2 : symCell k b ⟨m, hmk⟩ + 1 = headBitCell k b ⟨m, hmk⟩ + 2 := by
    simp only [symCell, headBitCell]
  have hh1 : 1 ≤ (c1.work 0).head := by
    rw [hhead]; simp only [headBitCell]; have := one_le_blockStart k b; omega
  have hscat : (scatterInterWork (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩)).head = b := by
    rw [scatterInterWork_head, if_pos hdr]; omega
  have hcb : (scatterInterWork (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩)).cells b
      = (c.work ⟨m, hmk⟩).cells b :=
    scatterInterWork_cells_of_ne (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩) (Ne.symm hhd)
  have htriple := scatter1_deposit_triple N bb q' wact oWoD iD iSym oSym m hmk rc ilm false c1 hst
    (by rw [hhead]; exact hot.1.trans (if_neg hhd))
    hrc hh1
    (by rw [hhead, ← hsym, hot.2.1]; exact (encSymΓ_ne_blank _).1)
    (by rw [hhead, ← hsym2, hot.2.2]; exact (encSymΓ_ne_blank _).2)
    (by rw [hhead, ← hsym, hot.2.1]; exact (encSymΓ_ne_start _).1)
    (by rw [hhead, ← hsym2, hot.2.2]; exact (encSymΓ_ne_start _).2)
    his hos
  refine ⟨⟨(c1.work 0).head + 3,
      Function.update (c1.work 0).cells (c1.work 0).head Γw.one.toΓ⟩, htriple, ?_, ?_⟩
  · show (c1.work 0).head + 3 = headBitCell k b ⟨m, hmk⟩ + 3
    rw [hhead]
  · apply scatter1_blockinv_step hb1 hbM hmk hbm
    · show Function.update (c1.work 0).cells (c1.work 0).head Γw.one.toΓ
        (headBitCell k b ⟨m, hmk⟩) = _
      rw [← hhead, Function.update_self, if_pos hscat]; rfl
    · show Function.update (c1.work 0).cells (c1.work 0).head Γw.one.toΓ
        (symCell k b ⟨m, hmk⟩) = _
      rw [Function.update_of_ne (by rw [hhead]; simp only [symCell, headBitCell]; omega), hcb]
      exact hot.2.1
    · show Function.update (c1.work 0).cells (c1.work 0).head Γw.one.toΓ
        (symCell k b ⟨m, hmk⟩ + 1) = _
      rw [Function.update_of_ne (by rw [hhead]; simp only [symCell, headBitCell]; omega), hcb]
      exact hot.2.2
    · intro c hc _ _
      show Function.update (c1.work 0).cells (c1.work 0).head Γw.one.toΓ c = (c1.work 0).cells c
      rw [Function.update_of_ne (by rw [hhead]; exact hc)]

/-- **SCATTER block step — head, stay.** Tape `m` has its head at block `b`
    (`(c.work m).head = b`) with `δ`-action `stay`: keep the head-bit `one`, write
    the new symbol into the two symbol cells. The intermediate head stays at `b`
    (`scatterInterWork.head = b`, since `stay ≠ right`) and the intermediate symbol
    at `b` is the new write (`scatterInterWork.cells b = (wact m).1`, via
    `cells_at_head`), matched to the triple's `encSymW` writes by the codec bridge.
    Advances `b m → b (m+1)`, `rc`/`ilm` unchanged. -/
theorem scatter1_tape_head_stay {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (b M : ℕ)
    (hb1 : 1 ≤ b) (hbM : b ≤ M) (m : ℕ) (hmk : m < k)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (rc ilm : Fin k → Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨m, by omega⟩, 0), rc, ilm, false, false))
    (hhead : (c1.work 0).head = headBitCell k b ⟨m, hmk⟩)
    (hbm : Scatter1BlockInv (c1.work 0) c.work wact M b m)
    (hhdb : (c.work ⟨m, hmk⟩).head = b) (hstay : (wact ⟨m, hmk⟩).2 = Dir3.stay)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    ∃ wt : Tape,
      (singleTapeSim N).trace 3 (fun _ => bb) c1 =
        { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
            (⟨if m + 1 < k then m + 1 else 0, by split <;> omega⟩, 0), rc, ilm, false, false),
          input := c1.input, work := fun _ => wt, output := c1.output }
      ∧ wt.head = headBitCell k b ⟨m, hmk⟩ + 3
      ∧ Scatter1BlockInv wt c.work wact M b (m + 1) := by
  have hot := hbm.oldTape ⟨m, hmk⟩ (le_refl m)
  have hsym : symCell k b ⟨m, hmk⟩ = headBitCell k b ⟨m, hmk⟩ + 1 := by
    simp only [symCell, headBitCell]
  have hsym2 : symCell k b ⟨m, hmk⟩ + 1 = headBitCell k b ⟨m, hmk⟩ + 2 := by
    simp only [symCell, headBitCell]
  have hh1 : 1 ≤ (c1.work 0).head := by
    rw [hhead]; simp only [headBitCell]; have := one_le_blockStart k b; omega
  have hscat : (scatterInterWork (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩)).head = b := by
    rw [scatterInterWork_head, if_neg (show ¬ (wact ⟨m, hmk⟩).2 = Dir3.right by rw [hstay]; decide)]
    exact hhdb
  have hcbh : (scatterInterWork (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩)).cells b = (wact ⟨m, hmk⟩).1.toΓ := by
    rw [← hhdb]; exact scatterInterWork_cells_at_head (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩) (by omega)
  have htriple := scatter1_head_stay_triple N bb q' wact oWoD iD iSym oSym m hmk rc ilm false c1 hst
    (by rw [hhead]; exact hot.1.trans (if_pos hhdb))
    hstay hh1
    (by rw [hhead, ← hsym, hot.2.1]; exact (encSymΓ_ne_blank _).1)
    (by rw [hhead, ← hsym2, hot.2.2]; exact (encSymΓ_ne_blank _).2)
    his hos
  refine ⟨⟨(c1.work 0).head + 3,
      Function.update (Function.update (c1.work 0).cells
        ((c1.work 0).head + 1) (encSymW (wact ⟨m, hmk⟩).1).1.toΓ)
        ((c1.work 0).head + 2) (encSymW (wact ⟨m, hmk⟩).1).2.toΓ⟩, htriple, ?_, ?_⟩
  · show (c1.work 0).head + 3 = headBitCell k b ⟨m, hmk⟩ + 3
    rw [hhead]
  · apply scatter1_blockinv_step hb1 hbM hmk hbm
    · show Function.update (Function.update (c1.work 0).cells _ _) _ _ (headBitCell k b ⟨m, hmk⟩) = _
      rw [Function.update_of_ne (by rw [hhead]; omega), Function.update_of_ne (by rw [hhead]; omega),
          hot.1, if_pos hhdb, if_pos hscat]
    · show Function.update (Function.update (c1.work 0).cells _ _) _ _ (symCell k b ⟨m, hmk⟩) = _
      rw [show symCell k b ⟨m, hmk⟩ = (c1.work 0).head + 1 by rw [hsym, hhead],
          Function.update_of_ne (by omega), Function.update_self, hcbh]
      exact (encSymW_toΓ_eq_encSymΓ _).1
    · show Function.update (Function.update (c1.work 0).cells _ _) _ _ (symCell k b ⟨m, hmk⟩ + 1) = _
      rw [show symCell k b ⟨m, hmk⟩ + 1 = (c1.work 0).head + 2 by rw [hsym2, hhead],
          Function.update_self, hcbh]
      exact (encSymW_toΓ_eq_encSymΓ _).2
    · intro c _ hc2 hc3
      show Function.update (Function.update (c1.work 0).cells _ _) _ _ c = (c1.work 0).cells c
      rw [Function.update_of_ne (show c ≠ (c1.work 0).head + 2 by rw [hhead, ← hsym2]; exact hc3),
          Function.update_of_ne (show c ≠ (c1.work 0).head + 1 by rw [hhead, ← hsym]; exact hc2)]

/-- **SCATTER block step — head, left.** Like `head_stay` (head-bit kept `one`,
    new symbol written) but the `δ`-action is `left`: the tape is recorded in
    `isLeftMover` (sweep-2 moves its bit one block left later). The intermediate
    head still sits at `b` (`scatterInterWork.head = b`, since `left ≠ right`), so
    the SCATTER-1 target is unchanged from stay; only `ilm` advances. -/
theorem scatter1_tape_head_left {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (b M : ℕ)
    (hb1 : 1 ≤ b) (hbM : b ≤ M) (m : ℕ) (hmk : m < k)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (rc ilm : Fin k → Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨m, by omega⟩, 0), rc, ilm, false, false))
    (hhead : (c1.work 0).head = headBitCell k b ⟨m, hmk⟩)
    (hbm : Scatter1BlockInv (c1.work 0) c.work wact M b m)
    (hhdb : (c.work ⟨m, hmk⟩).head = b) (hleft : (wact ⟨m, hmk⟩).2 = Dir3.left)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    ∃ wt : Tape,
      (singleTapeSim N).trace 3 (fun _ => bb) c1 =
        { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
            (⟨if m + 1 < k then m + 1 else 0, by split <;> omega⟩, 0), rc,
            Function.update ilm ⟨m, hmk⟩ true, false, false),
          input := c1.input, work := fun _ => wt, output := c1.output }
      ∧ wt.head = headBitCell k b ⟨m, hmk⟩ + 3
      ∧ Scatter1BlockInv wt c.work wact M b (m + 1) := by
  have hot := hbm.oldTape ⟨m, hmk⟩ (le_refl m)
  have hsym : symCell k b ⟨m, hmk⟩ = headBitCell k b ⟨m, hmk⟩ + 1 := by
    simp only [symCell, headBitCell]
  have hsym2 : symCell k b ⟨m, hmk⟩ + 1 = headBitCell k b ⟨m, hmk⟩ + 2 := by
    simp only [symCell, headBitCell]
  have hh1 : 1 ≤ (c1.work 0).head := by
    rw [hhead]; simp only [headBitCell]; have := one_le_blockStart k b; omega
  have hscat : (scatterInterWork (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩)).head = b := by
    rw [scatterInterWork_head, if_neg (show ¬ (wact ⟨m, hmk⟩).2 = Dir3.right by rw [hleft]; decide)]
    exact hhdb
  have hcbh : (scatterInterWork (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩)).cells b = (wact ⟨m, hmk⟩).1.toΓ := by
    rw [← hhdb]; exact scatterInterWork_cells_at_head (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩) (by omega)
  have htriple := scatter1_head_left_triple N bb q' wact oWoD iD iSym oSym m hmk rc ilm false c1 hst
    (by rw [hhead]; exact hot.1.trans (if_pos hhdb))
    hleft hh1
    (by rw [hhead, ← hsym, hot.2.1]; exact (encSymΓ_ne_blank _).1)
    (by rw [hhead, ← hsym2, hot.2.2]; exact (encSymΓ_ne_blank _).2)
    his hos
  refine ⟨⟨(c1.work 0).head + 3,
      Function.update (Function.update (c1.work 0).cells
        ((c1.work 0).head + 1) (encSymW (wact ⟨m, hmk⟩).1).1.toΓ)
        ((c1.work 0).head + 2) (encSymW (wact ⟨m, hmk⟩).1).2.toΓ⟩, htriple, ?_, ?_⟩
  · show (c1.work 0).head + 3 = headBitCell k b ⟨m, hmk⟩ + 3
    rw [hhead]
  · apply scatter1_blockinv_step hb1 hbM hmk hbm
    · show Function.update (Function.update (c1.work 0).cells _ _) _ _ (headBitCell k b ⟨m, hmk⟩) = _
      rw [Function.update_of_ne (by rw [hhead]; omega), Function.update_of_ne (by rw [hhead]; omega),
          hot.1, if_pos hhdb, if_pos hscat]
    · show Function.update (Function.update (c1.work 0).cells _ _) _ _ (symCell k b ⟨m, hmk⟩) = _
      rw [show symCell k b ⟨m, hmk⟩ = (c1.work 0).head + 1 by rw [hsym, hhead],
          Function.update_of_ne (by omega), Function.update_self, hcbh]
      exact (encSymW_toΓ_eq_encSymΓ _).1
    · show Function.update (Function.update (c1.work 0).cells _ _) _ _ (symCell k b ⟨m, hmk⟩ + 1) = _
      rw [show symCell k b ⟨m, hmk⟩ + 1 = (c1.work 0).head + 2 by rw [hsym2, hhead],
          Function.update_self, hcbh]
      exact (encSymW_toΓ_eq_encSymΓ _).2
    · intro c _ hc2 hc3
      show Function.update (Function.update (c1.work 0).cells _ _) _ _ c = (c1.work 0).cells c
      rw [Function.update_of_ne (show c ≠ (c1.work 0).head + 2 by rw [hhead, ← hsym2]; exact hc3),
          Function.update_of_ne (show c ≠ (c1.work 0).head + 1 by rw [hhead, ← hsym]; exact hc2)]

/-- **SCATTER block step — head, right.** Tape `m`'s head at `b` moving right:
    clears the head-bit here (`zero`), writes the new symbol, carries the head one
    block right via `rc`. The intermediate head moves to `b+1`
    (`scatterInterWork.head = b+1 ≠ b`), so the cleared `zero` matches; the new
    symbol at `b` (the old head's cell) matches via the codec bridge. Advances
    `b m → b (m+1)`, setting `rc m`. -/
theorem scatter1_tape_head_right {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (b M : ℕ)
    (hb1 : 1 ≤ b) (hbM : b ≤ M) (m : ℕ) (hmk : m < k)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (rc ilm : Fin k → Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨m, by omega⟩, 0), rc, ilm, false, false))
    (hhead : (c1.work 0).head = headBitCell k b ⟨m, hmk⟩)
    (hbm : Scatter1BlockInv (c1.work 0) c.work wact M b m)
    (hhdb : (c.work ⟨m, hmk⟩).head = b) (hright : (wact ⟨m, hmk⟩).2 = Dir3.right)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    ∃ wt : Tape,
      (singleTapeSim N).trace 3 (fun _ => bb) c1 =
        { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
            (⟨if m + 1 < k then m + 1 else 0, by split <;> omega⟩, 0),
            Function.update rc ⟨m, hmk⟩ true, ilm, false, false),
          input := c1.input, work := fun _ => wt, output := c1.output }
      ∧ wt.head = headBitCell k b ⟨m, hmk⟩ + 3
      ∧ Scatter1BlockInv wt c.work wact M b (m + 1) := by
  have hot := hbm.oldTape ⟨m, hmk⟩ (le_refl m)
  have hsym : symCell k b ⟨m, hmk⟩ = headBitCell k b ⟨m, hmk⟩ + 1 := by
    simp only [symCell, headBitCell]
  have hsym2 : symCell k b ⟨m, hmk⟩ + 1 = headBitCell k b ⟨m, hmk⟩ + 2 := by
    simp only [symCell, headBitCell]
  have hh1 : 1 ≤ (c1.work 0).head := by
    rw [hhead]; simp only [headBitCell]; have := one_le_blockStart k b; omega
  have hscat : (scatterInterWork (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩)).head ≠ b := by
    rw [scatterInterWork_head, if_pos hright]; omega
  have hcbh : (scatterInterWork (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩)).cells b = (wact ⟨m, hmk⟩).1.toΓ := by
    rw [← hhdb]; exact scatterInterWork_cells_at_head (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩) (by omega)
  have htriple := scatter1_head_right_triple N bb q' wact oWoD iD iSym oSym m hmk rc ilm false c1 hst
    (by rw [hhead]; exact hot.1.trans (if_pos hhdb))
    hright hh1
    (by rw [hhead, ← hsym, hot.2.1]; exact (encSymΓ_ne_blank _).1)
    (by rw [hhead, ← hsym2, hot.2.2]; exact (encSymΓ_ne_blank _).2)
    his hos
  refine ⟨⟨(c1.work 0).head + 3,
      Function.update (Function.update (Function.update (c1.work 0).cells
        (c1.work 0).head Γw.zero.toΓ)
        ((c1.work 0).head + 1) (encSymW (wact ⟨m, hmk⟩).1).1.toΓ)
        ((c1.work 0).head + 2) (encSymW (wact ⟨m, hmk⟩).1).2.toΓ⟩, htriple, ?_, ?_⟩
  · show (c1.work 0).head + 3 = headBitCell k b ⟨m, hmk⟩ + 3
    rw [hhead]
  · apply scatter1_blockinv_step hb1 hbM hmk hbm
    · show Function.update (Function.update (Function.update (c1.work 0).cells _ _) _ _) _ _
        (headBitCell k b ⟨m, hmk⟩) = _
      rw [Function.update_of_ne (by rw [hhead]; omega), Function.update_of_ne (by rw [hhead]; omega),
          ← hhead, Function.update_self, if_neg hscat]; rfl
    · show Function.update (Function.update (Function.update (c1.work 0).cells _ _) _ _) _ _
        (symCell k b ⟨m, hmk⟩) = _
      rw [show symCell k b ⟨m, hmk⟩ = (c1.work 0).head + 1 by rw [hsym, hhead],
          Function.update_of_ne (by omega), Function.update_self, hcbh]
      exact (encSymW_toΓ_eq_encSymΓ _).1
    · show Function.update (Function.update (Function.update (c1.work 0).cells _ _) _ _) _ _
        (symCell k b ⟨m, hmk⟩ + 1) = _
      rw [show symCell k b ⟨m, hmk⟩ + 1 = (c1.work 0).head + 2 by rw [hsym2, hhead],
          Function.update_self, hcbh]
      exact (encSymW_toΓ_eq_encSymΓ _).2
    · intro c hc1 hc2 hc3
      show Function.update (Function.update (Function.update (c1.work 0).cells _ _) _ _) _ _ c
        = (c1.work 0).cells c
      rw [Function.update_of_ne (show c ≠ (c1.work 0).head + 2 by rw [hhead, ← hsym2]; exact hc3),
          Function.update_of_ne (show c ≠ (c1.work 0).head + 1 by rw [hhead, ← hsym]; exact hc2),
          Function.update_of_ne (show c ≠ (c1.work 0).head by rw [hhead]; exact hc1)]

/-- **SCATTER block sweep (`trace (3*m)`).** Sweeping the first `m ≤ k` tapes of
    block `b` (from tape `0`, slot `0`, work head `blockStart k b`, incoming carry
    `rc_in j = decide((c.work j).head = b-1 ∧ right)`): after `m` tapes the head is
    at `blockStart k b + 3*m`, the sweep is back at slot `0` (tape `m mod k`), the
    tape's first `m` tapes of block `b` are intermediate-encoded (`Scatter1BlockInv
    … b m`), and `rc`/`ilm` are threaded — `rc` records the right-movers of the
    first `m` tapes, `ilm` the left-movers. Proved by induction on `m`, each step
    one of the five per-tape block-step lemmas selected by the old head-bit and
    `rc`. -/
theorem scatter1_block_aux {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (b M : ℕ)
    (hb1 : 1 ≤ b) (hbM : b ≤ M)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (rc_in ilm_in : Fin k → Bool)
    (hrc_in : ∀ j : Fin k, rc_in j = decide ((c.work j).head = b - 1 ∧ (wact j).2 = Dir3.right))
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨0, by omega⟩, 0), rc_in, ilm_in, false, false))
    (hhead : (c1.work 0).head = blockStart k b)
    (hbm : Scatter1BlockInv (c1.work 0) c.work wact M b 0)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start)
    (m : ℕ) (hm : m ≤ k) :
    ∃ wt : Tape,
      (singleTapeSim N).trace (3 * m) (fun _ => bb) c1 =
        { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
            (⟨if m < k then m else 0, by split <;> omega⟩, 0),
            (fun (j : Fin k) => if (j : ℕ) < m then
                decide ((c.work j).head = b ∧ (wact j).2 = Dir3.right) else rc_in j),
            (fun (j : Fin k) => if (j : ℕ) < m ∧ (c.work j).head = b ∧ (wact j).2 = Dir3.left then
                true else ilm_in j),
            false, false),
          input := c1.input, work := fun _ => wt, output := c1.output }
      ∧ wt.head = blockStart k b + 3 * m
      ∧ Scatter1BlockInv wt c.work wact M b m := by
  induction m with
  | zero =>
    refine ⟨c1.work 0, ?_, ?_, hbm⟩
    · have h0 : (singleTapeSim N).trace (3 * 0) (fun _ => bb) c1 = c1 := by
        simp only [Nat.mul_zero]; rfl
      rw [h0]
      obtain ⟨cst, cin, cwk, cout⟩ := c1
      simp only [Nat.not_lt_zero, ↓reduceIte, false_and] at hst ⊢
      subst hst
      refine (Cfg.mk.injEq ..).mpr ⟨?_, rfl, ?_, rfl⟩
      · split <;> rfl
      · funext x
        obtain rfl : x = 0 := Subsingleton.elim x 0
        rfl
    · simp only [Nat.mul_zero, Nat.add_zero]; exact hhead
  | succ m ih =>
    obtain ⟨wtm, htm, hwhm, hbim⟩ := ih (by omega)
    have hmk : m < k := by omega
    -- the threaded rc/ilm at m (what the IH config carries)
    set RCm := (fun (j : Fin k) => if (j : ℕ) < m then
        decide ((c.work j).head = b ∧ (wact j).2 = Dir3.right) else rc_in j) with hRCm
    set ILMm := (fun (j : Fin k) => if (j : ℕ) < m ∧ (c.work j).head = b ∧ (wact j).2 = Dir3.left then
        true else ilm_in j) with hILMm
    -- structural step: the m+1 closed forms are single-slot updates of the m forms
    have hstep_rc : (fun (j : Fin k) => if (j : ℕ) < m + 1 then
          decide ((c.work j).head = b ∧ (wact j).2 = Dir3.right) else rc_in j)
        = Function.update RCm ⟨m, hmk⟩
            (decide ((c.work ⟨m, hmk⟩).head = b ∧ (wact ⟨m, hmk⟩).2 = Dir3.right)) := by
      funext j
      by_cases hj : j = ⟨m, hmk⟩
      · subst hj; rw [Function.update_self]; simp only [Nat.lt_succ_self, if_true]
      · rw [Function.update_of_ne hj, hRCm]
        have hjm : (j : ℕ) ≠ m := fun h => hj (Fin.ext h)
        by_cases hlt : (j : ℕ) < m
        · simp only [if_pos hlt, if_pos (show (j : ℕ) < m + 1 by omega)]
        · simp only [if_neg hlt, if_neg (show ¬ (j : ℕ) < m + 1 by omega)]
    have hstep_ilm : (fun (j : Fin k) => if (j : ℕ) < m + 1 ∧ (c.work j).head = b ∧ (wact j).2 = Dir3.left then
          true else ilm_in j)
        = Function.update ILMm ⟨m, hmk⟩
            (if (c.work ⟨m, hmk⟩).head = b ∧ (wact ⟨m, hmk⟩).2 = Dir3.left then
              true else ilm_in ⟨m, hmk⟩) := by
      funext j
      by_cases hj : j = ⟨m, hmk⟩
      · subst hj; rw [Function.update_self]; simp only [Nat.lt_succ_self, true_and]
      · rw [Function.update_of_ne hj, hILMm]
        have hjm : (j : ℕ) ≠ m := fun h => hj (Fin.ext h)
        have hiff : ((j : ℕ) < m + 1 ∧ (c.work j).head = b ∧ (wact j).2 = Dir3.left)
            ↔ ((j : ℕ) < m ∧ (c.work j).head = b ∧ (wact j).2 = Dir3.left) :=
          ⟨fun h => ⟨by omega, h.2⟩, fun h => ⟨by omega, h.2⟩⟩
        simp only [hiff]
    -- ILMm at slot m collapses to the incoming ilm_in
    have hILMm_at : ILMm ⟨m, hmk⟩ = ilm_in ⟨m, hmk⟩ := by
      rw [hILMm]; simp only [lt_irrefl, false_and, if_false]
    have hRCm_at : RCm ⟨m, hmk⟩ = rc_in ⟨m, hmk⟩ := by
      rw [hRCm]; simp only [lt_irrefl, if_false]
    -- facts about the IH config cM = trace (3*m) c1
    have hcs : ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).state
        = SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, (⟨m, by omega⟩, 0), RCm, ILMm, false, false) := by
      rw [htm]; simp only [if_pos hmk]
    have hch : (((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).work 0).head
        = headBitCell k b ⟨m, hmk⟩ := by
      rw [show ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).work 0 = wtm from by rw [htm], hwhm]
      simp only [headBitCell]
    have hcbi : Scatter1BlockInv (((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).work 0)
        c.work wact M b m := by
      rw [show ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).work 0 = wtm from by rw [htm]]
      exact hbim
    have hcis : ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).input.read ≠ Γ.start := by
      rw [show ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).input = c1.input from by rw [htm]]
      exact his
    have hcos : ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).output.read ≠ Γ.start := by
      rw [show ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).output = c1.output from by rw [htm]]
      exact hos
    -- assembly closure (the trace_const_add + input/output reconciliation, done once)
    have key : ∀ (wt : Tape) (rc' ilm' : Fin k → Bool),
        (singleTapeSim N).trace 3 (fun _ => bb)
            ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1)
          = { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
                (⟨if m + 1 < k then m + 1 else 0, by split <;> omega⟩, 0), rc', ilm', false, false),
              input := ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).input,
              work := fun _ => wt,
              output := ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).output } →
        rc' = (fun (j : Fin k) => if (j : ℕ) < m + 1 then
            decide ((c.work j).head = b ∧ (wact j).2 = Dir3.right) else rc_in j) →
        ilm' = (fun (j : Fin k) => if (j : ℕ) < m + 1 ∧ (c.work j).head = b ∧ (wact j).2 = Dir3.left then
            true else ilm_in j) →
        wt.head = headBitCell k b ⟨m, hmk⟩ + 3 →
        Scatter1BlockInv wt c.work wact M b (m + 1) →
        ∃ wt' : Tape,
          (singleTapeSim N).trace (3 * (m + 1)) (fun _ => bb) c1 =
            { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
                (⟨if m + 1 < k then m + 1 else 0, by split <;> omega⟩, 0),
                (fun (j : Fin k) => if (j : ℕ) < m + 1 then
                    decide ((c.work j).head = b ∧ (wact j).2 = Dir3.right) else rc_in j),
                (fun (j : Fin k) => if (j : ℕ) < m + 1 ∧ (c.work j).head = b ∧ (wact j).2 = Dir3.left then
                    true else ilm_in j), false, false),
              input := c1.input, work := fun _ => wt', output := c1.output }
          ∧ wt'.head = blockStart k b + 3 * (m + 1)
          ∧ Scatter1BlockInv wt' c.work wact M b (m + 1) := by
      intro wt rc' ilm' htr hrc hilm hwh hbi
      refine ⟨wt, ?_, ?_, hbi⟩
      · rw [show 3 * (m + 1) = 3 * m + 3 from by omega, trace_const_add, htr, hrc, hilm,
          show ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).input = c1.input from by rw [htm],
          show ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).output = c1.output from by rw [htm]]
      · rw [hwh]; simp only [headBitCell]; omega
    -- helper: ¬(head = b - 1 ∧ right) when head = b
    have hndep_of_eq : (c.work ⟨m, hmk⟩).head = b →
        ¬((c.work ⟨m, hmk⟩).head = b - 1 ∧ (wact ⟨m, hmk⟩).2 = Dir3.right) :=
      fun he h => by obtain ⟨h1, _⟩ := h; omega
    -- dispatch on the old head-bit and the carry
    by_cases hhd : (c.work ⟨m, hmk⟩).head = b
    · rcases h3 : (wact ⟨m, hmk⟩).2 with _ | _ | _
      · -- left
        obtain ⟨wt, htr, hwh, hbi⟩ := scatter1_tape_head_left N bb c b M hb1 hbM m hmk
          q' wact oWoD iD iSym oSym RCm ILMm _ hcs hch hcbi hhd h3 hcis hcos
        refine key wt RCm (Function.update ILMm ⟨m, hmk⟩ true) htr ?_ ?_ hwh hbi
        · rw [hstep_rc, show decide ((c.work ⟨m, hmk⟩).head = b ∧ (wact ⟨m, hmk⟩).2 = Dir3.right)
              = RCm ⟨m, hmk⟩ from by
            rw [hRCm_at, hrc_in, decide_eq_false
                (fun h => by rw [h3] at h; exact absurd h.2 (by decide)),
              decide_eq_false (hndep_of_eq hhd)], Function.update_eq_self]
        · rw [hstep_ilm, if_pos ⟨hhd, h3⟩]
      · -- right
        obtain ⟨wt, htr, hwh, hbi⟩ := scatter1_tape_head_right N bb c b M hb1 hbM m hmk
          q' wact oWoD iD iSym oSym RCm ILMm _ hcs hch hcbi hhd h3 hcis hcos
        refine key wt (Function.update RCm ⟨m, hmk⟩ true) ILMm htr ?_ ?_ hwh hbi
        · rw [hstep_rc, decide_eq_true ⟨hhd, h3⟩]
        · rw [hstep_ilm, if_neg (show ¬((c.work ⟨m, hmk⟩).head = b ∧ (wact ⟨m, hmk⟩).2 = Dir3.left)
              from fun h => by rw [h3] at h; exact absurd h.2 (by decide)), ← hILMm_at,
            Function.update_eq_self]
      · -- stay
        obtain ⟨wt, htr, hwh, hbi⟩ := scatter1_tape_head_stay N bb c b M hb1 hbM m hmk
          q' wact oWoD iD iSym oSym RCm ILMm _ hcs hch hcbi hhd h3 hcis hcos
        refine key wt RCm ILMm htr ?_ ?_ hwh hbi
        · rw [hstep_rc, show decide ((c.work ⟨m, hmk⟩).head = b ∧ (wact ⟨m, hmk⟩).2 = Dir3.right)
              = RCm ⟨m, hmk⟩ from by
            rw [hRCm_at, hrc_in, decide_eq_false
                (fun h => by rw [h3] at h; exact absurd h.2 (by decide)),
              decide_eq_false (hndep_of_eq hhd)], Function.update_eq_self]
        · rw [hstep_ilm, if_neg (show ¬((c.work ⟨m, hmk⟩).head = b ∧ (wact ⟨m, hmk⟩).2 = Dir3.left)
              from fun h => by rw [h3] at h; exact absurd h.2 (by decide)), ← hILMm_at,
            Function.update_eq_self]
    · by_cases hdep : (c.work ⟨m, hmk⟩).head = b - 1 ∧ (wact ⟨m, hmk⟩).2 = Dir3.right
      · -- deposit
        obtain ⟨wt, htr, hwh, hbi⟩ := scatter1_tape_deposit N bb c b M hb1 hbM m hmk
          q' wact oWoD iD iSym oSym RCm ILMm _ hcs hch hcbi hdep
          (by rw [hRCm_at, hrc_in]; exact decide_eq_true hdep) hcis hcos
        refine key wt (Function.update RCm ⟨m, hmk⟩ false) ILMm htr ?_ ?_ hwh hbi
        · rw [hstep_rc, decide_eq_false (show ¬((c.work ⟨m, hmk⟩).head = b ∧ _) from fun h => hhd h.1)]
        · rw [hstep_ilm, if_neg (show ¬((c.work ⟨m, hmk⟩).head = b ∧ _) from fun h => hhd h.1),
            ← hILMm_at, Function.update_eq_self]
      · -- nohead
        obtain ⟨wt, htr, hwh, hbi⟩ := scatter1_tape_nohead N bb c b M hb1 hbM m hmk
          q' wact oWoD iD iSym oSym RCm ILMm _ hcs hch hcbi hhd hdep
          (by rw [hRCm_at, hrc_in]) hcis hcos
        refine key wt RCm ILMm htr ?_ ?_ hwh hbi
        · rw [hstep_rc, show decide ((c.work ⟨m, hmk⟩).head = b ∧ (wact ⟨m, hmk⟩).2 = Dir3.right)
              = RCm ⟨m, hmk⟩ from by
            rw [hRCm_at, hrc_in, decide_eq_false (fun h => hhd h.1), decide_eq_false hdep],
            Function.update_eq_self]
        · rw [hstep_ilm, if_neg (show ¬((c.work ⟨m, hmk⟩).head = b ∧ _) from fun h => hhd h.1),
            ← hILMm_at, Function.update_eq_self]

/-- **SCATTER one full block (`trace (3*k)`).** Sweeping all `k` tapes of block `b`
    advances the mid-sweep invariant `Scatter1MidInv … b → … (b+1)`: the head moves
    to `blockStart k (b+1)`, the carry `rc` updates from the incoming
    `decide(head = b-1 ∧ right)` to the outgoing `decide(head = b ∧ right)` (= the
    incoming carry of block `b+1`), and `ilm` records block `b`'s left-movers.
    Wraps `scatter1_block_aux` at `m = k` between `ofMid` and `toMidSucc`. -/
theorem scatter1_block_step {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (b M : ℕ)
    (hb1 : 1 ≤ b) (hbM : b ≤ M)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (rc_in ilm_in : Fin k → Bool)
    (hrc_in : ∀ j : Fin k, rc_in j = decide ((c.work j).head = b - 1 ∧ (wact j).2 = Dir3.right))
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨0, by omega⟩, 0), rc_in, ilm_in, false, false))
    (hhead : (c1.work 0).head = blockStart k b)
    (hmid : Scatter1MidInv (c1.work 0) c.work wact M b)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    ∃ wt : Tape,
      (singleTapeSim N).trace (3 * k) (fun _ => bb) c1 =
        { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, (⟨0, by omega⟩, 0),
            (fun j => decide ((c.work j).head = b ∧ (wact j).2 = Dir3.right)),
            (fun j => if (c.work j).head = b ∧ (wact j).2 = Dir3.left then true else ilm_in j),
            false, false),
          input := c1.input, work := fun _ => wt, output := c1.output }
      ∧ wt.head = blockStart k (b + 1)
      ∧ Scatter1MidInv wt c.work wact M (b + 1) := by
  obtain ⟨wt, htr, hwh, hbi⟩ := scatter1_block_aux N bb c b M hb1 hbM q' wact oWoD iD iSym oSym
    rc_in ilm_in hrc_in c1 hst hhead (Scatter1BlockInv.ofMid hbM hmid) his hos k (le_refl k)
  refine ⟨wt, ?_, ?_, Scatter1BlockInv.toMidSucc hbi⟩
  · rw [htr]
    have hrc_k : (fun (j : Fin k) => if (j : ℕ) < k then
          decide ((c.work j).head = b ∧ (wact j).2 = Dir3.right) else rc_in j)
        = (fun j => decide ((c.work j).head = b ∧ (wact j).2 = Dir3.right)) := by
      funext j; rw [if_pos j.isLt]
    have hilm_k : (fun (j : Fin k) => if (j : ℕ) < k ∧ (c.work j).head = b ∧ (wact j).2 = Dir3.left then
          true else ilm_in j)
        = (fun j => if (c.work j).head = b ∧ (wact j).2 = Dir3.left then true else ilm_in j) := by
      funext j; simp only [j.isLt, true_and]
    rw [hrc_k, hilm_k]
    simp only [lt_irrefl, if_false]
  · rw [hwh, blockStart_succ k b hb1, blockWidth]

/-- **SCATTER full block sweep (`trace (3*k*B)`).** Sweeping the first `B ≤ M`
    blocks (from block `1`, tape `0`, slot `0`, work head `blockStart k 1`, incoming
    carry `decide(head = 0 ∧ right)`, the REWIND output `SimInvAt M`): after `B`
    blocks the head is at `blockStart k (B+1)`, the sweep is back at tape `0` slot
    `0`, the carry records the right-movers whose head is at `B`, `ilm` records the
    left-movers in blocks `[1, B]`, and the tape is `Scatter1MidInv … (B+1)`. Proved
    by induction on `B`, each step one `scatter1_block_step` at block `B+1`. -/
theorem scatter1_sweep_aux {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (M : ℕ)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (ilm_in : Fin k → Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, (⟨0, by omega⟩, 0),
      (fun j => decide ((c.work j).head = 0 ∧ (wact j).2 = Dir3.right)), ilm_in, false, false))
    (hhead : (c1.work 0).head = blockStart k 1)
    (hsim : SimInvAt k (c1.work 0) c.work M)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start)
    (B : ℕ) (hB : B ≤ M) :
    ∃ wt : Tape,
      (singleTapeSim N).trace (3 * k * B) (fun _ => bb) c1 =
        { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, (⟨0, by omega⟩, 0),
            (fun j => decide ((c.work j).head = B ∧ (wact j).2 = Dir3.right)),
            (fun j => if 1 ≤ (c.work j).head ∧ (c.work j).head ≤ B ∧ (wact j).2 = Dir3.left then
                true else ilm_in j),
            false, false),
          input := c1.input, work := fun _ => wt, output := c1.output }
      ∧ wt.head = blockStart k (B + 1)
      ∧ Scatter1MidInv wt c.work wact M (B + 1) := by
  induction B with
  | zero =>
    refine ⟨c1.work 0, ?_, ?_, scatter1MidInv_init wact hsim⟩
    · have h0 : (singleTapeSim N).trace (3 * k * 0) (fun _ => bb) c1 = c1 := by
        simp only [Nat.mul_zero]; rfl
      rw [h0]
      obtain ⟨cst, cin, cwk, cout⟩ := c1
      subst hst
      refine (Cfg.mk.injEq ..).mpr ⟨?_, rfl, ?_, rfl⟩
      · rw [show (fun (j : Fin k) => if 1 ≤ (c.work j).head ∧ (c.work j).head ≤ 0 ∧
              (wact j).2 = Dir3.left then true else ilm_in j) = ilm_in from by
          funext j; rw [if_neg (by rintro ⟨h1, h2, _⟩; omega)]]
      · funext x
        obtain rfl : x = 0 := Subsingleton.elim x 0
        rfl
    · exact hhead
  | succ B ih =>
    obtain ⟨wtB, htB, hwhB, hmidB⟩ := ih (by omega)
    have hcw : ((singleTapeSim N).trace (3 * k * B) (fun _ => bb) c1).work 0 = wtB := by rw [htB]
    have hci : ((singleTapeSim N).trace (3 * k * B) (fun _ => bb) c1).input = c1.input := by rw [htB]
    have hco : ((singleTapeSim N).trace (3 * k * B) (fun _ => bb) c1).output = c1.output := by rw [htB]
    obtain ⟨wt, htr, hwh, hmid'⟩ := scatter1_block_step N bb c (B + 1) M (by omega) hB
      q' wact oWoD iD iSym oSym
      (fun j => decide ((c.work j).head = B ∧ (wact j).2 = Dir3.right))
      (fun j => if 1 ≤ (c.work j).head ∧ (c.work j).head ≤ B ∧ (wact j).2 = Dir3.left then
          true else ilm_in j)
      (fun j => by simp only [Nat.add_sub_cancel])
      ((singleTapeSim N).trace (3 * k * B) (fun _ => bb) c1) (by rw [htB])
      (by rw [hcw]; exact hwhB) (by rw [hcw]; exact hmidB)
      (by rw [hci]; exact his) (by rw [hco]; exact hos)
    refine ⟨wt, ?_, ?_, hmid'⟩
    · rw [show 3 * k * (B + 1) = 3 * k * B + 3 * k from Nat.mul_succ (3 * k) B,
        trace_const_add, htr, hci, hco]
      refine (Cfg.mk.injEq ..).mpr ⟨?_, rfl, rfl, rfl⟩
      rw [show (fun (j : Fin k) => if (c.work j).head = B + 1 ∧ (wact j).2 = Dir3.left then true
            else if 1 ≤ (c.work j).head ∧ (c.work j).head ≤ B ∧ (wact j).2 = Dir3.left then
              true else ilm_in j)
          = (fun j => if 1 ≤ (c.work j).head ∧ (c.work j).head ≤ B + 1 ∧ (wact j).2 = Dir3.left then
              true else ilm_in j) from by
        funext j
        by_cases hL : (wact j).2 = Dir3.left
        · simp only [hL, and_true]
          split_ifs with h1 h2 h3 <;> first | rfl | omega
        · simp only [hL, and_false, if_false]]
    · rw [hwh]

/-- **Macro-step correspondence (the core obligation).** From a corresponding,
    non-halted configuration, for any nondeterministic choice `bit`, the
    simulator runs some number `m` of steps (with a choice sequence that feeds
    `bit` at the COMPUTE sub-step) and lands in a configuration corresponding to
    `N`'s one-step image under `bit`, with the materialized region grown by one,
    within `macroBound k M` sim steps.

    This is the heart of the behavioural correctness proof: it is established by
    tracing the phase machine `run → gather → rewind → scatter1 → scatter2 →
    commit` and showing each phase preserves/advances `SimInvAt`. -/
theorem macroStepCorr {k : ℕ} (N : NTM k) {M : ℕ}
    {c1 : Cfg 1 (SimQ k N.Q)} {c : Cfg k N.Q}
    (hcorr : Corr N M c1 c) (hne : c.state ≠ N.qhalt) (bitf : Fin 1 → Bool) :
    ∃ (m : ℕ) (choices : Fin m → Bool),
      Corr N (M + 1) ((singleTapeSim N).trace m choices c1) (N.trace 1 bitf c)
        ∧ m ≤ macroBound k M := by
  sorry

/-- **Iterated correspondence.** Simulating `t` steps of `N` (choices `g`): the
    simulator reaches, in some number `m` of steps (choices from a single
    `ℕ`-indexed `F`), a configuration corresponding to `N.trace t g c` (at some
    materialization level `M'`). Proved by induction on `t`, composing
    macro-steps with `trace_add`; the halted case reuses the previous one. -/
theorem iterCorr {k : ℕ} (N : NTM k) {M : ℕ}
    {c1 : Cfg 1 (SimQ k N.Q)} {c : Cfg k N.Q}
    (hcorr : Corr N M c1 c) (g : ℕ → Bool) (t : ℕ) :
    ∃ (m M' : ℕ) (F : ℕ → Bool),
      Corr N M' ((singleTapeSim N).trace m (fun i => F i.val) c1)
        (N.trace t (fun i => g i.val) c)
        ∧ M' ≤ M + t ∧ m ≤ t * macroBound k (M + t) := by
  induction t with
  | zero => exact ⟨0, M, g, hcorr, by omega, by omega⟩
  | succ t ih =>
    obtain ⟨m, M', f, hcorr_t, hM'le, hmle⟩ := ih
    set s_t := (singleTapeSim N).trace m (fun i => f i.val) c1 with hs_t
    set c_t := N.trace t (fun i => g i.val) c with hc_t
    -- N's (t+1)-step trace splits as one step from c_t
    have hNsplit : N.trace (t + 1) (fun i => g i.val) c
        = N.trace 1 (fun i => g (t + i.val)) c_t := by
      rw [hc_t]; exact N.trace_add t 1 g c
    -- the new bound `(t+1)·macroBound k (M+(t+1))` dominates the old one
    have hgrow : t * macroBound k (M + t) ≤ (t + 1) * macroBound k (M + (t + 1)) :=
      le_trans (Nat.mul_le_mul (Nat.le_succ t) (macroBound_mono (by omega)))
        (le_refl _)
    by_cases hh : c_t.state = N.qhalt
    · -- N has halted: the (t+1) step is a no-op, reuse the IH config
      refine ⟨m, M', f, ?_, by omega, le_trans hmle hgrow⟩
      rw [hNsplit, N.trace_halted 1 _ hh]
      exact hcorr_t
    · -- N steps: apply the macro-step correspondence and concatenate choices
      obtain ⟨m', choices', hstep, hbound'⟩ :=
        macroStepCorr N hcorr_t hh (fun i => g (t + i.val))
      -- concatenate `f` (first m steps) and `choices'` (next m') into one `F`
      set F : ℕ → Bool :=
        fun j => if j < m then f j else if h : j - m < m' then choices' ⟨j - m, h⟩ else false
        with hF
      refine ⟨m + m', M' + 1, F, ?_, by omega, ?_⟩
      · rw [hNsplit, (singleTapeSim N).trace_add m m' F c1]
        have hpre : (fun i : Fin m => F i.val) = (fun i : Fin m => f i.val) := by
          funext i; rw [hF]; simp only []; rw [if_pos i.isLt]
        have hsuf : (fun i : Fin m' => F (m + i.val)) = choices' := by
          funext i; rw [hF]; simp only []
          rw [if_neg (by omega), dif_pos (by omega)]
          have hsub : m + i.val - m = i.val := by omega
          simp only [hsub, Fin.eta]
        rw [hpre, ← hs_t, hsuf]
        exact hstep
      · -- m + m' ≤ (t+1)·macroBound k (M+(t+1))
        have hb1 : m ≤ t * macroBound k (M + (t + 1)) :=
          le_trans hmle (Nat.mul_le_mul (le_refl t) (macroBound_mono (by omega)))
        have hb2 : m' ≤ macroBound k (M + (t + 1)) :=
          le_trans hbound' (macroBound_mono (by omega))
        calc m + m' ≤ t * macroBound k (M + (t + 1)) + macroBound k (M + (t + 1)) :=
              Nat.add_le_add hb1 hb2
          _ = (t + 1) * macroBound k (M + (t + 1)) := by rw [Nat.succ_mul]

/-- **Forward acceptance.** If `N` accepts `x` within `Tn` steps, then
    `singleTapeSim N` accepts `x` within `Tn · macroBound k Tn + 1` steps:
    simulate `N`'s accepting run (`iterCorr`), then one `haltCorr` step lands in
    a halted accepting simulator config; pad via `AcceptsInTime_mono`. -/
theorem accepts_fwd {k : ℕ} (N : NTM k) (x : List Bool) (Tn : ℕ)
    (h : N.AcceptsInTime x Tn) :
    (singleTapeSim N).AcceptsInTime x (Tn * macroBound k Tn + 1) := by
  obtain ⟨chN, hhalt, hacc⟩ := h
  set g : ℕ → Bool := fun i => if hi : i < Tn then chN ⟨i, hi⟩ else false with hg
  obtain ⟨m, M', F, hcorr, _hM', hm⟩ := iterCorr N (corr_init N x) g Tn
  have hgN : (fun i : Fin Tn => g i.val) = chN := by
    funext i; rw [hg]; simp only []; rw [dif_pos i.isLt]
  rw [hgN] at hcorr
  -- one halt step lands in a halted, accepting simulator config
  obtain ⟨hhalted, hbit⟩ := haltCorr N hcorr hhalt
  -- the accepting config is reached after `m + 1` sim steps
  set sCfg := (singleTapeSim N).trace m (fun i => F i.val) ((singleTapeSim N).initCfg x) with hsCfg
  set F' : ℕ → Bool := fun j => if j < m then F j else false with hF'
  have hcompose : (singleTapeSim N).trace (m + 1) (fun i => F' i.val) ((singleTapeSim N).initCfg x)
      = (singleTapeSim N).trace 1 (fun _ => false) sCfg := by
    rw [(singleTapeSim N).trace_add m 1 F']
    have e1 : (fun i : Fin m => F' i.val) = (fun i : Fin m => F i.val) := by
      funext i; rw [hF']; simp only [i.isLt, if_true]
    have e2 : (fun i : Fin 1 => F' (m + i.val)) = (fun _ => false) := by
      funext i; rw [hF']; simp only []; rw [if_neg (by omega)]
    rw [e1, e2, ← hsCfg]
  have key : (singleTapeSim N).AcceptsInTime x (m + 1) := by
    refine ⟨fun i => F' i.val, ?_, ?_⟩
    · rw [hcompose]; exact hhalted
    · rw [hcompose]; exact hbit.mpr hacc
  exact NTM.AcceptsInTime_mono (by
    have : Tn * macroBound k (0 + Tn) = Tn * macroBound k Tn := by rw [Nat.zero_add]
    omega) key

end NTM.SingleTape
