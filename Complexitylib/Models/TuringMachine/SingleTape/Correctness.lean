import Complexitylib.Models.TuringMachine.SingleTape.Delta

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

/-- **Macro-step correspondence (the core obligation).** From a corresponding,
    non-halted configuration, for any nondeterministic choice `bit`, the
    simulator runs some number `m` of steps (with a choice sequence that feeds
    `bit` at the COMPUTE sub-step) and lands in a configuration corresponding to
    `N`'s one-step image under `bit`, with the materialized region grown by one.

    This is the heart of the behavioural correctness proof: it is established by
    tracing the phase machine `run → gather → rewind → scatter1 → scatter2 →
    commit` and showing each phase preserves/advances `SimInvAt`. -/
theorem macroStepCorr {k : ℕ} (N : NTM k) {M : ℕ}
    {c1 : Cfg 1 (SimQ k N.Q)} {c : Cfg k N.Q}
    (hcorr : Corr N M c1 c) (hne : c.state ≠ N.qhalt) (bit : Bool) :
    ∃ (m : ℕ) (choices : Fin m → Bool),
      Corr N (M + 1) ((singleTapeSim N).trace m choices c1) (N.trace 1 (fun _ => bit) c) := by
  sorry

end NTM.SingleTape
