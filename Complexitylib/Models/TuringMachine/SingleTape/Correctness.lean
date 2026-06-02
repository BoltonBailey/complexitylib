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
