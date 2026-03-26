import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.Hoare
import Complexitylib.Models.TuringMachine.UTM.Defs
import Complexitylib.Models.TuringMachine.UTM.Helpers
import Complexitylib.Models.TuringMachine.UTM.HelpersInternal
import Complexitylib.Models.TuringMachine.UTM.SimConfig.Defs
import Complexitylib.Models.TuringMachine.UTM.Init
import Complexitylib.Models.TuringMachine.UTM.ReadCurrent
import Complexitylib.Models.TuringMachine.UTM.Lookup
import Complexitylib.Models.TuringMachine.UTM.LookupInternal
import Complexitylib.Models.TuringMachine.UTM.ApplyTransition
import Complexitylib.Models.TuringMachine.UTM.ApplyTransitionInternal
import Complexitylib.Models.TuringMachine.UTM.CheckHalt
import Complexitylib.Models.TuringMachine.UTM.CheckHaltInternal
import Complexitylib.Models.TuringMachine.UTM.ExtractOutput

/-!
# Universal Turing Machine (AB Theorem 1.9)

Top-level composition of the UTM from sub-machines, connected via
`seqTM_hoareTime` and `loopTM_hoareTime`.

## Architecture

```
utmTM =
  seqTM initTM
    (seqTM (loopTM utmSimStepTM utmCheckHaltTM)
      extractOutputTM)
```

Where:
```
utmSimStepTM =
  seqTM readCurrentTM
    (seqTM lookupTM
      applyTransitionTM)
```

## Main results

- `utmTM` — the Universal Turing Machine definition
- `utm_simulates` — simulation correctness theorem
- `utm_correct` — AB Theorem 1.9: O(T²) time overhead
-/

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- Simulation step machine: one step of the simulated TM
-- ════════════════════════════════════════════════════════════════════════

/-- The simulation step machine performs one step of the simulated TM.
    Composed as: readCurrentTM ; lookupTM ; applyTransitionTM.
    Parametric in `k` (number of states of the simulated TM). -/
noncomputable def utmSimStepTM (k : ℕ) : TM 4 :=
  seqTM (readCurrentTM (n := n)) (seqTM (lookupTM (n := n) k) (applyTransitionTM (n := n) k))

-- ════════════════════════════════════════════════════════════════════════
-- The Universal Turing Machine
-- ════════════════════════════════════════════════════════════════════════

/-- The Universal Turing Machine.
    Architecture: initTM ; loop(simStepTM, checkHaltTM) ; extractOutputTM.
    Parametric in `k` (number of states of the simulated TM). -/
noncomputable def utmTM (k : ℕ) : TM 4 :=
  seqTM initTM
    (seqTM (loopTM (utmSimStepTM (n := n) k) utmCheckHaltTM)
      (extractOutputTM (n := n)))

-- ════════════════════════════════════════════════════════════════════════
-- Simulation correctness
-- ════════════════════════════════════════════════════════════════════════

/-- The UTM's initial configuration with input `⟨M, x⟩` encoded as `List Γ`.
    Uses `initTape` directly since `encodeUTMInput` returns `List Γ`
    (not `List Bool`), which already includes the blank separator. -/
noncomputable def utmInitCfg (tm : TM n) (k : ℕ) (x : List Bool) :
    Cfg 4 (utmTM (n := n) k).Q :=
  { state := (utmTM (n := n) k).qstart,
    input := initTape (encodeUTMInput tm x),
    work := fun _ => initTape [],
    output := initTape [] }

/-- Simulated work/output tape heads stay at position ≥ 1 throughout computation.

    This holds for TMs where `δ_right_of_start` ensures the first step moves all
    heads from position 0 (▷) to position 1, and no subsequent step moves
    work/output tape heads back to position 0. Required because `applyTransitionTM`
    writes symbol cells at the head position, which corrupts the super-cell encoding
    at position 0 (where `Tape.write` is a no-op but the encoding gets overwritten). -/
def SimHeadsGe1 (tm : TM n) (x : List Bool) : Prop :=
  ∀ (c : Cfg n tm.Q) (t : ℕ), t ≥ 1 → tm.reachesIn t (tm.initCfg x) c →
    (∀ i, (c.work i).head ≥ 1) ∧ c.output.head ≥ 1

/-- The UTM correctly simulates any TM M: if M decides L in time T,
    then running the UTM on `encodeUTMInput tm x` produces the same
    accept/reject decision as M on x.

    The `hHeads` hypothesis requires that simulated work/output tape heads
    stay at position ≥ 1 throughout computation (see `SimHeadsGe1`). -/
theorem utm_simulates (tm : TM n) (k : ℕ) (hk : k = @Fintype.card tm.Q tm.finQ)
    (L : Language) (T : ℕ → ℕ)
    (hM : tm.DecidesInTime L T) (x : List Bool)
    (hHeads : tm.SimHeadsGe1 x) :
    ∃ (c' : Cfg 4 (utmTM (n := n) k).Q) (t : ℕ),
      (utmTM (n := n) k).reachesIn t (utmInitCfg tm k x) c' ∧
      (utmTM (n := n) k).halted c' ∧
      (x ∈ L → c'.output.cells 1 = Γ.one) ∧
      (x ∉ L → c'.output.cells 1 = Γ.zero) := by
  -- Step 1: Get the simulated TM's halting computation
  obtain ⟨c_sim, t_sim, _ht_sim, hreach_sim, hhalt_sim, hmem, hnmem⟩ := hM x
  -- Step 2: The proof composes initTM, loopTM, and extractOutputTM.
  -- This requires threading Hoare specs through seqTM composition
  -- with all tape invariants (SimInvariant, scratch blank, inp/out WF).
  -- The composition is extremely involved (~500 lines) and requires:
  -- - initTM_hoareTime for initialization
  -- - Strong induction on t_sim for the loop body
  -- - extractOutputTM_hoareTime for output extraction
  -- - seqTM lifting lemmas from SeqInternal.lean
  -- - loopTM iteration lemmas from LoopInternal.lean
  sorry

-- ════════════════════════════════════════════════════════════════════════
-- AB Theorem 1.9: O(T²) overhead
-- ════════════════════════════════════════════════════════════════════════

/-- **Arora-Barak Theorem 1.9** (basic construction).

    For every TM M that decides language L in time T, there exists a
    constant C (depending on |M| but not the input) such that the UTM
    decides L in time C · T².

    The `hHeads` hypothesis requires that for every input x, the simulated
    work/output tape heads stay at position ≥ 1 (see `SimHeadsGe1`). -/
theorem utm_correct (tm : TM n) (k : ℕ) (hk : k = @Fintype.card tm.Q tm.finQ)
    (L : Language) (T : ℕ → ℕ)
    (hM : tm.DecidesInTime L T)
    (hHeads : ∀ x, tm.SimHeadsGe1 x) :
    ∃ (C : ℕ),
      (utmTM (n := n) k).DecidesInTime L (fun len => C * (T len) ^ 2) := by
  -- NOTE: DecidesInTime uses (utmTM k).initCfg x which puts raw x on the
  -- input tape. But the UTM needs encodeUTMInput tm x (with TM description
  -- prefix). Since Γ.ofBool cannot produce Γ.blank (the separator), there
  -- is no y : List Bool such that (utmTM k).initCfg y matches
  -- utmInitCfg tm k x. This theorem requires reformulation.
  -- See utm_simulates for the correctly formulated simulation result.
  sorry

end TM
