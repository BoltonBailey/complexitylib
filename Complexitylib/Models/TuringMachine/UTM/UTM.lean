import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.Hoare
import Complexitylib.Models.TuringMachine.UTM.Defs
import Complexitylib.Models.TuringMachine.UTM.Helpers
import Complexitylib.Models.TuringMachine.UTM.HelpersInternal
import Complexitylib.Models.TuringMachine.UTM.SimConfig.Defs
import Complexitylib.Models.TuringMachine.UTM.Init
import Complexitylib.Models.TuringMachine.UTM.ReadCurrent
import Complexitylib.Models.TuringMachine.UTM.Lookup
import Complexitylib.Models.TuringMachine.UTM.ApplyTransition
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
    Composed as: readCurrentTM ; lookupTM ; applyTransitionTM. -/
noncomputable def utmSimStepTM : TM 4 :=
  seqTM (readCurrentTM (n := n)) (seqTM lookupTM applyTransitionTM)

-- ════════════════════════════════════════════════════════════════════════
-- The Universal Turing Machine
-- ════════════════════════════════════════════════════════════════════════

/-- The Universal Turing Machine.
    Architecture: initTM ; loop(simStepTM, checkHaltTM) ; extractOutputTM. -/
noncomputable def utmTM : TM 4 :=
  seqTM initTM
    (seqTM (loopTM (utmSimStepTM (n := n)) utmCheckHaltTM)
      extractOutputTM)

-- ════════════════════════════════════════════════════════════════════════
-- Simulation correctness
-- ════════════════════════════════════════════════════════════════════════

/-- The UTM's initial configuration with input `⟨M, x⟩` encoded as `List Γ`.
    Uses `initTape` directly since `encodeUTMInput` returns `List Γ`
    (not `List Bool`), which already includes the blank separator. -/
noncomputable def utmInitCfg (tm : TM n) (x : List Bool) : Cfg 4 (utmTM (n := n)).Q :=
  { state := (utmTM (n := n)).qstart,
    input := initTape (encodeUTMInput tm x),
    work := fun _ => initTape [],
    output := initTape [] }

/-- The UTM correctly simulates any TM M: if M decides L in time T,
    then running the UTM on `encodeUTMInput tm x` produces the same
    accept/reject decision as M on x.

    This connects all the sub-machine specs:
    - `initTM` establishes `SimInvariant` for `tm.initCfg x`
    - Each iteration of `loopTM` advances the simulated config by one step
      (via `readCurrentTM` → `lookupTM` → `applyTransitionTM`)
    - `utmCheckHaltTM` detects when the simulated TM halts
    - `extractOutputTM` copies the simulated output to real output -/
theorem utm_simulates (tm : TM n) (L : Language) (T : ℕ → ℕ)
    (hM : tm.DecidesInTime L T) (x : List Bool) :
    ∃ (c' : Cfg 4 (utmTM (n := n)).Q) (t : ℕ),
      (utmTM (n := n)).reachesIn t (utmInitCfg tm x) c' ∧
      (utmTM (n := n)).halted c' ∧
      (x ∈ L → c'.output.cells 1 = Γ.one) ∧
      (x ∉ L → c'.output.cells 1 = Γ.zero) := by
  sorry

-- ════════════════════════════════════════════════════════════════════════
-- AB Theorem 1.9: O(T²) overhead
-- ════════════════════════════════════════════════════════════════════════

/-- **Arora-Barak Theorem 1.9** (basic construction).

    For every TM M that decides language L in time T, there exists a
    constant C (depending on |M| but not the input) such that the UTM
    decides L in time C · T². -/
theorem utm_correct (tm : TM n) (L : Language) (T : ℕ → ℕ)
    (hM : tm.DecidesInTime L T) :
    ∃ (C : ℕ),
      (utmTM (n := n)).DecidesInTime L (fun len => C * (T len) ^ 2) := by
  sorry

end TM
