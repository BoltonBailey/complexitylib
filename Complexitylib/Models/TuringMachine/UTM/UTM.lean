import Complexitylib.Models.TuringMachine.UTM.Machine
import Complexitylib.Models.TuringMachine.UTM.SimLoop

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

- `utmTM` — the Universal Turing Machine definition (in Machine.lean)
- `utm_simulates` — simulation correctness theorem
- `utm_correct` — AB Theorem 1.9: O(T²) time overhead
-/

namespace TM

variable {n : ℕ}

/-- The UTM correctly simulates any TM M: if M decides L in time T,
    then running the UTM on `encodeUTMInput tm x` produces the same
    accept/reject decision as M on x. -/
theorem utm_simulates (tm : TM n) (k : ℕ) (hk : k = @Fintype.card tm.Q tm.finQ)
    (L : Language) (T : ℕ → ℕ)
    (hM : tm.DecidesInTime L T) (x : List Bool) :
    ∃ (c' : Cfg 4 (utmTM (n := n) k).Q) (t : ℕ),
      (utmTM (n := n) k).reachesIn t (utmInitCfg tm k x) c' ∧
      (utmTM (n := n) k).halted c' ∧
      (x ∈ L → c'.output.cells 1 = Γ.one) ∧
      (x ∉ L → c'.output.cells 1 = Γ.zero) :=
  utm_simulates_proof tm k hk L T hM x

-- ════════════════════════════════════════════════════════════════════════
-- AB Theorem 1.9: O(T²) overhead
-- ════════════════════════════════════════════════════════════════════════

/-- **Arora-Barak Theorem 1.9** (basic construction).

    For every TM M that decides language L in time T, there exists a
    constant C (depending on |M| but not the input) such that the UTM
    decides L in time C · T². -/
theorem utm_correct (tm : TM n) (k : ℕ) (hk : k = @Fintype.card tm.Q tm.finQ)
    (L : Language) (T : ℕ → ℕ)
    (hM : tm.DecidesInTime L T) :
    ∃ (C : ℕ),
      (utmTM (n := n) k).DecidesInTime L (fun len => C * (T len) ^ 2) := by
  sorry

end TM
