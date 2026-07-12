/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.FiniteCounting
import Complexitylib.Models.TuringMachine.Repetition.Defs

/-!
# Fixed-time probabilistic-machine repetition

This public surface records the exact arithmetic schedule of
`NTM.repeatAtTime` and connects its simulated-step positions to the generic
compact-seed projection from `Complexitylib.Classes.FiniteCounting`.

It deliberately makes no trace or acceptance claim: those require the
simulation invariants proved in the internal correctness layer.

## Main results

- `NTM.repeatAtTimeStride_zero`, `NTM.repeatAtTimeStride_succ` — stride arithmetic
- `NTM.repeatAtTimeSteps_zero`, `NTM.repeatAtTimeSteps_succ` — total-time arithmetic
- `NTM.repeatRandomSeed_apply_repeatChoiceIdx` — compact and machine schedules align
-/

namespace Complexity

namespace NTM

/-! ### Exact schedule arithmetic -/

/-- With zero simulated steps, a stride consists only of rewind and finish. -/
@[simp] theorem repeatAtTimeStride_zero : repeatAtTimeStride 0 = 2 := rfl

/-- Increasing the simulated time by one adds one simulation transition and one
rewind transition to every stride. -/
theorem repeatAtTimeStride_succ (T : ℕ) :
    repeatAtTimeStride (T + 1) = repeatAtTimeStride T + 2 := by
  simp only [repeatAtTimeStride]
  omega

/-- Zero repetitions use exactly the two leading administrative transitions. -/
@[simp] theorem repeatAtTimeSteps_zero (T : ℕ) : repeatAtTimeSteps 0 T = 2 := by
  simp [repeatAtTimeSteps]

/-- At zero simulated time, every repetition contributes its two administrative
transitions. -/
@[simp] theorem repeatAtTimeSteps_zero_time (k : ℕ) :
    repeatAtTimeSteps k 0 = 2 + k * 2 := by
  simp [repeatAtTimeSteps]

/-- Adding one repetition appends exactly one stride. -/
theorem repeatAtTimeSteps_succ (k T : ℕ) :
    repeatAtTimeSteps (k + 1) T = repeatAtTimeSteps k T + repeatAtTimeStride T := by
  simp [repeatAtTimeSteps, Nat.add_mul, Nat.add_assoc]

/-! ### Compact-seed alignment -/

/-- The generic compact repetition seed selects exactly the global choice
position used by `repeatAtTime` for simulated step `t` of repetition `j`. -/
@[simp] theorem repeatRandomSeed_apply_repeatChoiceIdx (k T : ℕ)
    (choices : Fin (repeatAtTimeSteps k T) → Bool) (j : Fin k) (t : Fin T) :
    repeatRandomSeed k T choices (finProdFinEquiv (j, t)) =
      choices (repeatChoiceIdx T j t) := by
  rw [repeatRandomSeed_apply]
  congr 1
  apply Fin.ext
  change 2 + (t.val + (2 * T + 2) * j.val) =
    2 + j.val * (2 * T + 2) + t.val
  rw [Nat.mul_comm (2 * T + 2) j.val]
  omega

end NTM

end Complexity
