import Complexitylib.Models.TuringMachine
import Complexitylib.Classes.Polynomial

/-!
# FP

This file defines **FP**, the class of functions computable by a deterministic
Turing machine in polynomial time.
-/

/-- **FP** is the class of functions computable by a deterministic TM in
    polynomial time. -/
def FP : Set (List Bool → List Bool) :=
  {f | ∃ (T : ℕ → ℕ), IsPolyBounded T ∧ ∃ (k : ℕ) (tm : TM k), tm.ComputesInTime f T}
