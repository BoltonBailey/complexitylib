import Complexitylib.Models.TuringMachine
import Complexitylib.Classes.Polynomial

/-!
# DTIME, P, and FP

This file defines the deterministic time complexity class `DTIME(T)`, the
class **P** of languages decidable in polynomial time, and the function class
**FP** of functions computable in polynomial time.
-/

/-- `DTIME(T)` is the class of languages decidable by a deterministic TM in
    time `c · T(n)` for some constant `c` (AB Definition 1.6). The machine may
    have any number of work tapes. -/
def DTIME (T : ℕ → ℕ) : Set Language :=
  {L | ∃ (c k : ℕ) (tm : TM k), tm.DecidesInTime L (fun n => c * T n)}

/-- **P** is the class of languages decidable by a deterministic TM in
    polynomial time: `P = ∪_T DTIME(T)` over polynomially bounded `T`. -/
def P : Set Language :=
  {L | ∃ (T : ℕ → ℕ), IsPolyBounded T ∧ L ∈ DTIME T}

/-- **FP** is the class of functions computable by a deterministic TM in
    polynomial time. -/
def FP : Set (List Bool → List Bool) :=
  {f | ∃ (T : ℕ → ℕ), IsPolyBounded T ∧ ∃ (k : ℕ) (tm : TM k), tm.ComputesInTime f T}
