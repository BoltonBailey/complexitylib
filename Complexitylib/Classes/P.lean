import Complexitylib.Models.TuringMachine
import Complexitylib.Classes.Polynomial

/-!
# DTIME and P

This file defines the deterministic time complexity class `DTIME(T)` and the
class **P** of languages decidable in polynomial time.
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
