import Complexitylib.Models.TuringMachine
import Complexitylib.Classes.Polynomial

/-!
# DTIME and P

This file defines the deterministic time complexity class `DTIME(T)` and the
class **P** of languages decidable in polynomial time (Arora-Barak Definitions
1.2–1.3).
-/

/-- `DTIME(T)` is the class of languages decidable by a deterministic TM in
    time `T(n)` (Arora-Barak Definition 1.2). The machine may have any number
    of work tapes. -/
def DTIME (T : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : TM k), tm.DecidesInTime L T}

/-- **P** is the class of languages decidable by a deterministic TM in
    polynomial time: `P = ∪_T DTIME(T)` over polynomially bounded `T`
    (Arora-Barak Definition 1.3). -/
def P : Set Language :=
  {L | ∃ (T : ℕ → ℕ), IsPolyBounded T ∧ L ∈ DTIME T}
