import Complexitylib.Models.TuringMachine
import Complexitylib.Classes.Polynomial

/-!
# NTIME, NP, and coNP

This file defines the nondeterministic time complexity class `NTIME(T)`, the
class **NP** of languages decidable by a nondeterministic TM in polynomial time,
and **coNP** as the complement class.
-/

/-- `NTIME(T)` is the class of languages decidable by a nondeterministic TM in
    time `T(n)`. The machine may have any number of work tapes. -/
def NTIME (T : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : NTM k), tm.DecidesInTime L T}

/-- **NP** is the class of languages decidable by a nondeterministic TM in
    polynomial time: `NP = ∪_T NTIME(T)` over polynomially bounded `T`. -/
def NP : Set Language :=
  {L | ∃ (T : ℕ → ℕ), IsPolyBounded T ∧ L ∈ NTIME T}

/-- **coNP** is the class of languages whose complements are in NP. -/
def CoNP : Set Language :=
  {L | Lᶜ ∈ NP}
