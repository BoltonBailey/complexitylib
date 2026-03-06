import Complexitylib.Models.TuringMachine
import Complexitylib.Classes.Polynomial

/-!
# NTIME, NP, and coNP

This file defines the nondeterministic time complexity class `NTIME(T)`, the
class **NP** of languages decidable by a nondeterministic TM in polynomial time,
and **coNP** as the complement class (Arora-Barak Definitions 2.1, 2.14).
-/

/-- `NTIME(T)` is the class of languages decidable by a nondeterministic TM in
    time `T(n)` (Arora-Barak Definition 2.1). The machine may have any number
    of work tapes. -/
def NTIME (T : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : NTM k), tm.DecidesInTime L T}

/-- **NP** is the class of languages decidable by a nondeterministic TM in
    polynomial time: `NP = ∪_T NTIME(T)` over polynomially bounded `T`
    (Arora-Barak Definition 2.1). -/
def NP : Set Language :=
  {L | ∃ (T : ℕ → ℕ), IsPolyBounded T ∧ L ∈ NTIME T}

/-- **coNP** is the class of languages whose complements are in NP
    (Arora-Barak Definition 2.14). -/
def CoNP : Set Language :=
  {L | Lᶜ ∈ NP}
