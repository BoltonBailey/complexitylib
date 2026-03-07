import Complexitylib.Models.TuringMachine
import Complexitylib.Asymptotics

/-!
# NTIME, NP, and coNP

This file defines the nondeterministic time complexity class `NTIME(T)`, the
class **NP** of languages decidable by a nondeterministic TM in polynomial time,
and **coNP** as the complement class.
-/

open Complexity

/-- `NTIME(T)` is the class of languages decidable by a nondeterministic TM in
    time `O(T(n))` (AB Definition 2.1). The machine may have any number of
    work tapes. -/
def NTIME (T : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : NTM k) (f : ℕ → ℕ),
    tm.DecidesInTime L f ∧ f =O T}

/-- **NP** is the class of languages decidable by a nondeterministic TM in
    polynomial time: `NP = ⋃_k NTIME(n^k)`. -/
def NP : Set Language :=
  ⋃ k : ℕ, NTIME (· ^ k)

/-- **coNP** is the class of languages whose complements are in NP. -/
def CoNP : Set Language :=
  {L | Lᶜ ∈ NP}
