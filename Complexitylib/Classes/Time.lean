import Complexitylib.Models.TuringMachine
import Complexitylib.Asymptotics

/-!
# Base time complexity classes

This file defines the parametric time complexity classes `DTIME(T)` and
`NTIME(T)`, the building blocks from which polynomial, exponential, and
randomized time classes are derived.

Both use `=O` (Mathlib's `IsBigO` lifted to `ℕ → ℕ`) to express asymptotic
bounds.
-/

open Complexity

/-- `DTIME(T)` is the class of languages decidable by a deterministic TM in
    time `O(T(n))` (AB Definition 1.6). The machine may have any number of
    work tapes. -/
def DTIME (T : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : TM k) (f : ℕ → ℕ),
    tm.DecidesInTime L f ∧ f =O T}

/-- `NTIME(T)` is the class of languages decidable by a nondeterministic TM in
    time `O(T(n))` (AB Definition 2.1). The machine may have any number of
    work tapes. -/
def NTIME (T : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : NTM k) (f : ℕ → ℕ),
    tm.DecidesInTime L f ∧ f =O T}
