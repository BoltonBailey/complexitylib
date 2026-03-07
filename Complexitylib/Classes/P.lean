import Complexitylib.Models.TuringMachine
import Complexitylib.Asymptotics

/-!
# DTIME, P, and FP

This file defines the deterministic time complexity class `DTIME(T)`, the
class **P** of languages decidable in polynomial time, and the function class
**FP** of functions computable in polynomial time.

Time-parameterized classes use `=O` (Mathlib's `IsBigO` lifted to `ℕ → ℕ`)
to express asymptotic bounds, following standard complexity-theoretic
conventions (see https://complexityzoo.net/Complexity_Zoo).
-/

open Complexity

/-- `DTIME(T)` is the class of languages decidable by a deterministic TM in
    time `O(T(n))` (AB Definition 1.6). The machine may have any number of
    work tapes. -/
def DTIME (T : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : TM k) (f : ℕ → ℕ),
    tm.DecidesInTime L f ∧ f =O T}

/-- **P** is the class of languages decidable by a deterministic TM in
    polynomial time: `P = ⋃_k DTIME(n^k)`. -/
def P : Set Language :=
  ⋃ k : ℕ, DTIME (· ^ k)

/-- **FP** is the class of functions computable by a deterministic TM in
    polynomial time. -/
def FP : Set (List Bool → List Bool) :=
  {f | ∃ (d k : ℕ) (tm : TM k) (T : ℕ → ℕ),
    tm.ComputesInTime f T ∧ T =O (· ^ d)}
