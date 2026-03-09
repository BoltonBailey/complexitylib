import Complexitylib.Models.TuringMachine
import Complexitylib.Asymptotics

/-!
# Base complexity classes

This file defines the parametric complexity classes `DTIME(T)`, `DSPACE(S)`,
`NSPACE(S)`, the derived classes **P**, **PSPACE**, and the function class
**FP**.

All parameterized classes use `=O` (Mathlib's `IsBigO` lifted to `ℕ → ℕ`)
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

/-- `DSPACE(S)` is the class of languages decidable by a deterministic TM using
    `O(S(n))` space on work tapes. -/
def DSPACE (S : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : TM k) (f : ℕ → ℕ),
    tm.DecidesInSpace L f ∧ f =O S}

/-- `NSPACE(S)` is the class of languages decidable by a nondeterministic TM
    using `O(S(n))` space on work tapes. -/
def NSPACE (S : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : NTM k) (f : ℕ → ℕ),
    tm.DecidesInSpace L f ∧ f =O S}

/-- **PSPACE** is the class of languages decidable by a deterministic TM using
    polynomial space on work tapes: `PSPACE = ⋃_k DSPACE(n^k)`. -/
def PSPACE : Set Language :=
  ⋃ k : ℕ, DSPACE (· ^ k)
