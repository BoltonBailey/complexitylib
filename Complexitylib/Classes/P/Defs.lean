import Complexitylib.Classes.Time
import Complexitylib.Classes.Space

namespace Complexity

/-!
# P, FP, and PSPACE

This file defines **P** (polynomial time), **FP** (polynomial-time functions),
and **PSPACE** (polynomial space) in terms of the base classes `DTIME` and
`DSPACE`.
-/

open Complexity

/-- **P** is the class of languages decidable by a deterministic TM in
    polynomial time: `P = ⋃_k DTIME(n^k)`. -/
def P : Set Language :=
  ⋃ k : ℕ, DTIME (· ^ k)

/-- **FP** is the class of functions computable by a deterministic TM in
    polynomial time. -/
def FP : Set (List Bool → List Bool) :=
  {f | ∃ (d k : ℕ) (tm : TM k) (T : ℕ → ℕ),
    tm.ComputesInTime f T ∧ T =O (· ^ d)}

/-- **PSPACE** is the class of languages decidable by a deterministic TM using
    polynomial space on work tapes: `PSPACE = ⋃_k DSPACE(n^k)`. -/
def PSPACE : Set Language :=
  ⋃ k : ℕ, DSPACE (· ^ k)

end Complexity
