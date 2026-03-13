import Complexitylib.Classes.Time
import Complexitylib.Classes.Space

/-!
# NP, coNP, and NPSPACE

This file defines **NP** (nondeterministic polynomial time), **coNP**, and
**NPSPACE** (nondeterministic polynomial space) in terms of the base classes
`NTIME` and `NSPACE`.
-/

/-- **NP** is the class of languages decidable by a nondeterministic TM in
    polynomial time: `NP = ⋃_k NTIME(n^k)`. -/
def NP : Set Language :=
  ⋃ k : ℕ, NTIME (· ^ k)

/-- **coNP** is the class of languages whose complements are in NP. -/
def CoNP : Set Language :=
  {L | Lᶜ ∈ NP}

/-- **NPSPACE** is the class of languages decidable by a nondeterministic TM
    using polynomial space on work tapes: `NPSPACE = ⋃_k NSPACE(n^k)`. -/
def NPSPACE : Set Language :=
  ⋃ k : ℕ, NSPACE (· ^ k)
