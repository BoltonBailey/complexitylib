/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Defs
public import Complexitylib.Classes.PCP.Internal.AlgPCP
public import Complexitylib.Classes.PCP.Internal.SubsetNPFinal

/-!
# The PCP theorem

`PCP r q` and its verifiers are defined in `Complexitylib.Classes.PCP.Defs`;
this file states and proves the theorem itself.

Both inclusions are hard work. `NP ⊆ PCP[O(log n), O(1)]` is Dinur's gap
amplification, carried out by the modules under `PCP/Internal`: a formula
becomes a constraint graph, the graph is amplified logarithmically many times
until its unsatisfiability value is a constant, and a verifier reads one edge of
the result. `PCP[O(log n), O(1)] ⊆ NP` guesses the whole proof table.

## Main results

- `Complexity.PCP_theorem` — `NP = PCP[O(log n), O(1)]`
-/

@[expose] public section

namespace Complexity

/-! ## The PCP theorem -/

/-- **The PCP theorem**, as stated on
<https://en.wikipedia.org/wiki/PCP_theorem>: `NP = PCP[O(log n), O(1)]`. The
big-O classes are unions over all functions `r =O log` and `q =O 1` in the
library's `BigO` (eventual domination up to a constant), with the randomness
bound required to be `Constructible` — see that definition for why the
requirement cannot be dropped. -/
theorem PCP_theorem :
    NP = ⋃ (r : ℕ → ℕ) (_ : r =O Nat.log 2) (_ : Constructible r)
      (q : ℕ → ℕ) (_ : q =O fun _ => 1), PCP r q := by
  ext L
  simp only [Set.mem_iUnion, exists_prop]
  exact ⟨exists_pcp_of_mem_NP,
    fun ⟨_, hrlog, hrc, _, hq1, hmem⟩ => PCP_subset_NP hrc hrlog hq1 hmem⟩

end Complexity
