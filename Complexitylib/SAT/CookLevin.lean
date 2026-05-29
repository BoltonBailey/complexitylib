import Complexitylib.SAT.Headline
import Complexitylib.Classes.NP.Reduction

/-!
# Cook–Levin: SAT is NP-complete

This file assembles the **Cook–Levin theorem**, `SAT.NPComplete_L_SAT`:
`L_SAT` is NP-complete. Membership `L_SAT ∈ NP` is `SAT.L_SAT_mem_NP`
(`SAT/Headline.lean`); NP-hardness is the content here.

## Architecture

The hard direction is `cookLevin_reduction`: given a nondeterministic TM `N`
deciding a language `L` within a polynomial time bound, every input `x` is
mapped to (the encoding of) a CNF formula `φ_x` — the **computation-tableau
formula** — that is satisfiable iff `N` has an accepting computation on `x`
within the time bound, i.e. iff `x ∈ L`. The map `x ↦ φ_x.encode` is itself
polynomial-time computable (`∈ FP`), giving `L ≤ₚ L_SAT`.

`NPHard_L_SAT` then unpacks an arbitrary `L ∈ NP` to such an `N` and applies
`cookLevin_reduction`; `NPComplete_L_SAT` combines this with `L_SAT_mem_NP`.

The tableau construction, its satisfiability characterization, and its
`FP`-computability are the remaining proof obligations behind
`cookLevin_reduction`.
-/

open Complexity

namespace SAT

/-- **Per-machine Cook–Levin reduction.** If a nondeterministic machine `N`
    decides `L` within a polynomial time bound `T` (`T =O (·^c)`), then `L`
    polynomial-time many-one reduces to `L_SAT`, via the computation-tableau
    formula. -/
theorem cookLevin_reduction {k : ℕ} {L : Language} (N : NTM k) (T : ℕ → ℕ) (c : ℕ)
    (hdec : N.DecidesInTime L T) (hTO : T =O (· ^ c)) :
    L ≤ₚ L_SAT := by
  sorry

/-- **NP-hardness of SAT.** Every language in `NP` polynomial-time reduces to
    `L_SAT`. -/
theorem NPHard_L_SAT : NPHard L_SAT := by
  intro L hL
  obtain ⟨d, hLd⟩ := Set.mem_iUnion.mp hL
  obtain ⟨k, N, f, hdec, hfO⟩ := hLd
  exact cookLevin_reduction N f d hdec hfO

/-- **Cook–Levin theorem: SAT is NP-complete.** -/
theorem NPComplete_L_SAT : NPComplete L_SAT :=
  ⟨L_SAT_mem_NP, NPHard_L_SAT⟩

end SAT
