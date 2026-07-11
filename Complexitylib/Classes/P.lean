import Complexitylib.Classes.P.Defs
import Complexitylib.Classes.P.Internal

namespace Complexity

/-!
# P — surface layer

This file aggregates the definitions and theorems for DTIME, P, DSPACE, and PSPACE.

## Definitions (from `P/Defs.lean`)

- `DTIME` — deterministic time complexity class (AB Definition 1.6)
- `P` — polynomial time: `⋃ k, DTIME(n^k)`
- `FP` — functions computable in polynomial time
- `DSPACE` — deterministic space complexity class
- `NSPACE` — nondeterministic space complexity class
- `PSPACE` — polynomial space: `⋃ k, DSPACE(n^k)`

## Theorems

- `DTIME_union` — DTIME is closed under union (AB Claim 1.5)
-/

open Complexity

/-- **DTIME is closed under union** (AB Claim 1.5): if `L₁ ∈ DTIME(T₁)` and
    `L₂ ∈ DTIME(T₂)`, then `L₁ ∪ L₂ ∈ DTIME(T₁ + T₂)`. -/
theorem DTIME_union {T₁ T₂ : ℕ → ℕ} {L₁ L₂ : Language}
    (h₁ : L₁ ∈ DTIME T₁) (h₂ : L₂ ∈ DTIME T₂) :
    L₁ ∪ L₂ ∈ DTIME (fun n => T₁ n + T₂ n) := by
  obtain ⟨k₁, tm₁, f₁, hd₁, ho₁⟩ := h₁
  obtain ⟨k₂, tm₂, f₂, hd₂, ho₂⟩ := h₂
  exact ⟨k₁ + 1 + k₂, TM.unionTM tm₁ tm₂, fun n => 10 * f₁ n + f₂ n,
    TM.unionTM_decidesInTime hd₁ hd₂,
    bigO_union_bound ho₁ ho₂⟩

end Complexity
