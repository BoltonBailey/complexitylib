/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.P.Defs
import Complexitylib.Classes.P.Internal
import Complexitylib.Models.TuringMachine.Subroutines.CopyOutput

/-!
# P — surface layer

This file aggregates the definitions and theorems for P, FP, and PSPACE.

## Definitions (from `P/Defs.lean`)

- `P` — polynomial time: `⋃ k, DTIME(n^k)`
- `FP` — functions computable in polynomial time
- `PSPACE` — polynomial space: `⋃ k, DSPACE(n^k)`

## Theorems

- `DTIME_union` — DTIME is closed under union (AB Claim 1.5)
- `id_mem_FP` — the identity function is computable in linear time
-/

namespace Complexity


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

/-- **The identity function belongs to `FP`.** The executable
    `copyInputToOutputTM` copies the input to the output in `n + 2` steps, and
    this concrete bound is linear. -/
theorem id_mem_FP : id ∈ FP := by
  refine ⟨1, 0, TM.copyInputToOutputTM, (fun n => n + 2), ?_, ?_⟩
  · exact TM.copyInputToOutputTM_computesInTime 0
  · have hn : (fun n : ℕ => n) =O (· ^ 1) := by
      simpa [pow_one] using BigO.refl (fun n : ℕ => n)
    exact BigO.add hn (BigO.const_le_pow 2 1)

end Complexity
