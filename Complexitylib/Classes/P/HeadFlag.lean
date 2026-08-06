/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.HeadFlag.Internal

/-!
# Polynomial-time leading-bit test

## Main result

- `headFlag_mem_FP` — `Complexity.headFlag` is polynomial-time computable
-/


@[expose] public section

namespace Complexity

/-- **A bit test, as a length.** -/
theorem headFlag_mem_FP (target : Bool) : headFlag target ∈ FP :=
  ⟨1, 0, headFlagTM target, (fun _ => 2), headFlagTM_computesInTime target,
    BigO.const_le_pow 2 1⟩

end Complexity
