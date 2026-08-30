/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.NP
public import Complexitylib.Classes.Containments

/-!
# `PSPACE ⊆ NPSPACE`

⚠️ Unreviewed by Bolton

Deterministic polynomial space is contained in nondeterministic polynomial space.

This direction is immediate: a deterministic decider is a nondeterministic one whose two
transition functions agree, so each `DSPACE` level embeds in the corresponding `NSPACE` level.
The converse is Savitch's theorem — see `NPSPACESubsetPSPACE`.
-/

@[expose] public section

namespace Complexity

/-- **`PSPACE ⊆ NPSPACE`**: every deterministic space-bounded decider is a nondeterministic
one, level by level. -/
theorem PSPACE_subset_NPSPACE : PSPACE ⊆ NPSPACE := by
  intro L hL
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hL
  exact Set.mem_iUnion.mpr ⟨k, DSPACE_subset_NSPACE _ hk⟩

end Complexity
