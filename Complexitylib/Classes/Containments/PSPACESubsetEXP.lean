/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.PSPACESubsetEXP

/-!
# `PSPACE ⊆ EXP`

⚠️ Unreviewed by Bolton

Polynomial space is contained in exponential time.

A machine using space `S(n)` has only `2^O(S(n))` configurations that respect its space bound, so
a deterministic run visits each at most once before halting: a repeat would make the run periodic
and pull an earlier halt, contradicting minimality. The halting time is therefore bounded by the
configuration count, and the *same machine* — no simulation is needed — decides the language in
exponential time.

The proof is in `Complexitylib.Classes.Containments.Internal.PSPACESubsetEXP`. Its one subtlety
is that `Cfg.WithinDecisionSpace` bounds head *positions* but says nothing about tape *contents*;
`TM.Windowed` supplies the missing invariant — a head that never leaves the window can never write
outside it — which is what makes the configuration count finite.

## Main results

- `PSPACE_subset_EXP` — the containment
-/

@[expose] public section

namespace Complexity

/-- **`PSPACE ⊆ EXP`**: a space-bounded machine halts within its configuration count. -/
theorem PSPACE_subset_EXP : PSPACE ⊆ EXP := PSPACE_subset_EXP_internal

end Complexity
