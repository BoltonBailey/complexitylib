/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Complexitylib.Classes.P.TakeLen.Internal

/-!
# Polynomial-time truncation to a ruler length

`Complexity.takeLen` (with its defining equation `takeLen_pair`) is defined in
`Complexitylib.Classes.P.TakeLen.Defs`; this file records that it is
polynomial-time.

## Main result

- `takeLen_mem_FP` — the truncation is polynomial-time computable
-/


@[expose] public section

namespace Complexity

/-- Truncating the suffix of a pair to the length of its leading block is a
polynomial-time string function, via the one-work-tape transducer `takeLenTM`
(count the ruler into unary marks, rewind, then copy one symbol per mark). -/
theorem takeLen_mem_FP : takeLen ∈ FP :=
  takeLen_mem_FP_internal

end Complexity
