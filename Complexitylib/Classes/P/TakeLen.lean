/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Complexitylib.Classes.P.TakeLen.Internal

/-!
# Polynomial-time truncation to a ruler length

`takeLen (pair c y) = y.take |c|`: the leading self-delimiting block is a
*ruler* and the verbatim suffix is truncated to its length.

Carrying the width bound as a string rather than as a number is what makes an
iterated `FP` step function polynomial-time: each iteration truncates its state
to the ruler, so no intermediate value can grow beyond it, and the clamp itself
costs only linear time.

## Main results

- `takeLen_pair` — the defining equation on genuine pairs
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
