/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Complexitylib.Classes.P.Reverse.Internal

/-!
# Polynomial-time string reversal

## Main result

- `reverse_mem_FP` — `x ↦ x.reverse` is polynomial-time computable

Reversal is what lets an iterative loop consume a string in the order a
right-to-left structural recursion needs: recursion on notation peels the *head*
of a string, so evaluating it bottom-up processes the *last* bit first.
-/


@[expose] public section

namespace Complexity

/-- Reversing a bitstring is a polynomial-time string function, via the
one-work-tape transducer `reverseTM` (copy right, then sweep back emitting). -/
theorem reverse_mem_FP : (fun x : List Bool => x.reverse) ∈ FP :=
  reverse_mem_FP_internal

end Complexity
