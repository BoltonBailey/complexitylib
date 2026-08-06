/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Mathlib.Data.List.Basic

/-!
# Testing a leading bit — definition

Every other `FP` primitive in this library — `Complexity.takeLen`,
`List.reverse`, `Complexity.pair`, `Cobham.mulUnpair` — fixes its output's
*length* from its inputs' lengths alone, so none of them can react to a bit's
value. `Complexity.headFlag` closes that gap by turning a bit test into a
length: the answer is carried by whether the result is empty.
-/


@[expose] public section

namespace Complexity

/-- `[false]` when `x` begins with `target`, and `[]` otherwise: a bit test whose
answer is carried by the *length* of the result. -/
def headFlag (target : Bool) (x : List Bool) : List Bool :=
  if x.head? = some target then [false] else []

end Complexity
