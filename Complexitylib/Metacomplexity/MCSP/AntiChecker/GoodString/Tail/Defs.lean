/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.GoodString.Defs

/-!
# Good-string binomial-tail bound -- definitions
-/


@[expose] public section

namespace Complexity

namespace AntiChecker

/-- Elementary upper bound for the number of length-`arity` survivor tuples
caught when `disagreements` of `survivors` codes disagree at an input. -/
def caughtTupleUpperBound
    (arity survivors disagreements : ℕ) : ℕ :=
  2 ^ arity * disagreements ^ (arity - arity / 2) *
    survivors ^ (arity / 2)

end AntiChecker

end Complexity
