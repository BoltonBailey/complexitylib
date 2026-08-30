/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Kolmogorov.Defs

/-!
# Computational depth -- definitions

The `time`-bounded computational depth of `output` relative to a machine is the
description-length gap `C_M^time(output) - C_M(output)`. Because this library
allows either complexity to be `⊤`, `descriptionDifference` returns `⊤` if
either operand is infinite and otherwise embeds the natural-number difference.
The proof layer establishes the required order `C_M ≤ C_M^time` before using
the natural subtraction identity.
-/


@[expose] public section

namespace Complexity

/-- Difference of two finite extended-natural description lengths. If either
length is infinite, the difference is infinite rather than silently defaulting
to zero. -/
def descriptionDifference (upper lower : WithTop ℕ) : WithTop ℕ :=
  upper.recTopCoe ⊤ fun upperValue =>
    lower.recTopCoe ⊤ fun lowerValue =>
      (upperValue - lowerValue : ℕ)

namespace TM

variable {n : ℕ}

/-- Machine-relative `time`-bounded computational depth:
`C_M^time(output) - C_M(output)`. -/
noncomputable def computationalDepth (machine : TM n)
    (output : List Bool) (time : ℕ) : WithTop ℕ :=
  descriptionDifference
    (machine.timeBoundedKolmogorovComplexity output time)
    (machine.plainKolmogorovComplexity output)

end TM

end Complexity
