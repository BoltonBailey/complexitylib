/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Kolmogorov.Defs

/-!
# Computational depth -- definitions

The two-clock computational depth of `output` relative to a machine is the gap
`C_M^first(output) - C_M^later(output)`, where `first ≤ later`. Taking the
second clock to infinity gives the usual one-clock gap
`C_M^time(output) - C_M(output)`.

Because this library allows a complexity to be `⊤`, `descriptionDifference`
returns `⊤` if either operand is infinite and otherwise embeds the
natural-number difference. The proof layer establishes the required complexity
order before using natural subtraction.
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

/-- Machine-relative two-clock computational depth:
`C_M^firstTime(output) - C_M^laterTime(output)`. Its exact laws require
`firstTime ≤ laterTime`. -/
noncomputable def computationalDepthBetween (machine : TM n)
    (output : List Bool) (firstTime laterTime : ℕ) : WithTop ℕ :=
  descriptionDifference
    (machine.timeBoundedKolmogorovComplexity output firstTime)
    (machine.timeBoundedKolmogorovComplexity output laterTime)

/-- Machine-relative `time`-bounded computational depth:
`C_M^time(output) - C_M(output)`. -/
noncomputable def computationalDepth (machine : TM n)
    (output : List Bool) (time : ℕ) : WithTop ℕ :=
  descriptionDifference
    (machine.timeBoundedKolmogorovComplexity output time)
    (machine.plainKolmogorovComplexity output)

end TM

end Complexity
