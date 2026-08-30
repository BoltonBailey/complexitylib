/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Gap.Defs

/-!
# Difference estimators for conditional gap MinKT -- definitions

Hirahara's Proposition 6.2 estimates conditional complexity by subtracting an
estimate for the condition from an estimate for the joint string, together
with a logarithmic centering correction. This module isolates the numerical
shape

`B = minuend - subtrahend - correction`

from the later construction of those components.

`SatisfiesAccounting` states the two inequalities before cancellation. Its
proof layer shows that natural truncated subtraction is sound under precisely
those inequalities and produces the `GapMINCKT.Estimator.SatisfiesBounds`
sandwich required by the promise solver.
-/


@[expose] public section

namespace Complexity

namespace GapMINCKT

/-- Three numerical components of a threshold-free conditional estimator. -/
structure DifferenceEstimator where
  /-- Joint-string estimate, the minuend of the difference. -/
  minuend : MINCKT.Instance → ℕ
  /-- Condition-only estimate subtracted from the joint estimate. -/
  subtrahend : MINCKT.Instance → ℕ
  /-- Explicit centering/rounding correction subtracted last. -/
  correction : MINCKT.Instance → ℕ

namespace DifferenceEstimator

/-- The natural-valued adjusted difference used as a conditional estimate. -/
def estimate (components : DifferenceEstimator) : Estimator :=
  fun inst =>
    components.minuend inst - components.subtrahend inst -
      components.correction inst

/-- The two pre-cancellation inequalities needed to validate the adjusted
difference.

The upper inequality leaves the subtrahend and correction on the right of the
desired source-complexity bound. The lower inequality leaves the same terms on
the left of the transformed-complexity bound. Cancellation then yields exactly
the conditional estimator sandwich. -/
structure SatisfiesAccounting {ordinaryTapes conditionalTapes : ℕ}
    (components : DifferenceEstimator)
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters) : Prop where
  /-- Pre-cancellation upper bound. -/
  upper : ∀ inst : MINCKT.Instance,
    (components.minuend inst : WithTop ℕ) ≤
      inst.complexity conditionalMachine +
          ordinaryMachine.computationalDepthBetween inst.condition inst.time
            (parameters.transformedTime inst) +
        (components.subtrahend inst + components.correction inst : ℕ)
  /-- Pre-cancellation lower bound. -/
  lower : ∀ inst : MINCKT.Instance,
    (inst.withTime (parameters.transformedTime inst)).complexity
          conditionalMachine +
        (components.subtrahend inst + components.correction inst : ℕ) ≤
      (components.minuend inst + parameters.logarithmicSlack inst : ℕ)

end DifferenceEstimator

end GapMINCKT

end Complexity
