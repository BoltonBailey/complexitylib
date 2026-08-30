/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Kolmogorov.Chain.Defs
public import Mathlib.Algebra.Order.Monoid.WithTop
public import Mathlib.Data.Nat.Log

/-!
# Time-bounded symmetry of information -- definitions

Hirahara's time-bounded symmetry-of-information hypothesis has the lower-chain
form

`C_cond^{p(t)}(x | y) + C^{p(t)}(y) <= C^t(pair x y) + log p(t)`.

This layer makes the ordinary machine, random-access conditional machine,
canonical pair codec, transformed clock, and loss function explicit. Because
the machines are arbitrary rather than implicitly universal, the fixed-clock
hypothesis also requires the joint bounded complexity to be finite. This
prevents an incapable joint machine from satisfying the inequality vacuously
through `top`.
-/


@[expose] public section

namespace Complexity

/-- A clock suitable for the polynomial time-bounded SoI package dominates the
original clock and has a uniform polynomial upper bound. -/
structure IsAdmissibleKolmogorovClock (clock : ℕ → ℕ) : Prop where
  /-- The transformed clock never gives less time than the source clock. -/
  dominates : ∀ time, time ≤ clock time
  /-- One power bound controls the transformed clock at every input. -/
  polynomiallyBounded : ∃ coefficient exponent, ∀ time,
    clock time ≤ coefficient * (time + 1) ^ exponent

/-- Machine-relative time-bounded symmetry of information for a fixed clock
transform and loss. The first conjunct is a non-vacuity condition needed when
the ordinary machine is not yet known to be universal. -/
structure TimeBoundedSymmetryOfInformation
    {ordinaryTapes conditionalTapes : ℕ}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (clock loss : ℕ → ℕ) : Prop where
  /-- Every admissible paired instance has a bounded description. -/
  pairFinite : ∀ first condition time,
    first.length + condition.length ≤ time →
    ordinaryMachine.timeBoundedKolmogorovComplexity
      (pair first condition) time ≠ ⊤
  /-- The lower-chain inequality at the transformed clock. -/
  chain_le : ∀ first condition time,
    first.length + condition.length ≤ time →
    conditionalMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
            first condition (clock time) +
        ordinaryMachine.timeBoundedKolmogorovComplexity
          condition (clock time) ≤
      ordinaryMachine.timeBoundedKolmogorovComplexity
          (pair first condition) time + (loss time : WithTop ℕ)

/-- The polynomial/logarithmic SoI package. An additive loss constant remains
explicit because the machines and codecs are explicit; it cannot be hidden by
silently changing the universal evaluator. -/
def PolynomialTimeBoundedSymmetryOfInformation
    {ordinaryTapes conditionalTapes : ℕ}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes) : Prop :=
  ∃ clock additive,
    IsAdmissibleKolmogorovClock clock ∧
    TimeBoundedSymmetryOfInformation ordinaryMachine conditionalMachine clock
      (fun time => Nat.log 2 (clock time) + additive)

end Complexity
