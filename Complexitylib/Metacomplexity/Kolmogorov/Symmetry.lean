/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Kolmogorov.Symmetry.Defs
public import Complexitylib.Metacomplexity.Kolmogorov.Symmetry.Internal

/-!
# Time-bounded symmetry of information

This module exposes a non-vacuous machine-relative version of Hirahara's SoI
hypothesis. The lower-chain inequality is separate from the unconditional upper
chain rule: SoI is a substantive hypothesis, while upper composition follows
from an evaluator contract.

The polynomial package quantifies an identity-dominating, polynomially bounded
clock and retains an explicit additive constant next to its base-two logarithmic
loss. Later results must instantiate the ordinary and conditional evaluators;
no universality or Heuristica consequence is assumed here.
-/


public section

namespace Complexity

/-- The identity transform is an admissible Kolmogorov clock. -/
theorem isAdmissibleKolmogorovClock_id :
    IsAdmissibleKolmogorovClock id :=
  isAdmissibleKolmogorovClock_id_internal

/-- Non-vacuous SoI forces the transformed conditional description to exist on
every admissible pair. -/
theorem TimeBoundedSymmetryOfInformation.conditional_ne_top
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {clock loss : ℕ → ℕ}
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine clock loss)
    {first condition : List Bool} {time : ℕ}
    (hsize : first.length + condition.length ≤ time) :
    conditionalMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
      first condition (clock time) ≠ ⊤ :=
  hsoi.conditional_ne_top_internal hsize

/-- Non-vacuous SoI also forces the transformed ordinary description of the
condition to exist. -/
theorem TimeBoundedSymmetryOfInformation.condition_ne_top
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {clock loss : ℕ → ℕ}
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine clock loss)
    {first condition : List Bool} {time : ℕ}
    (hsize : first.length + condition.length ≤ time) :
    ordinaryMachine.timeBoundedKolmogorovComplexity
      condition (clock time) ≠ ⊤ :=
  hsoi.condition_ne_top_internal hsize

/-- Increasing the permitted loss preserves a fixed-clock SoI theorem. -/
theorem TimeBoundedSymmetryOfInformation.weaken_loss
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {clock firstLoss secondLoss : ℕ → ℕ}
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine clock firstLoss)
    (hloss : ∀ time, firstLoss time ≤ secondLoss time) :
    TimeBoundedSymmetryOfInformation ordinaryMachine conditionalMachine
      clock secondLoss :=
  hsoi.weaken_loss_internal hloss

/-- Giving both left-hand descriptions more time preserves SoI. -/
theorem TimeBoundedSymmetryOfInformation.weaken_clock
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {firstClock secondClock loss : ℕ → ℕ}
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine firstClock loss)
    (hclock : ∀ time, firstClock time ≤ secondClock time) :
    TimeBoundedSymmetryOfInformation ordinaryMachine conditionalMachine
      secondClock loss :=
  hsoi.weaken_clock_internal hclock

/-- Any polynomial SoI witness remains valid at an admissible larger clock,
with the logarithmic loss recalculated at that clock. The premise quantifies
over witnesses because the existential clock is intentionally opaque. -/
theorem PolynomialTimeBoundedSymmetryOfInformation.enlarge_clock
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    (hsoi : PolynomialTimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine)
    {largerClock : ℕ → ℕ}
    (hlargerAdmissible : IsAdmissibleKolmogorovClock largerClock)
    (hlarger : ∀ clock additive,
      IsAdmissibleKolmogorovClock clock →
      TimeBoundedSymmetryOfInformation ordinaryMachine conditionalMachine clock
        (fun time => Nat.log 2 (clock time) + additive) →
      ∀ time, clock time ≤ largerClock time) :
    IsAdmissibleKolmogorovClock largerClock ∧
      ∃ additive,
        TimeBoundedSymmetryOfInformation ordinaryMachine conditionalMachine
          largerClock (fun time => Nat.log 2 (largerClock time) + additive) :=
  hsoi.enlarge_clock_internal hlargerAdmissible hlarger

end Complexity
