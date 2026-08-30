/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Promise.Defs
public import Complexitylib.Metacomplexity.MINKT.Gap.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Nat.Log

/-!
# Logarithmic-gap MINKT -- definitions

This is the exact machine-relative form of Hirahara's `Gap_tau MINKT` promise
from Definition 3.3 of *Symmetry of Information from Meta-Complexity* (CCC
2022). It reuses the canonical `(x, 1^t, 1^s)` codec from `GapMINKT`, but fixes
the promised sides to

- yes: `C^t(x) <= s`;
- no: `C^tau(x) > s + log_2(tau)`.

The existing general `GapMINKT.Parameters` remains useful for optimization
search with an arbitrary description transformation `sigma(n,s)`. This module
is separate because the paper's exact logarithmic loss depends on the source
clock through `tau(n,t)`.
-/


@[expose] public section

namespace Complexity

namespace GapMINKT

namespace Logarithmic

/-- The paper's two-argument clock transformation `tau(|x|,t)`. -/
structure Parameters where
  /-- Later primitive clock from output length and source clock. -/
  clock : ℕ → ℕ → ℕ

namespace Parameters

/-- The transformed clock never gives less time than the source clock. -/
def IsWidening (parameters : Parameters) : Prop :=
  ∀ outputLength time, time ≤ parameters.clock outputLength time

/-- One power of the total numeric input controls the clock transformation. -/
def IsPolynomiallyBounded (parameters : Parameters) : Prop :=
  ∃ coefficient exponent, ∀ outputLength time,
    parameters.clock outputLength time ≤
      coefficient * (outputLength + time + 1) ^ exponent

/-- A paper-level clock is admissible when it is widening and polynomially
bounded. Computability remains a separate implementation property. -/
structure IsAdmissible (parameters : Parameters) : Prop where
  /-- The target clock dominates the source clock. -/
  widening : parameters.IsWidening
  /-- The target clock has uniform polynomial growth. -/
  polynomiallyBounded : parameters.IsPolynomiallyBounded

/-- The identity transformation, giving the zero-blow-up boundary case. -/
def identity : Parameters where
  clock := fun _outputLength time => time

/-- Apply the clock transformation to a threshold-free MINKT instance. -/
def transformedTime (parameters : Parameters) (inst : MINKT.Instance) : ℕ :=
  parameters.clock inst.output.length inst.time

/-- Base-two logarithmic slack at the transformed clock. -/
def logarithmicSlack (parameters : Parameters) (inst : MINKT.Instance) : ℕ :=
  Nat.log 2 (parameters.transformedTime inst)

end Parameters

/-- A threshold-free numerical estimator for ordinary bounded complexity. -/
abbrev Estimator := MINKT.Instance → ℕ

/-- Fact 3.4's subtraction-free estimator sandwich:

`B(x,1^t) <= C^t(x)` and `C^tau(x) <= B(x,1^t) + log_2(tau)`.
-/
def Estimator.SatisfiesBounds {tapes : ℕ} (estimate : Estimator)
    (machine : TM tapes) (parameters : Parameters) : Prop :=
  ∀ inst : MINKT.Instance,
    (estimate inst : WithTop ℕ) ≤
        machine.timeBoundedKolmogorovComplexity inst.output inst.time ∧
      machine.timeBoundedKolmogorovComplexity inst.output
          (parameters.transformedTime inst) ≤
        (estimate inst + parameters.logarithmicSlack inst : ℕ)

/-- The estimator sandwich restricted to an explicit set of inputs.

Hirahara's Fact 3.4 uses the domain `|x| <= t`. Keeping the domain explicit
lets the machine-relative library state that version without pretending that
an arbitrary machine can print every output at every tiny clock. -/
def Estimator.SatisfiesBoundsOn {tapes : ℕ} (estimate : Estimator)
    (machine : TM tapes) (parameters : Parameters)
    (eligible : MINKT.Instance → Prop) : Prop :=
  ∀ inst : MINKT.Instance, eligible inst →
    (estimate inst : WithTop ℕ) ≤
        machine.timeBoundedKolmogorovComplexity inst.output inst.time ∧
      machine.timeBoundedKolmogorovComplexity inst.output
          (parameters.transformedTime inst) ≤
        (estimate inst + parameters.logarithmicSlack inst : ℕ)

/-- The input domain `|x| <= t` used in Fact 3.4. -/
def IsLengthWithinTime (inst : MINKT.Instance) : Prop :=
  inst.output.length ≤ inst.time

/-- Exact logarithmic no condition
`C^tau(x) > s + log_2(tau)`. -/
def IsNo {tapes : ℕ} (inst : GapMINKT.Instance) (machine : TM tapes)
    (parameters : Parameters) : Prop :=
  (inst.threshold + parameters.logarithmicSlack inst.base : ℕ) <
    machine.timeBoundedKolmogorovComplexity inst.output
      (parameters.transformedTime inst.base)

/-- A concrete program forbidden by the exact logarithmic no condition. -/
def IsRelaxedWitness {tapes : ℕ} (inst : GapMINKT.Instance)
    (machine : TM tapes) (parameters : Parameters)
    (program : List Bool) : Prop :=
  program.length ≤ inst.threshold + parameters.logarithmicSlack inst.base ∧
    machine.ProducesInTime program inst.output
      (parameters.transformedTime inst.base)

/-- The yes language is exactly the existing source-threshold language. -/
def yesLanguage {tapes : ℕ} (machine : TM tapes) : Language :=
  GapMINKT.yesLanguage machine

/-- Canonically encoded exact logarithmic no language. -/
def noLanguage {tapes : ℕ} (machine : TM tapes)
    (parameters : Parameters) : Language :=
  {bits | match GapMINKT.Instance.decode? bits with
    | some inst => IsNo inst machine parameters
    | none => False}

/-- Total completion obtained by thresholding a numerical estimator. -/
def estimatorLanguage (estimate : Estimator) : Language :=
  {bits | match GapMINKT.Instance.decode? bits with
    | some inst => estimate inst.base ≤ inst.threshold
    | none => False}

/-- Executable thresholding of an ordinary bounded-complexity estimator. -/
def decisionOfEstimator (estimate : Estimator) : List Bool → Bool :=
  fun bits => match GapMINKT.Instance.decode? bits with
    | some inst => decide (estimate inst.base ≤ inst.threshold)
    | none => false

/-- Add a description threshold to a threshold-free MINKT instance. -/
def thresholdInstance (inst : MINKT.Instance) (threshold : ℕ) :
    GapMINKT.Instance where
  output := inst.output
  time := inst.time
  threshold := threshold

/-- Search the finite interval `[0,cap]` for the first threshold accepted by a
Boolean promise solver. If the solver accepts none of them, return `cap`.

The fallback makes the operation total. Correctness theorems use an accepted
upper bound, so the fallback branch is then unreachable. -/
def firstAcceptedThreshold (decide : List Bool → Bool)
    (inst : MINKT.Instance) (cap : ℕ) : ℕ :=
  match Fin.find? fun threshold : Fin (cap + 1) =>
      decide (thresholdInstance inst threshold.val).encode with
  | some threshold => threshold.val
  | none => cap

/-- Turn a gap solver into a numerical estimator by bounded threshold search. -/
def estimatorOfSolver (decide : List Bool → Bool)
    (cap : MINKT.Instance → ℕ) : Estimator :=
  fun inst => firstAcceptedThreshold decide inst (cap inst)

/-- The canonical Fact 3.4 search uses the unary source clock as its threshold
cap. Every finite source complexity is at most this value by input locality. -/
def timeSearchEstimator (decide : List Bool → Bool) : Estimator :=
  estimatorOfSolver decide fun inst => inst.time

end Logarithmic

end GapMINKT

end Complexity
