/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Promise.Defs
public import Complexitylib.Metacomplexity.Kolmogorov.Depth.Defs
public import Complexitylib.Metacomplexity.MINCKT.Defs
public import Mathlib.Data.Nat.Log

/-!
# Gap conditional MinKT -- definitions

This is the machine-relative form of Hirahara's `Gap_tau MINcKT` promise from
Definition 6.1 of *Symmetry of Information from Meta-Complexity* (CCC 2022).
For an instance `(x, y, 1^t, 1^s)`, write
`t' = tau(|x|, |y|, t)`. The promised sides are

- yes: `C_cond^t(x | y) + cd^(t,t')(y) <= s`;
- no: `C_cond^t'(x | y) > s + log_2(t')`.

The sum on the yes side is the natural-number-safe form of the paper's
`C_cond^t(x | y) <= s - cd^(t,t')(y)`: if the depth exceeds `s`, the yes
condition is false rather than relying on truncated subtraction.

The ordinary machine used for depth and the oracle machine used for conditional
complexity are explicit and may differ. Relating them to one paper-specific
universal evaluator is a later simulation theorem.
-/


@[expose] public section

namespace Complexity

namespace GapMINCKT

/-- The three-argument clock transformation `tau(|x|, |y|, t)`. -/
structure Parameters where
  /-- Later primitive clock from output length, condition length, and source
  clock. -/
  clock : ℕ → ℕ → ℕ → ℕ

namespace Parameters

/-- The transformed clock never gives less time than the source clock. This is
the semantic condition needed to make the two promise sides disjoint. -/
def IsWidening (parameters : Parameters) : Prop :=
  ∀ outputLength conditionLength time,
    time ≤ parameters.clock outputLength conditionLength time

/-- One power of the total numeric input controls the clock transformation.
This records the polynomial-growth part of the paper's quantification over
`tau`; computability of the transform is a separate implementation property. -/
def IsPolynomiallyBounded (parameters : Parameters) : Prop :=
  ∃ coefficient exponent, ∀ outputLength conditionLength time,
    parameters.clock outputLength conditionLength time ≤
      coefficient * (outputLength + conditionLength + time + 1) ^ exponent

/-- An admissible paper-level clock is widening and polynomially bounded. -/
structure IsAdmissible (parameters : Parameters) : Prop where
  /-- The transformed clock dominates the source clock. -/
  widening : parameters.IsWidening
  /-- The transformed clock has uniform polynomial growth. -/
  polynomiallyBounded : parameters.IsPolynomiallyBounded

/-- The identity clock, useful as the zero-depth boundary case. -/
def identity : Parameters where
  clock := fun _outputLength _conditionLength time => time

/-- Apply the clock transformation to one threshold-free conditional MinKT
instance. -/
def transformedTime (parameters : Parameters) (inst : MINCKT.Instance) : ℕ :=
  parameters.clock inst.output.length inst.condition.length inst.time

/-- Base-two logarithmic error attached to the transformed clock. -/
def logarithmicSlack (parameters : Parameters) (inst : MINCKT.Instance) : ℕ :=
  Nat.log 2 (parameters.transformedTime inst)

end Parameters

/-- A threshold-free numerical estimator for conditional bounded complexity. -/
abbrev Estimator := MINCKT.Instance → ℕ

/-- The two-sided estimator sandwich used in Proposition 6.2:

`B(x,y,1^t) <= C^t(x|y) + cd^(t,tau)(y)` and
`C^tau(x|y) <= B(x,y,1^t) + log_2(tau)`.

Both inequalities use `WithTop` so a claimed estimator also certifies the
relevant descriptions are finite. -/
def Estimator.SatisfiesBounds {ordinaryTapes conditionalTapes : ℕ}
    (estimate : Estimator) (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters) : Prop :=
  ∀ inst : MINCKT.Instance,
    (estimate inst : WithTop ℕ) ≤
        inst.complexity conditionalMachine +
          ordinaryMachine.computationalDepthBetween inst.condition inst.time
            (parameters.transformedTime inst) ∧
      (inst.withTime (parameters.transformedTime inst)).complexity
          conditionalMachine ≤
        (estimate inst + parameters.logarithmicSlack inst : ℕ)

/-- A decoded conditional gap instance `(x, y, 1^t, 1^s)`. -/
structure Instance where
  /-- String whose conditional complexity is measured. -/
  output : List Bool
  /-- Finite random-access condition. -/
  condition : List Bool
  /-- Source primitive clock. -/
  time : ℕ
  /-- Source description threshold. -/
  threshold : ℕ

namespace Instance

/-- Forget the decision threshold, retaining the conditional MinKT instance. -/
def base (inst : Instance) : MINCKT.Instance where
  output := inst.output
  condition := inst.condition
  time := inst.time

/-- Unary encoding of the decision threshold. -/
def unaryThreshold (inst : Instance) : List Bool :=
  List.replicate inst.threshold true

/-- Canonical nested-pair encoding of `(x, y, 1^t, 1^s)`. -/
def encode (inst : Instance) : List Bool :=
  pair inst.base.encode inst.unaryThreshold

/-- Decode one canonical gap instance, rejecting malformed conditional MinKT
codes and every non-unary threshold field. -/
def decode? (bits : List Bool) : Option Instance := do
  let (baseBits, thresholdBits) ← unpair? bits
  let base ← MINCKT.Instance.decode? baseBits
  if thresholdBits = List.replicate thresholdBits.length true then
    some
      { output := base.output
        condition := base.condition
        time := base.time
        threshold := thresholdBits.length }
  else
    none

/-- Replace only the source description threshold. -/
def withThreshold (inst : Instance) (threshold : ℕ) : Instance :=
  { inst with threshold }

/-- The transformed clock `tau(|x|, |y|, t)`. -/
def laterTime (inst : Instance) (parameters : Parameters) : ℕ :=
  parameters.transformedTime inst.base

/-- The base-two logarithmic slack on the no side. -/
def logSlack (inst : Instance) (parameters : Parameters) : ℕ :=
  parameters.logarithmicSlack inst.base

/-- The condition's two-clock computational depth
`C^t(y) - C^tau(y)`. -/
noncomputable def conditionDepth {tapes : ℕ} (inst : Instance)
    (ordinaryMachine : TM tapes) (parameters : Parameters) : WithTop ℕ :=
  ordinaryMachine.computationalDepthBetween inst.condition inst.time
    (inst.laterTime parameters)

/-- Promised yes condition
`C_cond^t(x | y) + cd^(t,tau)(y) <= s`. -/
def IsYes {ordinaryTapes conditionalTapes : ℕ} (inst : Instance)
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters) : Prop :=
  inst.base.complexity conditionalMachine +
      inst.conditionDepth ordinaryMachine parameters ≤
    (inst.threshold : WithTop ℕ)

/-- Promised no condition
`C_cond^tau(x | y) > s + log_2(tau)`. -/
def IsNo {conditionalTapes : ℕ} (inst : Instance)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters) : Prop :=
  (inst.threshold + inst.logSlack parameters : ℕ) <
    (inst.base.withTime (inst.laterTime parameters)).complexity
      conditionalMachine

/-- A concrete program witnessing the depth-adjusted yes budget. -/
def IsAdjustedWitness {ordinaryTapes conditionalTapes : ℕ}
    (inst : Instance) (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters) (program : List Bool) : Prop :=
  (program.length : WithTop ℕ) +
        inst.conditionDepth ordinaryMachine parameters ≤
      (inst.threshold : WithTop ℕ) ∧
    conditionalMachine.ProducesInTime
      (RandomAccessCondition.oracle inst.condition) program inst.output inst.time

/-- A concrete program forbidden by the promised no condition. -/
def IsRelaxedWitness {conditionalTapes : ℕ} (inst : Instance)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters) (program : List Bool) : Prop :=
  program.length ≤ inst.threshold + inst.logSlack parameters ∧
    conditionalMachine.ProducesInTime
      (RandomAccessCondition.oracle inst.condition) program inst.output
        (inst.laterTime parameters)

end Instance

/-- Canonically encoded depth-adjusted yes language. Malformed codes are
outside the promise. -/
def yesLanguage {ordinaryTapes conditionalTapes : ℕ}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters) : Language :=
  {bits | match Instance.decode? bits with
    | some inst => inst.IsYes ordinaryMachine conditionalMachine parameters
    | none => False}

/-- Canonically encoded logarithmic-slack no language. -/
def noLanguage {conditionalTapes : ℕ}
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters) : Language :=
  {bits | match Instance.decode? bits with
    | some inst => inst.IsNo conditionalMachine parameters
    | none => False}

/-- Total completion obtained by accepting exactly when the estimator value is
at most the encoded threshold. Malformed codes are rejected. -/
def estimatorLanguage (estimate : Estimator) : Language :=
  {bits | match Instance.decode? bits with
    | some inst => estimate inst.base ≤ inst.threshold
    | none => False}

/-- Executable thresholding of a numerical estimator. -/
def decisionOfEstimator (estimate : Estimator) : List Bool → Bool :=
  fun bits => match Instance.decode? bits with
    | some inst => decide (estimate inst.base ≤ inst.threshold)
    | none => false

end GapMINCKT

end Complexity
