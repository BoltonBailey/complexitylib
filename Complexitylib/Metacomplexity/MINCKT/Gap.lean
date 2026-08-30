/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Promise
public import Complexitylib.Metacomplexity.MINCKT.Gap.Defs
public import Complexitylib.Metacomplexity.MINCKT.Gap.Internal

/-!
# Gap conditional MinKT

For a canonical input `(x, y, 1^t, 1^s)`, this module exposes the exact
depth-adjusted promise used in Hirahara's 2022 route toward excluding
Heuristica:

- yes: `C_cond^t(x | y) + cd^(t,tau)(y) <= s`;
- no: `C_cond^tau(x | y) > s + log_2(tau)`.

The ordinary depth machine and conditional oracle machine remain explicit.
Malformed encodings and intermediate-gap instances lie outside the promise.
-/


public section

namespace Complexity

namespace GapMINCKT

namespace Parameters

/-- The identity transform is an admissible conditional MinKT clock. -/
theorem identity_isAdmissible : identity.IsAdmissible :=
  identity_isAdmissible_internal

end Parameters

namespace Instance

variable {ordinaryTapes conditionalTapes : ℕ}

/-- The unary threshold has exactly the represented length. -/
@[simp] theorem length_unaryThreshold (inst : Instance) :
    inst.unaryThreshold.length = inst.threshold :=
  length_unaryThreshold_internal inst

/-- Every canonical conditional gap instance decodes exactly. -/
@[simp] theorem decode?_encode (inst : Instance) :
    decode? inst.encode = some inst :=
  decode?_encode_internal inst

/-- Successful decoding characterizes canonical gap-instance encodings. -/
theorem decode?_eq_some_iff (bits : List Bool) (inst : Instance) :
    decode? bits = some inst ↔ bits = inst.encode :=
  decode?_eq_some_iff_internal bits inst

/-- Decoding fails exactly on noncanonical strings. -/
theorem decode?_eq_none_iff (bits : List Bool) :
    decode? bits = none ↔ ¬ ∃ inst : Instance, bits = inst.encode :=
  decode?_eq_none_iff_internal bits

/-- Canonical conditional gap encoding is injective. -/
theorem encode_injective : Function.Injective encode :=
  encode_injective_internal

/-- Exact nested-pair code length for `(x, y, 1^t, 1^s)`. -/
@[simp] theorem length_encode (inst : Instance) :
    inst.encode.length =
      4 * inst.output.length + 4 * inst.condition.length +
        2 * inst.time + inst.threshold + 10 :=
  length_encode_internal inst

/-- Widening places the transformed clock after the source clock. -/
theorem laterTime_ge (parameters : Parameters)
    (hwidening : parameters.IsWidening) (inst : Instance) :
    inst.time ≤ inst.laterTime parameters :=
  laterTime_ge_internal parameters hwidening inst

/-- Under widening, depth plus later-clock complexity reconstructs the
source-clock complexity of the condition exactly. -/
theorem conditionDepth_add_later (ordinaryMachine : TM ordinaryTapes)
    (parameters : Parameters) (hwidening : parameters.IsWidening)
    (inst : Instance) :
    inst.conditionDepth ordinaryMachine parameters +
        ordinaryMachine.timeBoundedKolmogorovComplexity inst.condition
          (inst.laterTime parameters) =
      ordinaryMachine.timeBoundedKolmogorovComplexity inst.condition inst.time :=
  conditionDepth_add_later_internal ordinaryMachine parameters hwidening inst

/-- The depth-adjusted yes inequality is equivalent to a concrete source-clock
program obeying that same adjusted description budget. -/
theorem isYes_iff_exists_adjustedWitness (inst : Instance)
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters) :
    inst.IsYes ordinaryMachine conditionalMachine parameters ↔
      ∃ program,
        inst.IsAdjustedWitness ordinaryMachine conditionalMachine parameters
          program :=
  isYes_iff_exists_adjustedWitness_internal inst ordinaryMachine
    conditionalMachine parameters

/-- Every depth-adjusted yes-instance is, in particular, below its unadjusted
source threshold. -/
theorem isYes_implies_base_isAtMost (inst : Instance)
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters)
    (hyes : inst.IsYes ordinaryMachine conditionalMachine parameters) :
    inst.base.IsAtMost conditionalMachine inst.threshold :=
  isYes_implies_base_isAtMost_internal inst ordinaryMachine conditionalMachine
    parameters hyes

/-- The no condition says exactly that no program meets the transformed clock
and logarithmically relaxed description budget. -/
theorem isNo_iff_no_relaxedWitness (inst : Instance)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters) :
    inst.IsNo conditionalMachine parameters ↔
      ¬∃ program, inst.IsRelaxedWitness conditionalMachine parameters program :=
  isNo_iff_no_relaxedWitness_internal inst conditionalMachine parameters

/-- Increasing the stored threshold preserves a yes-instance. -/
theorem IsYes.withThreshold_mono (inst : Instance)
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters) {first second : ℕ}
    (hthreshold : first ≤ second)
    (hyes : (inst.withThreshold first).IsYes ordinaryMachine
      conditionalMachine parameters) :
    (inst.withThreshold second).IsYes ordinaryMachine conditionalMachine
      parameters :=
  IsYes.withThreshold_mono_internal inst ordinaryMachine conditionalMachine
    parameters hthreshold hyes

/-- Decreasing the stored threshold preserves a no-instance. -/
theorem IsNo.withThreshold_anti (inst : Instance)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters) {first second : ℕ}
    (hthreshold : first ≤ second)
    (hno : (inst.withThreshold second).IsNo conditionalMachine parameters) :
    (inst.withThreshold first).IsNo conditionalMachine parameters :=
  IsNo.withThreshold_anti_internal inst conditionalMachine parameters
    hthreshold hno

/-- Widening the clock prevents a depth-adjusted yes-instance from also
satisfying the logarithmic no condition. -/
theorem not_isNo_of_isYes (inst : Instance)
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters) (hwidening : parameters.IsWidening)
    (hyes : inst.IsYes ordinaryMachine conditionalMachine parameters) :
    ¬inst.IsNo conditionalMachine parameters :=
  not_isNo_of_isYes_internal inst ordinaryMachine conditionalMachine parameters
    hwidening hyes

end Instance

/-- The estimator's upper sandwich bound places it below the threshold of every
depth-adjusted yes-instance. -/
theorem Estimator.SatisfiesBounds.le_threshold_of_isYes
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : Parameters} {estimate : Estimator}
    (hestimate : estimate.SatisfiesBounds ordinaryMachine conditionalMachine
      parameters)
    (inst : Instance)
    (hyes : inst.IsYes ordinaryMachine conditionalMachine parameters) :
    estimate inst.base ≤ inst.threshold :=
  estimator_le_threshold_of_isYes_internal hestimate inst hyes

/-- The estimator's lower sandwich bound places it strictly above the threshold
of every logarithmic no-instance. -/
theorem Estimator.SatisfiesBounds.threshold_lt_of_isNo
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : Parameters} {estimate : Estimator}
    (hestimate : estimate.SatisfiesBounds ordinaryMachine conditionalMachine
      parameters)
    (inst : Instance) (hno : inst.IsNo conditionalMachine parameters) :
    inst.threshold < estimate inst.base :=
  threshold_lt_estimator_of_isNo_internal hestimate inst hno

/-- Canonical yes-language membership is the depth-adjusted upper bound. -/
@[simp] theorem mem_yesLanguage_encode_iff
    {ordinaryTapes conditionalTapes : ℕ}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters) (inst : Instance) :
    inst.encode ∈ yesLanguage ordinaryMachine conditionalMachine parameters ↔
      inst.IsYes ordinaryMachine conditionalMachine parameters :=
  yesLanguage_mem_encode_iff_internal ordinaryMachine conditionalMachine
    parameters inst

/-- Canonical no-language membership is the transformed-clock lower bound. -/
@[simp] theorem mem_noLanguage_encode_iff {conditionalTapes : ℕ}
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters) (inst : Instance) :
    inst.encode ∈ noLanguage conditionalMachine parameters ↔
      inst.IsNo conditionalMachine parameters :=
  noLanguage_mem_encode_iff_internal conditionalMachine parameters inst

/-- Under clock widening, the two encoded gap languages are disjoint. -/
theorem disjoint_yesLanguage_noLanguage
    {ordinaryTapes conditionalTapes : ℕ}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters) (hwidening : parameters.IsWidening) :
    Disjoint (yesLanguage ordinaryMachine conditionalMachine parameters)
      (noLanguage conditionalMachine parameters) :=
  disjoint_yesLanguage_noLanguage_internal ordinaryMachine conditionalMachine
    parameters hwidening

/-- On canonical codes, the estimator completion accepts exactly when its value
is at most the stored threshold. -/
@[simp] theorem mem_estimatorLanguage_encode_iff (estimate : Estimator)
    (inst : Instance) :
    inst.encode ∈ estimatorLanguage estimate ↔
      estimate inst.base ≤ inst.threshold :=
  estimatorLanguage_mem_encode_iff_internal estimate inst

/-- Executable estimator thresholding is the characteristic function of its
completion language. -/
theorem decisionOfEstimator_eq_true_iff (estimate : Estimator)
    (bits : List Bool) :
    decisionOfEstimator estimate bits = true ↔
      bits ∈ estimatorLanguage estimate :=
  decisionOfEstimator_eq_true_iff_internal estimate bits

/-- A valid estimator's completion contains every promised yes-instance. -/
theorem Estimator.SatisfiesBounds.yesLanguage_subset
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : Parameters} {estimate : Estimator}
    (hestimate : estimate.SatisfiesBounds ordinaryMachine conditionalMachine
      parameters) :
    yesLanguage ordinaryMachine conditionalMachine parameters ⊆
      estimatorLanguage estimate :=
  yesLanguage_subset_estimatorLanguage_internal hestimate

/-- A valid estimator's completion excludes every promised no-instance. -/
theorem Estimator.SatisfiesBounds.disjoint_noLanguage
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : Parameters} {estimate : Estimator}
    (hestimate : estimate.SatisfiesBounds ordinaryMachine conditionalMachine
      parameters) :
    Disjoint (estimatorLanguage estimate)
      (noLanguage conditionalMachine parameters) :=
  disjoint_estimatorLanguage_noLanguage_internal hestimate

/-- Thresholding a valid estimator accepts every promised yes-instance. -/
theorem Estimator.SatisfiesBounds.decision_eq_true_of_mem_yesLanguage
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : Parameters} {estimate : Estimator}
    (hestimate : estimate.SatisfiesBounds ordinaryMachine conditionalMachine
      parameters) {bits : List Bool}
    (hyes : bits ∈ yesLanguage ordinaryMachine conditionalMachine parameters) :
    decisionOfEstimator estimate bits = true :=
  decisionOfEstimator_eq_true_of_mem_yesLanguage_internal hestimate hyes

/-- Thresholding a valid estimator rejects every promised no-instance. -/
theorem Estimator.SatisfiesBounds.decision_eq_false_of_mem_noLanguage
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : Parameters} {estimate : Estimator}
    (hestimate : estimate.SatisfiesBounds ordinaryMachine conditionalMachine
      parameters) {bits : List Bool}
    (hno : bits ∈ noLanguage conditionalMachine parameters) :
    decisionOfEstimator estimate bits = false :=
  decisionOfEstimator_eq_false_of_mem_noLanguage_internal hestimate hno

end GapMINCKT

/-- Hirahara's widening-certified depth-adjusted conditional MinKT promise. -/
@[expose]
def GapMINCKT {ordinaryTapes conditionalTapes : ℕ}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters)
    (hwidening : parameters.IsWidening) : PromiseProblem where
  yesInstances :=
    GapMINCKT.yesLanguage ordinaryMachine conditionalMachine parameters
  noInstances := GapMINCKT.noLanguage conditionalMachine parameters
  disjoint := GapMINCKT.disjoint_yesLanguage_noLanguage ordinaryMachine
    conditionalMachine parameters hwidening

/-- The promise's yes side is definitionally the canonical depth-adjusted
language. -/
@[simp] theorem GapMINCKT_yesInstances
    {ordinaryTapes conditionalTapes : ℕ}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters)
    (hwidening : parameters.IsWidening) :
    (GapMINCKT ordinaryMachine conditionalMachine parameters
      hwidening).yesInstances =
        GapMINCKT.yesLanguage ordinaryMachine conditionalMachine parameters :=
  rfl

/-- The promise's no side is definitionally the canonical transformed-clock
language. -/
@[simp] theorem GapMINCKT_noInstances
    {ordinaryTapes conditionalTapes : ℕ}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters)
    (hwidening : parameters.IsWidening) :
    (GapMINCKT ordinaryMachine conditionalMachine parameters
      hwidening).noInstances =
        GapMINCKT.noLanguage conditionalMachine parameters :=
  rfl

/-- Proposition 6.2's numerical core: thresholding any function satisfying the
two-sided conditional-complexity sandwich solves the exact gap promise. -/
theorem GapMINCKT_solvedBy_decisionOfEstimator
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : GapMINCKT.Parameters}
    (hwidening : parameters.IsWidening)
    {estimate : GapMINCKT.Estimator}
    (hestimate : estimate.SatisfiesBounds ordinaryMachine conditionalMachine
      parameters) :
    (GapMINCKT ordinaryMachine conditionalMachine parameters hwidening).SolvedBy
      (GapMINCKT.decisionOfEstimator estimate) := by
  constructor
  · intro bits hyes
    exact hestimate.decision_eq_true_of_mem_yesLanguage hyes
  · intro bits hno
    exact hestimate.decision_eq_false_of_mem_noLanguage hno

/-- If a valid estimator's threshold language is in `P`, it is a deterministic
polynomial-time completion of the conditional gap promise. This isolates the
remaining algorithmic obligation in Proposition 6.2. -/
theorem GapMINCKT_mem_PromiseP_of_estimatorLanguage_mem_P
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : GapMINCKT.Parameters}
    (hwidening : parameters.IsWidening)
    {estimate : GapMINCKT.Estimator}
    (hestimate : estimate.SatisfiesBounds ordinaryMachine conditionalMachine
      parameters)
    (hpolynomial : GapMINCKT.estimatorLanguage estimate ∈ P) :
    GapMINCKT ordinaryMachine conditionalMachine parameters hwidening ∈
      PromiseP := by
  refine ⟨GapMINCKT.estimatorLanguage estimate, hpolynomial, ?_, ?_⟩
  · exact hestimate.yesLanguage_subset
  · exact hestimate.disjoint_noLanguage

end Complexity
