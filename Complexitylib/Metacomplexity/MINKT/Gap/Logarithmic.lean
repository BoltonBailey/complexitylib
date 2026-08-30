/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Promise
public import Complexitylib.Metacomplexity.MINKT.Gap.Logarithmic.Defs
public import Complexitylib.Metacomplexity.MINKT.Gap.Logarithmic.Internal

/-!
# Logarithmic-gap MINKT

This module exposes the exact `Gap_tau MINKT` promise from Hirahara's 2022
Definition 3.3. For `(x,1^t,1^s)`, it distinguishes `C^t(x) <= s` from
`C^tau(x) > s + log_2(tau)`. It also packages Fact 3.4's numerical estimator
sandwich and proves that thresholding any such estimator solves the promise.
-/


public section

namespace Complexity

namespace GapMINKT

namespace Logarithmic

namespace Parameters

/-- The identity transformation is admissible. -/
theorem identity_isAdmissible : identity.IsAdmissible :=
  identity_isAdmissible_internal

end Parameters

/-- Widening places the transformed clock after the source clock. -/
theorem transformedTime_ge (parameters : Parameters)
    (hwidening : parameters.IsWidening) (inst : MINKT.Instance) :
    inst.time ≤ parameters.transformedTime inst :=
  transformedTime_ge_internal parameters hwidening inst

/-- The logarithmic no condition excludes exactly the programs meeting its
relaxed description budget and transformed clock. -/
theorem isNo_iff_no_relaxedWitness {tapes : ℕ}
    (inst : GapMINKT.Instance) (machine : TM tapes)
    (parameters : Parameters) :
    IsNo inst machine parameters ↔
      ¬∃ program, IsRelaxedWitness inst machine parameters program :=
  isNo_iff_no_relaxedWitness_internal inst machine parameters

/-- A widening clock prevents a source yes-instance from also satisfying the
exact logarithmic no condition. -/
theorem not_isNo_of_isYes {tapes : ℕ}
    (inst : GapMINKT.Instance) (machine : TM tapes)
    (parameters : Parameters) (hwidening : parameters.IsWidening)
    (hyes : inst.IsYes machine) : ¬IsNo inst machine parameters :=
  not_isNo_of_isYes_internal inst machine parameters hwidening hyes

/-- Canonical yes membership is the source bounded-complexity inequality. -/
@[simp] theorem mem_yesLanguage_encode_iff {tapes : ℕ}
    (machine : TM tapes) (inst : GapMINKT.Instance) :
    inst.encode ∈ yesLanguage machine ↔ inst.IsYes machine :=
  yesLanguage_mem_encode_iff_internal machine inst

/-- Canonical no membership is the exact transformed-clock lower bound. -/
@[simp] theorem mem_noLanguage_encode_iff {tapes : ℕ}
    (machine : TM tapes) (parameters : Parameters)
    (inst : GapMINKT.Instance) :
    inst.encode ∈ noLanguage machine parameters ↔
      IsNo inst machine parameters :=
  noLanguage_mem_encode_iff_internal machine parameters inst

/-- Widening makes the exact logarithmic promise sides disjoint. -/
theorem disjoint_yesLanguage_noLanguage {tapes : ℕ}
    (machine : TM tapes) (parameters : Parameters)
    (hwidening : parameters.IsWidening) :
    Disjoint (yesLanguage machine) (noLanguage machine parameters) :=
  disjoint_yesLanguage_noLanguage_internal machine parameters hwidening

/-- The estimator's upper bound places it below every yes threshold. -/
theorem Estimator.SatisfiesBounds.le_threshold_of_isYes {tapes : ℕ}
    {machine : TM tapes} {parameters : Parameters} {estimate : Estimator}
    (hestimate : estimate.SatisfiesBounds machine parameters)
    (inst : GapMINKT.Instance) (hyes : inst.IsYes machine) :
    estimate inst.base ≤ inst.threshold :=
  estimator_le_threshold_of_isYes_internal hestimate inst hyes

/-- The estimator's lower bound places it above every no threshold. -/
theorem Estimator.SatisfiesBounds.threshold_lt_of_isNo {tapes : ℕ}
    {machine : TM tapes} {parameters : Parameters} {estimate : Estimator}
    (hestimate : estimate.SatisfiesBounds machine parameters)
    (inst : GapMINKT.Instance) (hno : IsNo inst machine parameters) :
    inst.threshold < estimate inst.base :=
  threshold_lt_estimator_of_isNo_internal hestimate inst hno

/-- Canonical estimator-language membership is numerical thresholding. -/
@[simp] theorem mem_estimatorLanguage_encode_iff (estimate : Estimator)
    (inst : GapMINKT.Instance) :
    inst.encode ∈ estimatorLanguage estimate ↔
      estimate inst.base ≤ inst.threshold :=
  estimatorLanguage_mem_encode_iff_internal estimate inst

/-- Executable thresholding characterizes the estimator completion. -/
theorem decisionOfEstimator_eq_true_iff (estimate : Estimator)
    (bits : List Bool) :
    decisionOfEstimator estimate bits = true ↔
      bits ∈ estimatorLanguage estimate :=
  decisionOfEstimator_eq_true_iff_internal estimate bits

/-- Adding a threshold and then forgetting it recovers the original MINKT
instance. -/
@[simp] theorem thresholdInstance_base (inst : MINKT.Instance)
    (threshold : ℕ) :
    (thresholdInstance inst threshold).base = inst :=
  thresholdInstance_base_internal inst threshold

/-- If some threshold up to the cap is accepted, bounded search returns an
accepted threshold no larger than that witness. -/
theorem firstAcceptedThreshold_spec_of_accepted
    (decide : List Bool → Bool) (inst : MINKT.Instance) {cap threshold : ℕ}
    (hthreshold : threshold ≤ cap)
    (haccept : decide (thresholdInstance inst threshold).encode = true) :
    decide
        (thresholdInstance inst
          (firstAcceptedThreshold decide inst cap)).encode = true ∧
      firstAcceptedThreshold decide inst cap ≤ threshold :=
  firstAcceptedThreshold_spec_of_accepted_internal
    decide inst hthreshold haccept

/-- A valid estimator completion contains the yes language. -/
theorem Estimator.SatisfiesBounds.yesLanguage_subset {tapes : ℕ}
    {machine : TM tapes} {parameters : Parameters} {estimate : Estimator}
    (hestimate : estimate.SatisfiesBounds machine parameters) :
    yesLanguage machine ⊆ estimatorLanguage estimate :=
  yesLanguage_subset_estimatorLanguage_internal hestimate

/-- A valid estimator completion excludes the logarithmic no language. -/
theorem Estimator.SatisfiesBounds.disjoint_noLanguage {tapes : ℕ}
    {machine : TM tapes} {parameters : Parameters} {estimate : Estimator}
    (hestimate : estimate.SatisfiesBounds machine parameters) :
    Disjoint (estimatorLanguage estimate) (noLanguage machine parameters) :=
  disjoint_estimatorLanguage_noLanguage_internal hestimate

/-- Thresholding a valid estimator accepts every promised yes-instance. -/
theorem Estimator.SatisfiesBounds.decision_eq_true_of_mem_yesLanguage
    {tapes : ℕ} {machine : TM tapes} {parameters : Parameters}
    {estimate : Estimator}
    (hestimate : estimate.SatisfiesBounds machine parameters)
    {bits : List Bool} (hyes : bits ∈ yesLanguage machine) :
    decisionOfEstimator estimate bits = true :=
  decisionOfEstimator_eq_true_of_mem_yesLanguage_internal hestimate hyes

/-- Thresholding a valid estimator rejects every promised no-instance. -/
theorem Estimator.SatisfiesBounds.decision_eq_false_of_mem_noLanguage
    {tapes : ℕ} {machine : TM tapes} {parameters : Parameters}
    {estimate : Estimator}
    (hestimate : estimate.SatisfiesBounds machine parameters)
    {bits : List Bool} (hno : bits ∈ noLanguage machine parameters) :
    decisionOfEstimator estimate bits = false :=
  decisionOfEstimator_eq_false_of_mem_noLanguage_internal hestimate hno

/-- The widening-certified exact logarithmic GapMINKT promise. -/
def problem {tapes : ℕ} (machine : TM tapes) (parameters : Parameters)
    (hwidening : parameters.IsWidening) : PromiseProblem where
  yesInstances := yesLanguage machine
  noInstances := noLanguage machine parameters
  disjoint := disjoint_yesLanguage_noLanguage machine parameters hwidening

/-- The reverse numerical direction of Fact 3.4 at one finite source instance.

Bounded threshold search against any solver for logarithmic GapMINKT returns a
value between the later-clock complexity minus logarithmic slack and the exact
source-clock complexity. -/
theorem timeSearchEstimator_satisfiesBoundsAt {tapes : ℕ}
    {machine : TM tapes} {parameters : Parameters}
    (hwidening : parameters.IsWidening) {decide : List Bool → Bool}
    (hsolve : (problem machine parameters hwidening).SolvedBy decide)
    (inst : MINKT.Instance)
    (hfinite : machine.timeBoundedKolmogorovComplexity
      inst.output inst.time ≠ ⊤) :
    (timeSearchEstimator decide inst : WithTop ℕ) ≤
        machine.timeBoundedKolmogorovComplexity inst.output inst.time ∧
      machine.timeBoundedKolmogorovComplexity inst.output
          (parameters.transformedTime inst) ≤
        (timeSearchEstimator decide inst +
          parameters.logarithmicSlack inst : ℕ) :=
  timeSearchEstimator_satisfiesBoundsAt_internal
    hsolve.1 hsolve.2 inst hfinite

/-- A gap solver yields the Fact 3.4 estimator sandwich on every explicitly
eligible input whose source-clock complexity is finite. -/
theorem timeSearchEstimator_satisfiesBoundsOn {tapes : ℕ}
    {machine : TM tapes} {parameters : Parameters}
    (hwidening : parameters.IsWidening) {decide : List Bool → Bool}
    {eligible : MINKT.Instance → Prop}
    (hsolve : (problem machine parameters hwidening).SolvedBy decide)
    (hfinite : ∀ inst, eligible inst →
      machine.timeBoundedKolmogorovComplexity inst.output inst.time ≠ ⊤) :
    (timeSearchEstimator decide).SatisfiesBoundsOn
      machine parameters eligible :=
  timeSearchEstimator_satisfiesBoundsOn_internal
    hsolve.1 hsolve.2 hfinite

/-- Exact domain-restricted reverse Fact 3.4: on inputs with `|x| <= t`, it is
enough that the source complexity be finite on that same domain. -/
theorem timeSearchEstimator_satisfiesBoundsOn_lengthWithinTime
    {tapes : ℕ} {machine : TM tapes} {parameters : Parameters}
    (hwidening : parameters.IsWidening) {decide : List Bool → Bool}
    (hsolve : (problem machine parameters hwidening).SolvedBy decide)
    (hfinite : ∀ inst : MINKT.Instance, IsLengthWithinTime inst →
      machine.timeBoundedKolmogorovComplexity inst.output inst.time ≠ ⊤) :
    (timeSearchEstimator decide).SatisfiesBoundsOn machine parameters
      IsLengthWithinTime :=
  timeSearchEstimator_satisfiesBoundsOn hwidening hsolve hfinite

/-- If source-clock complexity is finite on every input, bounded threshold
search converts a logarithmic-gap solver into a global Fact 3.4 estimator. -/
theorem timeSearchEstimator_satisfiesBounds {tapes : ℕ}
    {machine : TM tapes} {parameters : Parameters}
    (hwidening : parameters.IsWidening) {decide : List Bool → Bool}
    (hsolve : (problem machine parameters hwidening).SolvedBy decide)
    (hfinite : ∀ inst : MINKT.Instance,
      machine.timeBoundedKolmogorovComplexity inst.output inst.time ≠ ⊤) :
    (timeSearchEstimator decide).SatisfiesBounds machine parameters :=
  timeSearchEstimator_satisfiesBounds_internal
    hsolve.1 hsolve.2 hfinite

/-- Thresholding a valid estimator solves the exact logarithmic promise. -/
theorem problem_solvedBy_decisionOfEstimator {tapes : ℕ}
    {machine : TM tapes} {parameters : Parameters}
    (hwidening : parameters.IsWidening) {estimate : Estimator}
    (hestimate : estimate.SatisfiesBounds machine parameters) :
    (problem machine parameters hwidening).SolvedBy
      (decisionOfEstimator estimate) := by
  constructor
  · intro bits hyes
    exact hestimate.decision_eq_true_of_mem_yesLanguage hyes
  · intro bits hno
    exact hestimate.decision_eq_false_of_mem_noLanguage hno

/-- If a valid estimator's threshold language is in `P`, it completes the exact
logarithmic promise in deterministic polynomial time. -/
theorem problem_mem_PromiseP_of_estimatorLanguage_mem_P {tapes : ℕ}
    {machine : TM tapes} {parameters : Parameters}
    (hwidening : parameters.IsWidening) {estimate : Estimator}
    (hestimate : estimate.SatisfiesBounds machine parameters)
    (hpolynomial : estimatorLanguage estimate ∈ P) :
    problem machine parameters hwidening ∈ PromiseP := by
  refine ⟨estimatorLanguage estimate, hpolynomial, ?_, ?_⟩
  · exact hestimate.yesLanguage_subset
  · exact hestimate.disjoint_noLanguage

end Logarithmic

end GapMINKT

end Complexity
