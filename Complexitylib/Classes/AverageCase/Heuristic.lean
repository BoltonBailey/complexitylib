/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.AverageCase.Heuristic.Defs
public import Complexitylib.Classes.AverageCase.Heuristic.Internal

/-!
# Errorless average-case heuristics

This module exposes the exact errorless-heuristic semantics used in average-case
complexity: globally sound yes/no/failure answers, polynomial runtime through a
canonical `FP` output codec, and slice-wise failure probability over dyadic
ensembles. It also defines `AvgPAt δ` and the inverse-polynomial intersection
`AvgP` for distributional problems.
-/


public section

namespace Complexity

namespace HeuristicAnswer

/-- Canonical heuristic answers round-trip through their binary codec. -/
@[simp] theorem decode?_encode (answer : HeuristicAnswer) :
    decode? answer.encode = some answer :=
  decode?_encode_internal answer

/-- The canonical three-answer encoding is injective. -/
theorem encode_injective : Function.Injective encode :=
  encode_injective_internal

/-- Every canonical heuristic-answer code has length at most one. -/
theorem encode_length_le_one (answer : HeuristicAnswer) :
    answer.encode.length ≤ 1 :=
  encode_length_le_one_internal answer

/-- Complementing an answer twice returns the original answer. -/
@[simp] theorem complement_complement (answer : HeuristicAnswer) :
    answer.complement.complement = answer :=
  complement_complement_internal answer

/-- Complement preserves and reflects explicit failure. -/
@[simp] theorem complement_eq_failure_iff (answer : HeuristicAnswer) :
    answer.complement = .failure ↔ answer = .failure :=
  complement_eq_failure_iff_internal answer

/-- Complementing a sound answer gives a sound answer for the negated truth
value. -/
theorem CorrectFor.complement {answer : HeuristicAnswer} {truth : Prop}
    (hcorrect : answer.CorrectFor truth) :
    answer.complement.CorrectFor (¬ truth) :=
  hcorrect.complement_internal

end HeuristicAnswer

namespace HeuristicAlgorithm

/-- Complementing a globally errorless heuristic yields an errorless heuristic
for the complement language. -/
theorem IsErrorlessFor.complement {A : HeuristicAlgorithm} {L : Language}
    (herrorless : A.IsErrorlessFor L) :
    A.complement.IsErrorlessFor Lᶜ :=
  herrorless.complement_internal

/-- Complementing a heuristic preserves its failure event pointwise. -/
@[simp] theorem complement_apply_eq_failure_iff
    (A : HeuristicAlgorithm) (x : List Bool) :
    A.complement x = .failure ↔ A x = .failure :=
  complement_apply_eq_failure_iff_internal A x

/-- Failure probability is nonnegative. -/
theorem failureProbability_nonneg (D : DyadicEnsemble (List Bool))
    (A : HeuristicAlgorithm) (n : ℕ) :
    0 ≤ A.failureProbability D n :=
  failureProbability_nonneg_internal D A n

/-- Failure probability is at most one. -/
theorem failureProbability_le_one (D : DyadicEnsemble (List Bool))
    (A : HeuristicAlgorithm) (n : ℕ) :
    A.failureProbability D n ≤ 1 :=
  failureProbability_le_one_internal D A n

/-- Complementing a heuristic preserves its failure probability exactly. -/
@[simp] theorem failureProbability_complement
    (D : DyadicEnsemble (List Bool)) (A : HeuristicAlgorithm) (n : ℕ) :
    A.complement.failureProbability D n = A.failureProbability D n :=
  failureProbability_complement_internal D A n

/-- A failure guarantee remains true under a pointwise weaker bound. -/
theorem FailsWithProbabilityAtMost.mono
    {D : DyadicEnsemble (List Bool)} {A : HeuristicAlgorithm} {δ ε : ℕ → ℚ}
    (hfailure : A.FailsWithProbabilityAtMost D δ)
    (hδε : ∀ n, δ n ≤ ε n) :
    A.FailsWithProbabilityAtMost D ε :=
  hfailure.mono_internal hδε

/-- Complementing a heuristic preserves every failure guarantee. -/
theorem FailsWithProbabilityAtMost.complement
    {D : DyadicEnsemble (List Bool)} {A : HeuristicAlgorithm} {δ : ℕ → ℚ}
    (hfailure : A.FailsWithProbabilityAtMost D δ) :
    A.complement.FailsWithProbabilityAtMost D δ :=
  hfailure.complement_internal

/-- The decision-function adapter has its advertised pointwise semantics. -/
theorem ofDecision_apply (decide : List Bool → Bool) (x : List Bool) :
    ofDecision decide x = if decide x then .accept else .reject :=
  ofDecision_apply_internal decide x

/-- The canonical encoding of a decision adapter is its singleton Boolean
output. -/
theorem ofDecision_encoded (decide : List Bool → Bool) :
    (ofDecision decide).encoded = fun x => [decide x] :=
  ofDecision_encoded_internal decide

/-- A decision adapter runs in polynomial time whenever its singleton Boolean
output function belongs to `FP`. -/
theorem ofDecision_isPolynomialTime {decide : List Bool → Bool}
    (htime : (fun x => [decide x]) ∈ FP) :
    (ofDecision decide).IsPolynomialTime :=
  ofDecision_isPolynomialTime_internal htime

/-- An exact Boolean decision function induces a globally errorless heuristic. -/
theorem ofDecision_isErrorlessFor {decide : List Bool → Bool} {L : Language}
    (hdecide : ∀ x, decide x = true ↔ x ∈ L) :
    (ofDecision decide).IsErrorlessFor L :=
  ofDecision_isErrorlessFor_internal hdecide

/-- A total decision adapter has zero failure probability on every ensemble
slice. -/
@[simp] theorem ofDecision_failureProbability
    (D : DyadicEnsemble (List Bool)) (decide : List Bool → Bool) (n : ℕ) :
    (ofDecision decide).failureProbability D n = 0 :=
  ofDecision_failureProbability_internal D decide n

/-- A total decision adapter meets the zero failure bound. -/
theorem ofDecision_failsWithProbabilityAtMost_zero
    (D : DyadicEnsemble (List Bool)) (decide : List Bool → Bool) :
    (ofDecision decide).FailsWithProbabilityAtMost D (fun _ => 0) :=
  ofDecision_failsWithProbabilityAtMost_zero_internal D decide

end HeuristicAlgorithm

/-- The total inverse-polynomial failure target is nonnegative. -/
theorem inversePolynomialFailure_nonneg (c n : ℕ) :
    0 ≤ inversePolynomialFailure c n :=
  inversePolynomialFailure_nonneg_internal c n

/-- The total inverse-polynomial failure target is at most one. -/
theorem inversePolynomialFailure_le_one (c n : ℕ) :
    inversePolynomialFailure c n ≤ 1 :=
  inversePolynomialFailure_le_one_internal c n

/-- `AvgPAt` is monotone in its allowed failure probability. -/
theorem AvgPAt_mono {δ ε : ℕ → ℚ} (hδε : ∀ n, δ n ≤ ε n) :
    AvgPAt δ ⊆ AvgPAt ε :=
  AvgPAt_mono_internal hδε

/-- Membership in `AvgP` means meeting every total inverse-polynomial failure
target. -/
theorem mem_AvgP_iff (problem : DistributionalProblem) :
    problem ∈ AvgP ↔
      ∀ c, problem ∈ AvgPAt (inversePolynomialFailure c) :=
  mem_AvgP_iff_internal problem

namespace DistributionalProblem

/-- Any exact polynomial-time Boolean decision function gives a zero-failure
member of `AvgPAt δ` for every nonnegative failure allowance. -/
theorem mem_AvgPAt_of_decision (problem : DistributionalProblem)
    (δ : ℕ → ℚ) (decide : List Bool → Bool)
    (htime : (fun x => [decide x]) ∈ FP)
    (hdecide : ∀ x, decide x = true ↔ x ∈ problem.language)
    (hδ : ∀ n, 0 ≤ δ n) :
    problem ∈ AvgPAt δ :=
  problem.mem_AvgPAt_of_decision_internal δ decide htime hdecide hδ

/-- Any exact polynomial-time Boolean decision function solves the same language
errorlessly on every distribution ensemble, hence places the distributional
problem in `AvgP`. -/
theorem mem_AvgP_of_decision (problem : DistributionalProblem)
    (decide : List Bool → Bool)
    (htime : (fun x => [decide x]) ∈ FP)
    (hdecide : ∀ x, decide x = true ↔ x ∈ problem.language) :
    problem ∈ AvgP :=
  problem.mem_AvgP_of_decision_internal decide htime hdecide

end DistributionalProblem

end Complexity
