/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.AverageCase.Heuristic.Defs
import Complexitylib.Classes.AverageCase.FiniteEnsemble.Internal

/-!
# Errorless average-case heuristics -- proof internals

This layer proves codec exactness, semantic soundness of complement and decision
adapters, and the elementary probability/class monotonicity laws.
-/


public section

namespace Complexity

namespace HeuristicAnswer

theorem decode?_encode_internal (answer : HeuristicAnswer) :
    decode? answer.encode = some answer := by
  cases answer <;> rfl

theorem encode_injective_internal : Function.Injective encode := by
  intro a b hab
  have := congrArg decode? hab
  simpa only [decode?_encode_internal, Option.some.injEq] using this

theorem encode_length_le_one_internal (answer : HeuristicAnswer) :
    answer.encode.length ≤ 1 := by
  cases answer <;> simp [encode]

theorem complement_complement_internal (answer : HeuristicAnswer) :
    answer.complement.complement = answer := by
  cases answer <;> rfl

theorem complement_eq_failure_iff_internal (answer : HeuristicAnswer) :
    answer.complement = .failure ↔ answer = .failure := by
  cases answer <;> simp [complement]

theorem CorrectFor.complement_internal {answer : HeuristicAnswer} {truth : Prop}
    (hcorrect : answer.CorrectFor truth) :
    answer.complement.CorrectFor (¬ truth) := by
  cases answer <;> simp_all [CorrectFor, complement]

end HeuristicAnswer

namespace HeuristicAlgorithm

theorem IsErrorlessFor.complement_internal {A : HeuristicAlgorithm}
    {L : Language} (herrorless : A.IsErrorlessFor L) :
    A.complement.IsErrorlessFor Lᶜ := by
  intro x
  exact (herrorless x).complement_internal

theorem complement_apply_eq_failure_iff_internal
    (A : HeuristicAlgorithm) (x : List Bool) :
    A.complement x = .failure ↔ A x = .failure := by
  exact HeuristicAnswer.complement_eq_failure_iff_internal (A x)

theorem failureProbability_nonneg_internal
    (D : FiniteEnsemble (List Bool)) (A : HeuristicAlgorithm) (n : ℕ) :
    0 ≤ A.failureProbability D n :=
  D.probability_nonneg_internal n _

theorem failureProbability_le_one_internal
    (D : FiniteEnsemble (List Bool)) (A : HeuristicAlgorithm) (n : ℕ) :
    A.failureProbability D n ≤ 1 :=
  D.probability_le_one_internal n _

theorem answerProbability_nonneg_internal
    (D : FiniteEnsemble (List Bool)) (A : HeuristicAlgorithm)
    (answer : HeuristicAnswer) (n : ℕ) :
    0 ≤ A.answerProbability D answer n :=
  D.probability_nonneg_internal n _

theorem answerProbability_le_one_internal
    (D : FiniteEnsemble (List Bool)) (A : HeuristicAlgorithm)
    (answer : HeuristicAnswer) (n : ℕ) :
    A.answerProbability D answer n ≤ 1 :=
  D.probability_le_one_internal n _

theorem failureProbability_eq_answerProbability_internal
    (D : FiniteEnsemble (List Bool)) (A : HeuristicAlgorithm) (n : ℕ) :
    A.failureProbability D n = A.answerProbability D .failure n :=
  rfl

theorem IsErrorlessFor.one_sub_languageProbability_sub_failure_le_reject_internal
    {A : HeuristicAlgorithm} {L : Language}
    (herrorless : A.IsErrorlessFor L)
    (D : FiniteEnsemble (List Bool)) (n : ℕ) :
    1 - D.languageProbability L n - A.failureProbability D n ≤
      A.answerProbability D .reject n := by
  classical
  unfold FiniteEnsemble.languageProbability failureProbability answerProbability
  have hcover : ∀ x : List Bool, True →
      x ∈ L ∨ A x = .failure ∨ A x = .reject := by
    intro x _hx
    cases hanswer : A x with
    | accept =>
        left
        simpa only [IsErrorlessFor, hanswer, HeuristicAnswer.CorrectFor] using
          herrorless x
    | reject => exact Or.inr (Or.inr rfl)
    | failure => exact Or.inr (Or.inl rfl)
  have htotal : 1 ≤ D.probability n
      (fun x => x ∈ L ∨ A x = .failure ∨ A x = .reject) := by
    have hmono := D.probability_mono_internal n
      (fun _x : List Bool => True)
      (fun x => x ∈ L ∨ A x = .failure ∨ A x = .reject) hcover
    simpa only [D.probability_true_internal] using hmono
  have houter := D.probability_or_le_internal n
    (fun x => x ∈ L) (fun x => A x = .failure ∨ A x = .reject)
  have hinner := D.probability_or_le_internal n
    (fun x => A x = .failure) (fun x => A x = .reject)
  linarith

theorem failureProbability_complement_internal
    (D : FiniteEnsemble (List Bool)) (A : HeuristicAlgorithm) (n : ℕ) :
    A.complement.failureProbability D n = A.failureProbability D n := by
  apply D.probability_congr_internal
  intro x
  exact complement_apply_eq_failure_iff_internal A x

theorem FailsWithProbabilityAtMost.mono_internal
    {D : FiniteEnsemble (List Bool)} {A : HeuristicAlgorithm} {δ ε : ℕ → ℚ}
    (hfailure : A.FailsWithProbabilityAtMost D δ)
    (hδε : ∀ n, δ n ≤ ε n) :
    A.FailsWithProbabilityAtMost D ε := by
  intro n
  exact (hfailure n).trans (hδε n)

theorem FailsWithProbabilityAtMost.complement_internal
    {D : FiniteEnsemble (List Bool)} {A : HeuristicAlgorithm} {δ : ℕ → ℚ}
    (hfailure : A.FailsWithProbabilityAtMost D δ) :
    A.complement.FailsWithProbabilityAtMost D δ := by
  intro n
  rw [failureProbability_complement_internal]
  exact hfailure n

theorem ofDecision_apply_internal (decide : List Bool → Bool) (x : List Bool) :
    ofDecision decide x = if decide x then .accept else .reject :=
  rfl

theorem ofDecision_encoded_internal (decide : List Bool → Bool) :
    (ofDecision decide).encoded = fun x => [decide x] := by
  funext x
  cases h : decide x <;> simp [ofDecision, encoded, HeuristicAnswer.encode, h]

theorem ofDecision_isPolynomialTime_internal {decide : List Bool → Bool}
    (htime : (fun x => [decide x]) ∈ FP) :
    (ofDecision decide).IsPolynomialTime := by
  rw [IsPolynomialTime, ofDecision_encoded_internal]
  exact htime

theorem ofDecision_isErrorlessFor_internal {decide : List Bool → Bool}
    {L : Language} (hdecide : ∀ x, decide x = true ↔ x ∈ L) :
    (ofDecision decide).IsErrorlessFor L := by
  intro x
  cases h : decide x
  · simp only [ofDecision, h, Bool.false_eq_true, ↓reduceIte,
      HeuristicAnswer.CorrectFor]
    intro hx
    have : decide x = true := (hdecide x).mpr hx
    simp [h] at this
  · simp only [ofDecision, h, ↓reduceIte, HeuristicAnswer.CorrectFor]
    exact (hdecide x).mp h

theorem ofDecision_failureProbability_internal
    (D : FiniteEnsemble (List Bool)) (decide : List Bool → Bool) (n : ℕ) :
    (ofDecision decide).failureProbability D n = 0 := by
  unfold failureProbability
  have himpossible : ∀ x : List Bool, ofDecision decide x ≠ .failure := by
    intro x
    cases h : decide x <;> simp [ofDecision, h]
  apply le_antisymm
  · have hzero := D.probability_mono_internal n
      (fun x => ofDecision decide x = .failure) (fun _ => False)
      (fun x hx => himpossible x hx)
    exact hzero.trans_eq (D.probability_false_internal n)
  · exact D.probability_nonneg_internal n _

theorem ofDecision_failsWithProbabilityAtMost_zero_internal
    (D : FiniteEnsemble (List Bool)) (decide : List Bool → Bool) :
    (ofDecision decide).FailsWithProbabilityAtMost D (fun _ => 0) := by
  intro n
  rw [ofDecision_failureProbability_internal]

end HeuristicAlgorithm

theorem inversePolynomialFailure_nonneg_internal (c n : ℕ) :
    0 ≤ inversePolynomialFailure c n := by
  unfold inversePolynomialFailure
  positivity

theorem inversePolynomialFailure_le_one_internal (c n : ℕ) :
    inversePolynomialFailure c n ≤ 1 := by
  unfold inversePolynomialFailure
  have hbase : (1 : ℚ) ≤ Nat.max 1 n := by
    exact_mod_cast Nat.le_max_left 1 n
  have hpow : (1 : ℚ) ≤ (Nat.max 1 n : ℚ) ^ c := by
    exact one_le_pow₀ hbase
  simpa using one_div_le_one_div_of_le (a := (1 : ℚ)) (by norm_num) hpow

theorem AvgPAt_mono_internal {δ ε : ℕ → ℚ} (hδε : ∀ n, δ n ≤ ε n) :
    AvgPAt δ ⊆ AvgPAt ε := by
  intro problem hproblem
  obtain ⟨A, htime, herrorless, hfailure⟩ := hproblem
  exact ⟨A, htime, herrorless, hfailure.mono_internal hδε⟩

theorem mem_AvgP_iff_internal (problem : DistributionalProblem) :
    problem ∈ AvgP ↔
      ∀ c, problem ∈ AvgPAt (inversePolynomialFailure c) := by
  simp [AvgP]

theorem DistributionalProblem.mem_AvgPAt_of_decision_internal
    (problem : DistributionalProblem) (δ : ℕ → ℚ)
    (decide : List Bool → Bool)
    (htime : (fun x => [decide x]) ∈ FP)
    (hdecide : ∀ x, decide x = true ↔ x ∈ problem.language)
    (hδ : ∀ n, 0 ≤ δ n) :
    problem ∈ AvgPAt δ := by
  refine ⟨HeuristicAlgorithm.ofDecision decide,
    HeuristicAlgorithm.ofDecision_isPolynomialTime_internal htime,
    HeuristicAlgorithm.ofDecision_isErrorlessFor_internal hdecide, ?_⟩
  intro n
  rw [HeuristicAlgorithm.ofDecision_failureProbability_internal]
  exact hδ n

theorem DistributionalProblem.mem_AvgP_of_decision_internal
    (problem : DistributionalProblem) (decide : List Bool → Bool)
    (htime : (fun x => [decide x]) ∈ FP)
    (hdecide : ∀ x, decide x = true ↔ x ∈ problem.language) :
    problem ∈ AvgP := by
  rw [mem_AvgP_iff_internal]
  intro c
  exact problem.mem_AvgPAt_of_decision_internal
    (inversePolynomialFailure c) decide htime hdecide
    (inversePolynomialFailure_nonneg_internal c)

end Complexity
