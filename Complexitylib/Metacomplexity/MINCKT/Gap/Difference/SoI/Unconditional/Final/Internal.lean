/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Slack.Internal
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Growth.Internal

/-!
# Polynomial growth of the slack-amplified final clock -- proof internals
-/


public section

namespace Complexity

namespace GapMINCKT

namespace DifferenceEstimator

namespace Unconditional

namespace Iterated

namespace Slack

theorem clockIterate_add_one_polynomiallyBounded_internal
    {clock : ℕ → ℕ}
    (hclock : ∃ coefficient exponent, ∀ time,
      clock time ≤ coefficient * (time + 1) ^ exponent)
    (iterations : ℕ) :
    ∃ coefficient exponent, ∀ time,
      clockIterate clock iterations time + 1 ≤
        coefficient * (time + 1) ^ exponent := by
  obtain ⟨coefficient, exponent, hbound⟩ :=
    clockIterate_polynomiallyBounded_internal hclock iterations
  refine ⟨coefficient + 1, exponent, ?_⟩
  intro time
  have hone : 1 ≤ (time + 1) ^ exponent :=
    Nat.one_le_pow' exponent time
  calc
    clockIterate clock iterations time + 1 ≤
        coefficient * (time + 1) ^ exponent + 1 :=
      Nat.add_le_add_right (hbound time) 1
    _ ≤ coefficient * (time + 1) ^ exponent +
          (time + 1) ^ exponent :=
      Nat.add_le_add_left hone _
    _ = (coefficient + 1) * (time + 1) ^ exponent := by
      rw [Nat.add_mul, one_mul]

theorem pow_slackExponent_le_product_internal
    (clock : ℕ → ℕ) (additive compilerLoss : ℕ)
    (outputLength conditionLength time : ℕ) :
    2 ^ slackExponent clock additive compilerLoss
          outputLength conditionLength time ≤
      (clockIterate clock 2
            (totalTime outputLength conditionLength time) + 1) *
        (clockIterate clock 3
            (totalTime outputLength conditionLength time) + 1) *
        (clockIterate clock 4
            (totalTime outputLength conditionLength time) + 1) *
        2 ^ additive * 2 ^ compilerLoss := by
  let second := clockIterate clock 2
    (totalTime outputLength conditionLength time) + 1
  let third := clockIterate clock 3
    (totalTime outputLength conditionLength time) + 1
  let fourth := clockIterate clock 4
    (totalTime outputLength conditionLength time) + 1
  have hsecond : 2 ^ Nat.log 2 second ≤ second :=
    Nat.pow_log_le_self 2 (by dsimp [second]; omega)
  have hthird : 2 ^ Nat.log 2 third ≤ third :=
    Nat.pow_log_le_self 2 (by dsimp [third]; omega)
  have hfourth : 2 ^ Nat.log 2 fourth ≤ fourth :=
    Nat.pow_log_le_self 2 (by dsimp [fourth]; omega)
  have hproduct := Nat.mul_le_mul
    (Nat.mul_le_mul
      (Nat.mul_le_mul
        (Nat.mul_le_mul hsecond hthird) hfourth)
        (le_refl (2 ^ additive)))
    (le_refl (2 ^ compilerLoss))
  simpa only [slackExponent, Nat.pow_add] using hproduct

theorem finalClock_polynomiallyBounded_internal
    {clock : ℕ → ℕ} (additive compilerLoss : ℕ)
    (hclock : ∃ coefficient exponent, ∀ time,
      clock time ≤ coefficient * (time + 1) ^ exponent) :
    ∃ coefficient exponent, ∀ outputLength conditionLength time,
      finalClock clock additive compilerLoss outputLength conditionLength time ≤
        coefficient * (outputLength + conditionLength + time + 1) ^ exponent := by
  obtain ⟨secondCoefficient, secondExponent, hsecond⟩ :=
    clockIterate_add_one_polynomiallyBounded_internal hclock 2
  obtain ⟨thirdCoefficient, thirdExponent, hthird⟩ :=
    clockIterate_add_one_polynomiallyBounded_internal hclock 3
  obtain ⟨fourthCoefficient, fourthExponent, hfourth⟩ :=
    clockIterate_add_one_polynomiallyBounded_internal hclock 4
  refine ⟨secondCoefficient * thirdCoefficient * fourthCoefficient *
      2 ^ additive * 2 ^ compilerLoss * fourthCoefficient,
    secondExponent + thirdExponent + fourthExponent + fourthExponent + 1, ?_⟩
  intro outputLength conditionLength time
  let total := totalTime outputLength conditionLength time
  let base := total + 1
  have hpower := pow_slackExponent_le_product_internal clock additive
    compilerLoss outputLength conditionLength time
  have hsecond' : clockIterate clock 2 total + 1 ≤
      secondCoefficient * base ^ secondExponent := hsecond total
  have hthird' : clockIterate clock 3 total + 1 ≤
      thirdCoefficient * base ^ thirdExponent := hthird total
  have hfourth' : clockIterate clock 4 total + 1 ≤
      fourthCoefficient * base ^ fourthExponent := hfourth total
  calc
    finalClock clock additive compilerLoss outputLength conditionLength time ≤
        (((clockIterate clock 2 total + 1) *
              (clockIterate clock 3 total + 1) *
            (clockIterate clock 4 total + 1) * 2 ^ additive *
          2 ^ compilerLoss) *
        ((clockIterate clock 4 total + 1) * base)) := by
      exact Nat.mul_le_mul_right _ hpower
    _ ≤ (((secondCoefficient * base ^ secondExponent) *
              (thirdCoefficient * base ^ thirdExponent) *
            (fourthCoefficient * base ^ fourthExponent) * 2 ^ additive *
          2 ^ compilerLoss) *
        ((fourthCoefficient * base ^ fourthExponent) * base)) := by
      gcongr
    _ = (secondCoefficient * thirdCoefficient * fourthCoefficient *
          2 ^ additive * 2 ^ compilerLoss * fourthCoefficient) *
        base ^ (secondExponent + thirdExponent + fourthExponent +
          fourthExponent + 1) := by
      simp only [Nat.pow_add, Nat.pow_one]
      ring
    _ = (secondCoefficient * thirdCoefficient * fourthCoefficient *
          2 ^ additive * 2 ^ compilerLoss * fourthCoefficient) *
        (outputLength + conditionLength + time + 1) ^
          (secondExponent + thirdExponent + fourthExponent +
            fourthExponent + 1) := by
      congr 2
      dsimp [base, total, totalTime]
      omega

theorem IsAdmissibleClock.parameters_admissible_internal
    {clock : ℕ → ℕ} (hclock : IsAdmissibleClock clock)
    (additive compilerLoss : ℕ) :
    (parameters clock additive compilerLoss).IsAdmissible := by
  constructor
  · intro outputLength conditionLength time
    exact finalClock_source_le_internal clock additive compilerLoss
      outputLength conditionLength time
  · exact finalClock_polynomiallyBounded_internal additive compilerLoss
      hclock.polynomiallyBounded

end Slack

end Iterated

end Unconditional

end DifferenceEstimator

end GapMINCKT

end Complexity
