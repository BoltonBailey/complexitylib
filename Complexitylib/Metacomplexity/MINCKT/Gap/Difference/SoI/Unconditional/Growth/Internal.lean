/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Iterated.Internal

/-!
# Growth bounds for the iterated-clock schedule -- proof internals
-/


public section

namespace Complexity

namespace GapMINCKT

namespace DifferenceEstimator

namespace Unconditional

namespace Iterated

theorem clockIterate_polynomiallyBounded_internal
    {clock : ℕ → ℕ}
    (hclock : ∃ coefficient exponent, ∀ time,
      clock time ≤ coefficient * (time + 1) ^ exponent)
    (iterations : ℕ) :
    ∃ coefficient exponent, ∀ time,
      clockIterate clock iterations time ≤
        coefficient * (time + 1) ^ exponent := by
  obtain ⟨coefficient, exponent, hbound⟩ := hclock
  induction iterations with
  | zero =>
      refine ⟨1, 1, ?_⟩
      intro time
      simp [clockIterate]
  | succ iterations ih =>
      obtain ⟨iterateCoefficient, iterateExponent, hiterate⟩ := ih
      refine ⟨coefficient * (iterateCoefficient + 1) ^ exponent,
        iterateExponent * exponent, ?_⟩
      intro time
      have hone : 1 ≤ (time + 1) ^ iterateExponent :=
        Nat.one_le_pow' iterateExponent time
      have hplus : clockIterate clock iterations time + 1 ≤
          (iterateCoefficient + 1) * (time + 1) ^ iterateExponent := by
        calc
          clockIterate clock iterations time + 1 ≤
              iterateCoefficient * (time + 1) ^ iterateExponent + 1 :=
            Nat.add_le_add_right (hiterate time) 1
          _ ≤ iterateCoefficient * (time + 1) ^ iterateExponent +
                (time + 1) ^ iterateExponent :=
            Nat.add_le_add_left hone _
          _ = (iterateCoefficient + 1) *
                (time + 1) ^ iterateExponent := by
            rw [Nat.add_mul, one_mul]
      calc
        clockIterate clock (iterations + 1) time =
            clock (clockIterate clock iterations time) := rfl
        _ ≤ coefficient *
              (clockIterate clock iterations time + 1) ^ exponent :=
          hbound _
        _ ≤ coefficient *
              ((iterateCoefficient + 1) *
                (time + 1) ^ iterateExponent) ^ exponent :=
          Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left hplus exponent)
        _ = (coefficient * (iterateCoefficient + 1) ^ exponent) *
              (time + 1) ^ (iterateExponent * exponent) := by
          rw [Nat.mul_pow, Nat.pow_mul]
          ac_rfl

theorem IsAdmissibleClock.ordinaryParameters_admissible_internal
    {clock : ℕ → ℕ} (hclock : IsAdmissibleClock clock) :
    (ordinaryParameters clock).IsAdmissible := by
  constructor
  · exact hclock.toIsRegularClock.ordinaryParameters_widening_internal
  · obtain ⟨coefficient, exponent, hbound⟩ := hclock.polynomiallyBounded
    refine ⟨coefficient, exponent, ?_⟩
    intro outputLength time
    exact (hbound time).trans <|
      Nat.mul_le_mul_left coefficient <|
        Nat.pow_le_pow_left (by omega) exponent

theorem IsAdmissibleClock.conditionalParameters_admissible_internal
    {clock : ℕ → ℕ} (hclock : IsAdmissibleClock clock) :
    (conditionalParameters clock).IsAdmissible := by
  constructor
  · exact hclock.toIsRegularClock.conditionalParameters_widening_internal
  · obtain ⟨coefficient, exponent, hbound⟩ :=
      clockIterate_polynomiallyBounded_internal hclock.polynomiallyBounded 4
    refine ⟨coefficient, exponent, ?_⟩
    intro outputLength conditionLength time
    simpa [conditionalParameters, GapMINCKT.Parameters.IsPolynomiallyBounded,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        hbound (time + outputLength + conditionLength)

end Iterated

end Unconditional

end DifferenceEstimator

end GapMINCKT

end Complexity
