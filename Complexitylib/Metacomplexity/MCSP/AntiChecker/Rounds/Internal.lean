/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Rounds.Defs
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Counting.Internal

/-!
# Anti-checker shrink rounds -- proof internals
-/


public section

namespace Complexity

namespace AntiChecker

theorem isShrinkTrace_nil_internal {arity denominator threshold : ℕ}
    (target : BitString arity → Bool) :
    IsShrinkTrace denominator target threshold [] := by
  trivial

theorem isShrinkTrace_cons_iff_internal
    {arity denominator threshold : ℕ}
    (target : BitString arity → Bool) (input : BitString arity)
    (inputs : List (BitString arity)) :
    IsShrinkTrace denominator target threshold (input :: inputs) ↔
      IsShrinkTrace denominator target threshold inputs ∧
        IsShrinkExtension denominator target threshold inputs input := by
  rfl

theorem IsShrinkTrace.scaledCandidateSurvivorCount_internal
    {arity denominator threshold : ℕ}
    {target : BitString arity → Bool}
    {inputs : List (BitString arity)}
    (htrace : IsShrinkTrace denominator target threshold inputs) :
    denominator ^ inputs.length *
        candidateSurvivorCount target threshold inputs ≤
      (denominator - 1) ^ inputs.length *
        candidateSurvivorCount target threshold [] := by
  induction inputs with
  | nil => simp
  | cons input inputs ih =>
      have htail := htrace.1
      have hstep := htrace.2
      have hinduction := ih htail
      unfold IsShrinkExtension at hstep
      simp only [List.length_cons, pow_succ]
      calc
        denominator ^ inputs.length * denominator *
              candidateSurvivorCount target threshold (input :: inputs) =
            denominator ^ inputs.length *
              (denominator *
                candidateSurvivorCount target threshold (input :: inputs)) := by
          ring
        _ ≤ denominator ^ inputs.length *
              ((denominator - 1) *
                candidateSurvivorCount target threshold inputs) :=
          Nat.mul_le_mul_left _ hstep
        _ = (denominator - 1) *
              (denominator ^ inputs.length *
                candidateSurvivorCount target threshold inputs) := by
          ring
        _ ≤ (denominator - 1) *
              ((denominator - 1) ^ inputs.length *
                candidateSurvivorCount target threshold []) :=
          Nat.mul_le_mul_left _ hinduction
        _ = (denominator - 1) ^ inputs.length * (denominator - 1) *
              candidateSurvivorCount target threshold [] := by
          ring

theorem IsShrinkTrace.candidateSurvivorCount_eq_zero_internal
    {arity denominator threshold : ℕ}
    {target : BitString arity → Bool}
    {inputs : List (BitString arity)}
    (htrace : IsShrinkTrace denominator target threshold inputs)
    (hbound :
      (denominator - 1) ^ inputs.length *
          candidateSurvivorCount target threshold [] <
        denominator ^ inputs.length) :
    candidateSurvivorCount target threshold inputs = 0 := by
  by_contra hnonzero
  have hpositive :
      1 ≤ candidateSurvivorCount target threshold inputs :=
    Nat.one_le_iff_ne_zero.mpr hnonzero
  have hlower :
      denominator ^ inputs.length ≤
        denominator ^ inputs.length *
          candidateSurvivorCount target threshold inputs := by
    simpa only [mul_one] using
      Nat.mul_le_mul_left (denominator ^ inputs.length) hpositive
  have hscaled := htrace.scaledCandidateSurvivorCount_internal
  exact (not_lt_of_ge (hlower.trans hscaled)) hbound

theorem IsShrinkTrace.isFor_internal
    {arity denominator threshold : ℕ} [NeZero arity]
    {target : BitString arity → Bool}
    {inputs : List (BitString arity)}
    (htrace : IsShrinkTrace denominator target threshold inputs)
    (hbound :
      (denominator - 1) ^ inputs.length *
          candidateSurvivorCount target threshold [] <
        denominator ^ inputs.length) :
    IsFor target threshold inputs := by
  apply (candidateSurvivorCount_eq_zero_iff_isFor_internal
    target inputs).mp
  exact htrace.candidateSurvivorCount_eq_zero_internal hbound

end AntiChecker

end Complexity
