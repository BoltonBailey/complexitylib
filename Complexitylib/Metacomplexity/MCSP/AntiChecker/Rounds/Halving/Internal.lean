/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Rounds.Defs
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Counting.Internal
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Rounds.Internal
import Mathlib.Algebra.Order.Ring.Pow

/-!
# Halving bounds for anti-checker shrink rounds -- proof internals
-/


public section

namespace Complexity

namespace AntiChecker

theorem two_mul_sub_one_pow_le_pow_internal {denominator : ℕ}
    (hdenominator : 2 ≤ denominator) :
    2 * (denominator - 1) ^ denominator ≤
      denominator ^ denominator := by
  have hpredPower :
      (denominator - 1) ^ denominator ≤
        denominator * (denominator - 1) ^ (denominator - 1) := by
    calc
      (denominator - 1) ^ denominator =
          (denominator - 1) ^ ((denominator - 1) + 1) := by
        congr 1
        omega
      _ =
          (denominator - 1) ^ (denominator - 1) *
            (denominator - 1) := by
        rw [pow_succ]
      _ ≤ (denominator - 1) ^ (denominator - 1) * denominator :=
        Nat.mul_le_mul_left _ (Nat.sub_le denominator 1)
      _ = denominator * (denominator - 1) ^ (denominator - 1) := by
        rw [Nat.mul_comm]
  have hbernoulli :
      (denominator - 1) ^ denominator +
          denominator * (denominator - 1) ^ (denominator - 1) ≤
        denominator ^ denominator := by
    have hbound := pow_add_mul_le_add_pow
      (R := ℕ) (a := denominator - 1) (b := 1)
      (by omega) (by omega) denominator
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ denominator)] using hbound
  calc
    2 * (denominator - 1) ^ denominator =
        (denominator - 1) ^ denominator +
          (denominator - 1) ^ denominator := by
      omega
    _ ≤ (denominator - 1) ^ denominator +
          denominator * (denominator - 1) ^ (denominator - 1) :=
      Nat.add_le_add_left hpredPower _
    _ ≤ denominator ^ denominator := hbernoulli

theorem two_pow_mul_sub_one_pow_mul_le_pow_mul_internal
    {denominator : ℕ} (hdenominator : 2 ≤ denominator)
    (blocks : ℕ) :
    2 ^ blocks * (denominator - 1) ^ (denominator * blocks) ≤
      denominator ^ (denominator * blocks) := by
  calc
    2 ^ blocks * (denominator - 1) ^ (denominator * blocks) =
        (2 * (denominator - 1) ^ denominator) ^ blocks := by
      rw [mul_pow, pow_mul]
    _ ≤ (denominator ^ denominator) ^ blocks :=
      Nat.pow_le_pow_left
        (two_mul_sub_one_pow_le_pow_internal hdenominator) blocks
    _ = denominator ^ (denominator * blocks) := by
      rw [pow_mul]

theorem IsShrinkTrace.candidateSurvivorCount_eq_zero_of_initial_lt_two_pow_internal
    {arity denominator threshold blocks : ℕ}
    {target : BitString arity → Bool}
    {inputs : List (BitString arity)}
    (htrace : IsShrinkTrace denominator target threshold inputs)
    (hdenominator : 2 ≤ denominator)
    (hlength : inputs.length = denominator * blocks)
    (hinitial :
      candidateSurvivorCount target threshold [] < 2 ^ blocks) :
    candidateSurvivorCount target threshold inputs = 0 := by
  apply htrace.candidateSurvivorCount_eq_zero_internal
  rw [hlength]
  have hfactorPos :
      0 < (denominator - 1) ^ (denominator * blocks) := by
    exact pow_pos (by omega) _
  calc
    (denominator - 1) ^ (denominator * blocks) *
          candidateSurvivorCount target threshold [] <
        (denominator - 1) ^ (denominator * blocks) * 2 ^ blocks :=
      Nat.mul_lt_mul_of_pos_left hinitial hfactorPos
    _ = 2 ^ blocks *
          (denominator - 1) ^ (denominator * blocks) := by
      rw [Nat.mul_comm]
    _ ≤ denominator ^ (denominator * blocks) :=
      two_pow_mul_sub_one_pow_mul_le_pow_mul_internal
        hdenominator blocks

theorem IsShrinkTrace.isFor_of_initial_lt_two_pow_internal
    {arity denominator threshold blocks : ℕ} [NeZero arity]
    {target : BitString arity → Bool}
    {inputs : List (BitString arity)}
    (htrace : IsShrinkTrace denominator target threshold inputs)
    (hdenominator : 2 ≤ denominator)
    (hlength : inputs.length = denominator * blocks)
    (hinitial :
      candidateSurvivorCount target threshold [] < 2 ^ blocks) :
    IsFor target threshold inputs := by
  apply (candidateSurvivorCount_eq_zero_iff_isFor_internal
    target inputs).mp
  exact htrace.candidateSurvivorCount_eq_zero_of_initial_lt_two_pow_internal
    hdenominator hlength hinitial

end AntiChecker

end Complexity
