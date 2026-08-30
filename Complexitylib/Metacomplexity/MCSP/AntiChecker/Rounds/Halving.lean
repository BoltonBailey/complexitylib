/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Rounds.Defs
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Rounds.Halving.Internal

/-!
# Halving bounds for anti-checker shrink rounds

For denominator `d >= 2`, a block of `d` rounds satisfying a `1/d` shrink
reduces the composed survivor bound by at least a factor of two. Thus `d*b`
rounds eliminate any initial canonical survivor count strictly below `2^b`.
-/


public section

namespace Complexity

namespace AntiChecker

/-- The elementary power inequality behind one halving block. -/
theorem two_mul_sub_one_pow_le_pow {denominator : ℕ}
    (hdenominator : 2 ≤ denominator) :
    2 * (denominator - 1) ^ denominator ≤
      denominator ^ denominator :=
  two_mul_sub_one_pow_le_pow_internal hdenominator

/-- Repeating the elementary halving inequality over `blocks` blocks. -/
theorem two_pow_mul_sub_one_pow_mul_le_pow_mul
    {denominator : ℕ} (hdenominator : 2 ≤ denominator)
    (blocks : ℕ) :
    2 ^ blocks * (denominator - 1) ^ (denominator * blocks) ≤
      denominator ^ (denominator * blocks) :=
  two_pow_mul_sub_one_pow_mul_le_pow_mul_internal hdenominator blocks

/-- A `d*b`-round shrink trace has no survivors when its initial survivor count
is strictly below `2^b`. -/
theorem IsShrinkTrace.candidateSurvivorCount_eq_zero_of_initial_lt_two_pow
    {arity denominator threshold blocks : ℕ}
    {target : BitString arity → Bool}
    {inputs : List (BitString arity)}
    (htrace : IsShrinkTrace denominator target threshold inputs)
    (hdenominator : 2 ≤ denominator)
    (hlength : inputs.length = denominator * blocks)
    (hinitial :
      candidateSurvivorCount target threshold [] < 2 ^ blocks) :
    candidateSurvivorCount target threshold inputs = 0 :=
  htrace.candidateSurvivorCount_eq_zero_of_initial_lt_two_pow_internal
    hdenominator hlength hinitial

/-- A `d*b`-round trace whose initial survivor count is below `2^b` is an
anti-checker. -/
theorem IsShrinkTrace.isFor_of_initial_lt_two_pow
    {arity denominator threshold blocks : ℕ} [NeZero arity]
    {target : BitString arity → Bool}
    {inputs : List (BitString arity)}
    (htrace : IsShrinkTrace denominator target threshold inputs)
    (hdenominator : 2 ≤ denominator)
    (hlength : inputs.length = denominator * blocks)
    (hinitial :
      candidateSurvivorCount target threshold [] < 2 ^ blocks) :
    IsFor target threshold inputs :=
  htrace.isFor_of_initial_lt_two_pow_internal
    hdenominator hlength hinitial

end AntiChecker

end Complexity
