/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Rounds.Defs
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Rounds.Internal
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Rounds.Selection

/-!
# Anti-checker shrink rounds

One shrink round bounds the next survivor count by a fixed fraction of the
current count. This module composes a trace of such rounds into an exact
natural-number power inequality. If that upper bound is smaller than one after
rescaling, the final survivor count is zero and the trace is an anti-checker.
The selection submodule constructs these traces by approximate minimization.
-/


public section

namespace Complexity

namespace AntiChecker

/-- The empty list is a valid shrink trace. -/
@[simp] theorem isShrinkTrace_nil {arity denominator threshold : ℕ}
    (target : BitString arity → Bool) :
    IsShrinkTrace denominator target threshold [] :=
  isShrinkTrace_nil_internal target

/-- Consing an input extends a shrink trace exactly when it shrinks the prefix
represented by the tail. -/
@[simp] theorem isShrinkTrace_cons_iff
    {arity denominator threshold : ℕ}
    (target : BitString arity → Bool) (input : BitString arity)
    (inputs : List (BitString arity)) :
    IsShrinkTrace denominator target threshold (input :: inputs) ↔
      IsShrinkTrace denominator target threshold inputs ∧
        IsShrinkExtension denominator target threshold inputs input :=
  isShrinkTrace_cons_iff_internal target input inputs

/-- Composing every round in a shrink trace gives the exact scaled survivor
bound with one factor per selected input. -/
theorem IsShrinkTrace.scaledCandidateSurvivorCount
    {arity denominator threshold : ℕ}
    {target : BitString arity → Bool}
    {inputs : List (BitString arity)}
    (htrace : IsShrinkTrace denominator target threshold inputs) :
    denominator ^ inputs.length *
        candidateSurvivorCount target threshold inputs ≤
      (denominator - 1) ^ inputs.length *
        candidateSurvivorCount target threshold [] :=
  htrace.scaledCandidateSurvivorCount_internal

/-- If the composed upper bound is smaller than one after rescaling, no
canonical candidate survives the trace. -/
theorem IsShrinkTrace.candidateSurvivorCount_eq_zero
    {arity denominator threshold : ℕ}
    {target : BitString arity → Bool}
    {inputs : List (BitString arity)}
    (htrace : IsShrinkTrace denominator target threshold inputs)
    (hbound :
      (denominator - 1) ^ inputs.length *
          candidateSurvivorCount target threshold [] <
        denominator ^ inputs.length) :
    candidateSurvivorCount target threshold inputs = 0 :=
  htrace.candidateSurvivorCount_eq_zero_internal hbound

/-- A shrink trace whose composed bound is below one is an anti-checker. -/
theorem IsShrinkTrace.isFor
    {arity denominator threshold : ℕ} [NeZero arity]
    {target : BitString arity → Bool}
    {inputs : List (BitString arity)}
    (htrace : IsShrinkTrace denominator target threshold inputs)
    (hbound :
      (denominator - 1) ^ inputs.length *
          candidateSurvivorCount target threshold [] <
        denominator ^ inputs.length) :
    IsFor target threshold inputs :=
  htrace.isFor_internal hbound

end AntiChecker

end Complexity
