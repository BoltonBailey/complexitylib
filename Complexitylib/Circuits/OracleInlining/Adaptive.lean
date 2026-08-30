/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.OracleInlining.Adaptive.Defs
import Complexitylib.Circuits.OracleInlining.Adaptive.Internal

/-!
# Fixed-round adaptive oracle circuit programs

This module compiles every query of a fixed-round adaptive oracle program into
one ordinary circuit. Correct oracle circuits give exact semantic preservation,
and the size recurrence records every query, oracle, and retained-history cost.
-/


public section

namespace Complexity

namespace AdaptiveOracleProgram

/-- Inlining correct oracle circuits produces the exact semantic history after
every prefix of the adaptive computation. -/
theorem inlineHistory_eval
    {inputWidth outputWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (program : AdaptiveOracleProgram inputWidth outputWidth rounds)
    (implementation : OracleCircuitImplementation program)
    {oracle : BooleanOracle} (himplementation : implementation.Implements oracle)
    (input : BitString inputWidth) (completed : ℕ) (hcompleted : completed ≤ rounds) :
    (program.inlineHistory implementation completed hcompleted).2.eval input =
      program.history oracle input completed hcompleted :=
  program.inlineHistory_eval_internal implementation himplementation input
    completed hcompleted

/-- The compiled history circuit has exactly the recursively accounted size. -/
theorem inlineHistory_size
    {inputWidth outputWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (program : AdaptiveOracleProgram inputWidth outputWidth rounds)
    (implementation : OracleCircuitImplementation program)
    (completed : ℕ) (hcompleted : completed ≤ rounds) :
    (program.inlineHistory implementation completed hcompleted).2.size =
      program.inlineHistorySize implementation completed hcompleted :=
  program.inlineHistory_size_internal implementation completed hcompleted

/-- Inlining correct oracle circuits preserves the complete adaptive program's
output on every input. -/
theorem inline_eval
    {inputWidth outputWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (program : AdaptiveOracleProgram inputWidth outputWidth rounds)
    (implementation : OracleCircuitImplementation program)
    {oracle : BooleanOracle} (himplementation : implementation.Implements oracle)
    (input : BitString inputWidth) :
    (program.inline implementation).2.eval input = program.eval oracle input :=
  program.inline_eval_internal implementation himplementation input

/-- The fully inlined circuit has the exact history-prefix cost plus the final
output circuit's size. -/
theorem inline_size
    {inputWidth outputWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (program : AdaptiveOracleProgram inputWidth outputWidth rounds)
    (implementation : OracleCircuitImplementation program) :
    (program.inline implementation).2.size =
      program.inlineHistorySize implementation rounds le_rfl +
        program.final.size :=
  program.inline_size_internal implementation

end AdaptiveOracleProgram

end Complexity
