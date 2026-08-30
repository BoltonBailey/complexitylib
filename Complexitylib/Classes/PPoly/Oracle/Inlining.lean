/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Oracle.Inlining.Defs
import Complexitylib.Classes.PPoly.Oracle.Inlining.Internal

/-!
# Inlining polynomial circuit oracles

This module turns a fixed-round adaptive computation relative to any language
in `P/poly` into an ordinary circuit by selecting and inlining the relevant
query-width circuit-family members.
-/


public section

namespace Complexity

namespace PolynomialCircuitOracle

/-- The width-selected family members implement the circuit oracle's induced
Boolean oracle in every adaptive round. -/
theorem implementation_implements {language : Language}
    (circuitOracle : PolynomialCircuitOracle language)
    {inputWidth outputWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (program : AdaptiveOracleProgram inputWidth outputWidth rounds) :
    (circuitOracle.implementation program).Implements circuitOracle.oracle :=
  circuitOracle.implementation_implements_internal program

/-- Each selected oracle circuit has exactly the circuit-family size at that
round's query width. -/
@[simp] theorem implementation_circuit_size {language : Language}
    (circuitOracle : PolynomialCircuitOracle language)
    {inputWidth outputWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (program : AdaptiveOracleProgram inputWidth outputWidth rounds)
    (round : Fin rounds) :
    ((circuitOracle.implementation program).circuit round).size =
      circuitOracle.family.size (program.queryWidth round) :=
  circuitOracle.implementation_circuit_size_internal program round

end PolynomialCircuitOracle

namespace AdaptiveOracleProgram

/-- Replacing all adaptive oracle calls by their polynomial circuit-family
members preserves the program output on every input. -/
theorem inlineCircuitOracle_eval {language : Language}
    {inputWidth outputWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (program : AdaptiveOracleProgram inputWidth outputWidth rounds)
    (circuitOracle : PolynomialCircuitOracle language)
    (input : BitString inputWidth) :
    (program.inlineCircuitOracle circuitOracle).2.eval input =
      program.eval circuitOracle.oracle input :=
  program.inlineCircuitOracle_eval_internal circuitOracle input

/-- The ordinary inlined circuit has exactly the adaptive-history recurrence
plus the final output circuit's size. -/
theorem inlineCircuitOracle_size {language : Language}
    {inputWidth outputWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (program : AdaptiveOracleProgram inputWidth outputWidth rounds)
    (circuitOracle : PolynomialCircuitOracle language) :
    (program.inlineCircuitOracle circuitOracle).2.size =
      program.inlineHistorySize (circuitOracle.implementation program)
        rounds le_rfl + program.final.size :=
  program.inlineCircuitOracle_size_internal circuitOracle

end AdaptiveOracleProgram

end Complexity
