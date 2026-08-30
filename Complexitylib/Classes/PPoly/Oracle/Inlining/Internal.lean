/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Oracle
public import Complexitylib.Classes.PPoly.Oracle.Inlining.Defs
public import Complexitylib.Circuits.OracleInlining.Adaptive

/-!
# Inlining polynomial circuit oracles -- proof internals
-/


public section

namespace Complexity

namespace PolynomialCircuitOracle

/-- Internal proof that the width-selected family members implement the
induced Boolean oracle in every round. -/
theorem implementation_implements_internal {language : Language}
    (circuitOracle : PolynomialCircuitOracle language)
    {inputWidth outputWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (program : AdaptiveOracleProgram inputWidth outputWidth rounds) :
    (circuitOracle.implementation program).Implements circuitOracle.oracle := by
  intro round query
  exact circuitOracle.circuit_eval_eq_oracle query

/-- Internal size identity for each width-selected oracle circuit. -/
theorem implementation_circuit_size_internal {language : Language}
    (circuitOracle : PolynomialCircuitOracle language)
    {inputWidth outputWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (program : AdaptiveOracleProgram inputWidth outputWidth rounds)
    (round : Fin rounds) :
    ((circuitOracle.implementation program).circuit round).size =
      circuitOracle.family.size (program.queryWidth round) := by
  exact circuitOracle.circuit_size_eq_family_size (program.queryWidth round)

end PolynomialCircuitOracle

namespace AdaptiveOracleProgram

/-- Internal semantic correctness of inlining a polynomial circuit oracle. -/
theorem inlineCircuitOracle_eval_internal {language : Language}
    {inputWidth outputWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (program : AdaptiveOracleProgram inputWidth outputWidth rounds)
    (circuitOracle : PolynomialCircuitOracle language)
    (input : BitString inputWidth) :
    (program.inlineCircuitOracle circuitOracle).2.eval input =
      program.eval circuitOracle.oracle input := by
  exact program.inline_eval (circuitOracle.implementation program)
    (circuitOracle.implementation_implements_internal program) input

/-- Internal exact size of a circuit with every oracle call inlined. -/
theorem inlineCircuitOracle_size_internal {language : Language}
    {inputWidth outputWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (program : AdaptiveOracleProgram inputWidth outputWidth rounds)
    (circuitOracle : PolynomialCircuitOracle language) :
    (program.inlineCircuitOracle circuitOracle).2.size =
      program.inlineHistorySize (circuitOracle.implementation program)
        rounds le_rfl + program.final.size := by
  exact program.inline_size (circuitOracle.implementation program)

end AdaptiveOracleProgram

end Complexity
