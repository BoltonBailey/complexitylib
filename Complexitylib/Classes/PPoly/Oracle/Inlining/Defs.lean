/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Oracle.Defs
public import Complexitylib.Circuits.OracleInlining.Adaptive.Defs

/-!
# Inlining polynomial circuit oracles -- definitions

For each round of an adaptive oracle program, a polynomial circuit oracle
selects the family member at that round's query width. The generic adaptive
compiler then replaces all oracle calls by those selected circuits.
-/


@[expose] public section

namespace Complexity

namespace PolynomialCircuitOracle

/-- Select the circuit-family member matching each query width of an adaptive
oracle program. -/
def implementation {language : Language}
    (circuitOracle : PolynomialCircuitOracle language)
    {inputWidth outputWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (program : AdaptiveOracleProgram inputWidth outputWidth rounds) :
    program.OracleCircuitImplementation where
  internalGates round :=
    circuitOracle.family.internalGateCount (program.queryWidth round)
  circuit round :=
    circuitOracle.family.circuit (program.queryWidth round)

end PolynomialCircuitOracle

namespace AdaptiveOracleProgram

/-- Replace every oracle call in `program` by the matching member of a
polynomial-size circuit oracle. -/
def inlineCircuitOracle {language : Language}
    {inputWidth outputWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (program : AdaptiveOracleProgram inputWidth outputWidth rounds)
    (circuitOracle : PolynomialCircuitOracle language) :
    Σ internalGates,
      Circuit Basis.andOr2 inputWidth outputWidth internalGates :=
  program.inline (circuitOracle.implementation program)

end AdaptiveOracleProgram

end Complexity
