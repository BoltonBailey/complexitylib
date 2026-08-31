/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.ApproximateCounting.Relative.OracleProgram.Defs
public import Complexitylib.Classes.PPoly.Oracle.Inlining
import Complexitylib.Classes.Randomized.ApproximateCounting.Relative.OracleProgram.Internal

/-!
# Oracle programs for relative approximate counting

Inlining exact oracle circuits preserves the hashing estimator semantics.
Consequently, a program using any language in `P/poly` yields an ordinary
circuit that becomes accurate on all inputs after one random seed is fixed.
-/


public section

namespace Complexity

namespace ApproximateCounting

namespace Relative

/-- Inlining an exact implementation of the Boolean oracle preserves the
program's relative-estimator semantics. -/
theorem inlineCircuitImplements
    {inputWidth outputWidth domainWidth rounds precision failureBits : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    {setOfInput : BitString inputWidth → Finset (BitString domainWidth)}
    {program : AdaptiveOracleProgram
      (seedWidth domainWidth precision failureBits + inputWidth)
      outputWidth rounds}
    {oracle : BooleanOracle}
    (implementation : program.OracleCircuitImplementation)
    (himplementation : implementation.Implements oracle)
    (hprogram : OracleProgramImplements precision failureBits setOfInput
      program oracle) :
    CircuitImplements precision failureBits setOfInput
      (program.inline implementation).2 :=
  inlineCircuitImplements_internal implementation himplementation hprogram

/-- If the program's oracle language is in `P/poly`, oracle inlining followed
by seed fixing produces one ordinary circuit accurate on every input. -/
theorem exists_hardwired_accurate_of_mem_PPoly
    {language : Language}
    {inputWidth outputWidth domainWidth rounds precision : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    {setOfInput : BitString inputWidth → Finset (BitString domainWidth)}
    (program : AdaptiveOracleProgram
      (seedWidth domainWidth precision (inputWidth + 1) + inputWidth)
      outputWidth rounds)
    (hprecision : 0 < precision) (hlanguage : language ∈ PPoly)
    (hprogram : ∀ oracle, oracle.Decides language →
      OracleProgramImplements precision (inputWidth + 1) setOfInput
        program oracle) :
    ∃ circuitOracle : PolynomialCircuitOracle language,
      ∃ fixed : Circuit Basis.andOr2 inputWidth outputWidth
        (program.inlineCircuitOracle circuitOracle).1,
        (∀ input, OutputIsAccurate precision setOfInput input
          (fixed.eval input)) ∧
          fixed.size = (program.inlineCircuitOracle circuitOracle).2.size :=
  exists_hardwired_accurate_of_mem_PPoly_internal
    program hprecision hlanguage hprogram

end Relative

end ApproximateCounting

end Complexity
