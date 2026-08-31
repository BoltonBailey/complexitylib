/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.ApproximateCounting.Relative.OracleProgram.Defs
public import Complexitylib.Classes.PPoly.Oracle.Inlining
import Complexitylib.Classes.PPoly.Oracle
import Complexitylib.Classes.Randomized.ApproximateCounting.Relative.Circuit
import Complexitylib.Circuits.OracleInlining.Adaptive

/-!
# Oracle programs for relative approximate counting -- proof internals
-/


public section

namespace Complexity

namespace ApproximateCounting

namespace Relative

theorem inlineCircuitImplements_internal
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
      (program.inline implementation).2 := by
  intro seed input
  rw [program.inline_eval implementation himplementation]
  exact hprogram seed input

theorem exists_hardwired_accurate_of_mem_PPoly_internal
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
          fixed.size = (program.inlineCircuitOracle circuitOracle).2.size := by
  obtain ⟨circuitOracle⟩ :=
    mem_PPoly_iff_nonempty_polynomialCircuitOracle.mp hlanguage
  have hinlined : CircuitImplements precision (inputWidth + 1) setOfInput
      (program.inlineCircuitOracle circuitOracle).2 :=
    inlineCircuitImplements_internal
      (circuitOracle.implementation program)
      (circuitOracle.implementation_implements program)
      (hprogram circuitOracle.oracle circuitOracle.oracle_decides)
  obtain ⟨fixed, hcorrect, hsize⟩ :=
    exists_hardwired_accurate_circuit hprecision hinlined
  exact ⟨circuitOracle, fixed, hcorrect, hsize⟩

end Relative

end ApproximateCounting

end Complexity
