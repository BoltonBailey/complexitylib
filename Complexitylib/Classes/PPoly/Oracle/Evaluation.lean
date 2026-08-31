/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Oracle.Evaluation.Defs
import Complexitylib.Classes.PPoly.Oracle.Evaluation.Internal

/-!
# Serialized evaluation circuits from polynomial circuit oracles

The fixed-layout compiler below decides successful true evaluation of an
arbitrary tagged family code. Malformed codes and successful false evaluations
both return false, exactly as in `circuitEvalLanguage`.
-/


public section

namespace Complexity

namespace CircuitCode

namespace EvaluationOracleCircuit

/-- The query front end serializes exactly the family-code and argument blocks
supplied in the packed ordinary input. -/
theorem eval_queryCircuit
    {codeWidth inputWidth : ℕ} [NeZero codeWidth]
    (code : BitString codeWidth) (input : BitString inputWidth) :
    BitString.toList
        ((queryCircuit codeWidth inputWidth).eval (packedInput code input)) =
      pair code.toList input.toList :=
  eval_queryCircuit_internal code input

/-- The compiled evaluator circuit accepts exactly successful true evaluation
of the supplied tagged family code. -/
theorem eval_compile
    (oracle : PolynomialCircuitOracle circuitEvalLanguage)
    {codeWidth inputWidth : ℕ} [NeZero codeWidth]
    (code : BitString codeWidth) (input : BitString inputWidth) :
    (compile oracle codeWidth inputWidth).2.eval (packedInput code input) 0 =
      decide (evalFamilyCode code.toList input.toList = some true) :=
  eval_compile_internal oracle code input

/-- Exact cost of the fixed pairing front end and selected evaluator-oracle
family member. -/
theorem size_compile
    (oracle : PolynomialCircuitOracle circuitEvalLanguage)
    (codeWidth inputWidth : ℕ) [NeZero codeWidth] :
    (compile oracle codeWidth inputWidth).2.size =
      queryWidth codeWidth inputWidth +
        oracle.family.size (queryWidth codeWidth inputWidth) :=
  size_compile_internal oracle codeWidth inputWidth

end EvaluationOracleCircuit

end CircuitCode

end Complexity
