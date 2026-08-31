/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Oracle.Evaluation.OutputMatch.Defs
import Complexitylib.Classes.PPoly.Oracle.Evaluation.OutputMatch.Internal

/-!
# Serialized output-match evaluator queries

This module exposes a source circuit that turns a live raw-gate stream,
evaluator argument, and expected output bit into a tagged circuit-family code.
Composing it with the verified evaluator oracle accepts exactly when the raw
circuit represented by that stream returns the expected bit.
-/


public section

namespace Complexity

namespace CircuitCode

namespace EvaluationOracleCircuit

namespace OutputMatchBranch

/-- Code sources serialize exactly the tagged two-gate output-match extension. -/
theorem eval_codeSources {bodyWidth inputWidth : ℕ} (gateCount : ℕ)
    (body : BitString bodyWidth) (input : BitString inputWidth)
    (expected : Bool) :
    BitString.toList
        (fun coordinate =>
          (codeSources gateCount bodyWidth inputWidth coordinate).eval
            (sourceInput body input expected)) =
      familyCode gateCount inputWidth body.toList expected :=
  eval_codeSources_internal gateCount body input expected

/-- The semantic code value has the exact emitted tagged family code. -/
@[simp] theorem toList_codeValue {bodyWidth inputWidth : ℕ} (gateCount : ℕ)
    (body : BitString bodyWidth) (input : BitString inputWidth)
    (expected : Bool) :
    (codeValue gateCount body input expected).toList =
      familyCode gateCount inputWidth body.toList expected :=
  toList_codeValue_internal gateCount body input expected

/-- The source front end emits the output-match family code followed by its
evaluator argument. -/
theorem eval_queryCircuit {bodyWidth inputWidth : ℕ} (gateCount : ℕ)
    (body : BitString bodyWidth) (input : BitString inputWidth)
    (expected : Bool) :
    (queryCircuit gateCount bodyWidth inputWidth).eval
        (sourceInput body input expected) =
      packedInput (codeValue gateCount body input expected) input :=
  eval_queryCircuit_internal gateCount body input expected

/-- The compiled evaluator branch accepts exactly successful true evaluation
of its tagged output-match code. -/
theorem eval_compile (oracle : PolynomialCircuitOracle circuitEvalLanguage)
    {bodyWidth inputWidth : ℕ} (gateCount : ℕ)
    (body : BitString bodyWidth) (input : BitString inputWidth)
    (expected : Bool) :
    (compile oracle gateCount bodyWidth inputWidth).2.eval
        (sourceInput body input expected) 0 =
      decide
        (evalFamilyCode (familyCode gateCount inputWidth body.toList expected)
          input.toList = some true) :=
  eval_compile_internal oracle gateCount body input expected

/-- Exact width of the tagged family code produced by a gate-stream branch. -/
theorem codeWidth_eq (gateCount bodyWidth inputWidth : ℕ) :
    codeWidth gateCount bodyWidth inputWidth =
      1 + (gateCount + 3) + bodyWidth +
        (5 + 2 * (inputWidth + gateCount - 1)) +
          (5 + 2 * (inputWidth + gateCount)) :=
  codeWidth_eq_internal gateCount bodyWidth inputWidth

/-- The source front end pays one output gate per packed evaluator input bit. -/
theorem size_queryCircuit (gateCount bodyWidth inputWidth : ℕ) :
    (queryCircuit gateCount bodyWidth inputWidth).size =
      packedWidth (codeWidth gateCount bodyWidth inputWidth) inputWidth :=
  size_queryCircuit_internal gateCount bodyWidth inputWidth

/-- Exact cost of source materialization, evaluator pairing, and the selected
oracle-family member. -/
theorem size_compile (oracle : PolynomialCircuitOracle circuitEvalLanguage)
    (gateCount bodyWidth inputWidth : ℕ) :
    (compile oracle gateCount bodyWidth inputWidth).2.size =
      packedWidth (codeWidth gateCount bodyWidth inputWidth) inputWidth +
        queryWidth (codeWidth gateCount bodyWidth inputWidth) inputWidth +
          oracle.family.size
            (queryWidth (codeWidth gateCount bodyWidth inputWidth) inputWidth) :=
  size_compile_internal oracle gateCount bodyWidth inputWidth

/-- A canonical gate stream produces exactly the tagged encoding of its
two-gate live-bit output-match extension. -/
theorem familyCode_eq_appendOutputMatchBit (gateCount inputWidth : ℕ)
    (circuit : RawCircuit) (expected : Bool)
    (hlength : circuit.length = gateCount) :
    familyCode gateCount inputWidth (circuit.flatMap RawGate.encode) expected =
      true :: (circuit.appendOutputMatchBit inputWidth expected).encode :=
  familyCode_eq_appendOutputMatchBit_internal
    gateCount inputWidth circuit expected hlength

/-- On a canonical nonempty gate stream, the compiled branch accepts exactly
when the represented raw circuit returns the live expected bit. -/
theorem eval_compile_gateStream
    (oracle : PolynomialCircuitOracle circuitEvalLanguage)
    {gateCount bodyWidth inputWidth : ℕ} [NeZero inputWidth]
    (body : BitString bodyWidth) (input : BitString inputWidth)
    (expected : Bool) (circuit : RawCircuit)
    (hbody : body.toList = circuit.flatMap RawGate.encode)
    (hlength : circuit.length = gateCount) (hnonempty : circuit ≠ []) :
    (compile oracle gateCount bodyWidth inputWidth).2.eval
        (sourceInput body input expected) 0 =
      decide (circuit.eval? input.toList = some expected) :=
  eval_compile_gateStream_internal oracle body input expected circuit
    hbody hlength hnonempty

end OutputMatchBranch

end EvaluationOracleCircuit

end CircuitCode

end Complexity
