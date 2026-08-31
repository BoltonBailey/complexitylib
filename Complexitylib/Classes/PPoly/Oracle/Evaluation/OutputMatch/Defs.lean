/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Oracle.Evaluation.Defs
public import Complexitylib.Circuits.Encoding.Fragment.Defs

/-!
# Serialized output-match evaluator queries -- definitions

A fixed gate count lets a live raw-gate stream be extended by the two-gate
output-match fragment without computing on its code bits. The source circuit
copies that stream, inserts the incremented count and fixed gate fields, and
uses the live expected bit positively in both negation fields of the mismatch
gate. The resulting tagged family code and its argument feed the verified
serialized evaluator oracle.
-/


@[expose] public section

namespace Complexity

namespace CircuitCode

namespace EvaluationOracleCircuit

namespace OutputMatchBranch

/-- Input width of a raw-gate body, evaluator argument, and expected bit. -/
def sourceInputWidth (bodyWidth inputWidth : ℕ) : ℕ :=
  bodyWidth + (inputWidth + 1)

instance (bodyWidth inputWidth : ℕ) :
    NeZero (sourceInputWidth bodyWidth inputWidth) :=
  ⟨by simp [sourceInputWidth]⟩

/-- Source of one raw-gate-body bit. -/
def bodySource (bodyWidth inputWidth : ℕ) (coordinate : Fin bodyWidth) :
    Circuit.InputSource (sourceInputWidth bodyWidth inputWidth) :=
  .input (Fin.castAdd (inputWidth + 1) coordinate)

/-- Source of one evaluator-argument bit. -/
def argumentSource (bodyWidth inputWidth : ℕ) (coordinate : Fin inputWidth) :
    Circuit.InputSource (sourceInputWidth bodyWidth inputWidth) :=
  .input (Fin.natAdd bodyWidth coordinate.castSucc)

/-- Source of the expected output bit after the evaluator argument. -/
def expectedSource (bodyWidth inputWidth : ℕ) :
    Circuit.InputSource (sourceInputWidth bodyWidth inputWidth) :=
  .input (Fin.natAdd bodyWidth (Fin.last inputWidth))

/-- Pack a raw-gate body, evaluator argument, and expected output bit. -/
def sourceInput {bodyWidth inputWidth : ℕ}
    (body : BitString bodyWidth) (input : BitString inputWidth)
    (expected : Bool) : BitString (sourceInputWidth bodyWidth inputWidth) :=
  Fin.append body (Fin.lastCases expected input)

/-- Materialize fixed bits as constant circuit sources. -/
def constantSources {sourceWidth : ℕ} (bits : List Bool) :
    List (Circuit.InputSource sourceWidth) :=
  bits.map Circuit.InputSource.constant

/-- Source-level encoding of a copy gate with one live negation bit. -/
def liveCopySources {sourceWidth : ℕ} (wire : ℕ)
    (negated : Circuit.InputSource sourceWidth) :
    List (Circuit.InputSource sourceWidth) :=
  [.constant true, negated, negated] ++
    constantSources (NatCode.encode wire) ++
      constantSources (NatCode.encode wire)

/-- Source list spelling the tagged family code for a live-bit output match. -/
def codeSourceList (gateCount bodyWidth inputWidth : ℕ) :
    List (Circuit.InputSource (sourceInputWidth bodyWidth inputWidth)) :=
  [.constant true] ++
    constantSources (NatCode.encode (gateCount + 2)) ++
      List.ofFn (bodySource bodyWidth inputWidth) ++
        liveCopySources (inputWidth + gateCount - 1)
          (expectedSource bodyWidth inputWidth) ++
          constantSources
            (RawGate.copy (inputWidth + gateCount) true).encode

/-- Width of the tagged output-match family code. -/
def codeWidth (gateCount bodyWidth inputWidth : ℕ) : ℕ :=
  (codeSourceList gateCount bodyWidth inputWidth).length

instance (gateCount bodyWidth inputWidth : ℕ) :
    NeZero (codeWidth gateCount bodyWidth inputWidth) :=
  ⟨by simp [codeWidth, codeSourceList]⟩

/-- Fixed-width view of the output-match code source list. -/
def codeSources (gateCount bodyWidth inputWidth : ℕ) :
    Fin (codeWidth gateCount bodyWidth inputWidth) →
      Circuit.InputSource (sourceInputWidth bodyWidth inputWidth) :=
  fun coordinate =>
    (codeSourceList gateCount bodyWidth inputWidth)[coordinate.val]'coordinate.isLt

/-- Output-match family-code sources followed by argument sources. -/
def querySources (gateCount bodyWidth inputWidth : ℕ) :
    Fin (packedWidth (codeWidth gateCount bodyWidth inputWidth) inputWidth) →
      Circuit.InputSource (sourceInputWidth bodyWidth inputWidth) :=
  Fin.append (codeSources gateCount bodyWidth inputWidth)
    (argumentSource bodyWidth inputWidth)

/-- Source circuit producing the evaluator adapter's packed input. -/
def queryCircuit (gateCount bodyWidth inputWidth : ℕ) :
    Circuit Basis.andOr2 (sourceInputWidth bodyWidth inputWidth)
      (packedWidth (codeWidth gateCount bodyWidth inputWidth) inputWidth) 0 :=
  Circuit.inputSources (querySources gateCount bodyWidth inputWidth)

/-- Compose the output-match query sources with the serialized evaluator
oracle member selected by their exact width. -/
def compile (oracle : PolynomialCircuitOracle circuitEvalLanguage)
    (gateCount bodyWidth inputWidth : ℕ) :
    Σ internalGates,
      Circuit Basis.andOr2 (sourceInputWidth bodyWidth inputWidth) 1 internalGates :=
  let query := queryCircuit gateCount bodyWidth inputWidth
  let evaluator :=
    EvaluationOracleCircuit.compile oracle
      (codeWidth gateCount bodyWidth inputWidth) inputWidth
  ⟨_, evaluator.2.compose query⟩

/-- Semantic tagged family code emitted for a gate body and expected bit. -/
def familyCode (gateCount inputWidth : ℕ) (body : List Bool)
    (expected : Bool) : List Bool :=
  true ::
    (NatCode.encode (gateCount + 2) ++ body ++
      (RawGate.copy (inputWidth + gateCount - 1) expected).encode ++
        (RawGate.copy (inputWidth + gateCount) true).encode)

/-- Semantic family-code bit string produced by the code sources. -/
def codeValue {bodyWidth inputWidth : ℕ} (gateCount : ℕ)
    (body : BitString bodyWidth) (input : BitString inputWidth)
    (expected : Bool) : BitString (codeWidth gateCount bodyWidth inputWidth) :=
  fun coordinate =>
    (codeSources gateCount bodyWidth inputWidth coordinate).eval
      (sourceInput body input expected)

end OutputMatchBranch

end EvaluationOracleCircuit

end CircuitCode

end Complexity
