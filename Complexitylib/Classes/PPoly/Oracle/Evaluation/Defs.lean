/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Oracle.Defs
public import Complexitylib.Circuits.Composition.Defs
public import Complexitylib.Circuits.Encoding.Machine.Defs
public import Complexitylib.Circuits.InputPairing.Defs

/-!
# Serialized evaluation circuits from polynomial circuit oracles -- definitions

A polynomial circuit oracle for the verified serialized evaluator can be
specialized to fixed family-code and argument widths. A zero-internal-gate
front end pairs the two input blocks, and ordinary circuit composition feeds
that canonical query to the matching oracle-family member.
-/


@[expose] public section

namespace Complexity

namespace CircuitCode

namespace EvaluationOracleCircuit

/-- Input width of a fixed-layout family-code and argument pair. -/
def packedWidth (codeWidth inputWidth : ℕ) : ℕ :=
  codeWidth + inputWidth

instance (codeWidth inputWidth : ℕ) [NeZero codeWidth] :
    NeZero (packedWidth codeWidth inputWidth) :=
  ⟨by simp [packedWidth, NeZero.ne codeWidth]⟩

/-- Serialized query width after applying the canonical pairing codec. -/
def queryWidth (codeWidth inputWidth : ℕ) : ℕ :=
  Circuit.pairSourceWidth codeWidth inputWidth

instance (codeWidth inputWidth : ℕ) :
    NeZero (queryWidth codeWidth inputWidth) :=
  inferInstanceAs (NeZero (Circuit.pairSourceWidth codeWidth inputWidth))

/-- Source of one family-code bit in the packed ordinary input. -/
def codeSource (codeWidth inputWidth : ℕ) (coordinate : Fin codeWidth) :
    Circuit.InputSource (packedWidth codeWidth inputWidth) :=
  .input (Fin.castAdd inputWidth coordinate)

/-- Source of one argument bit in the packed ordinary input. -/
def inputSource (codeWidth inputWidth : ℕ) (coordinate : Fin inputWidth) :
    Circuit.InputSource (packedWidth codeWidth inputWidth) :=
  .input (Fin.natAdd codeWidth coordinate)

/-- Canonical paired evaluator query produced from the two packed blocks. -/
def queryCircuit (codeWidth inputWidth : ℕ) [NeZero codeWidth] :
    Circuit Basis.andOr2 (packedWidth codeWidth inputWidth)
      (queryWidth codeWidth inputWidth) 0 :=
  Circuit.pairInputSources (codeSource codeWidth inputWidth)
    (inputSource codeWidth inputWidth)

/-- Pack a fixed-width family code before its fixed-width argument. -/
def packedInput {codeWidth inputWidth : ℕ}
    (code : BitString codeWidth) (input : BitString inputWidth) :
    BitString (packedWidth codeWidth inputWidth) :=
  Fin.append code input

/-- Compose the fixed-layout query front end with the evaluator-oracle member
at the resulting serialized query width. -/
def compile
    (oracle : PolynomialCircuitOracle circuitEvalLanguage)
    (codeWidth inputWidth : ℕ) [NeZero codeWidth] :
    Σ internalGates,
      Circuit Basis.andOr2 (packedWidth codeWidth inputWidth) 1 internalGates :=
  let query := queryCircuit codeWidth inputWidth
  let evaluator := oracle.family.circuit (queryWidth codeWidth inputWidth)
  ⟨_, evaluator.compose query⟩

end EvaluationOracleCircuit

end CircuitCode

end Complexity
