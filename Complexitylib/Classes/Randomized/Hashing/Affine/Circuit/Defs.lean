/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.Hashing.Affine.Defs
public import Complexitylib.Circuits.Encoding.Parity.Defs

/-!
# Circuit fragments for affine Boolean forms -- definitions

This module compiles one affine Boolean form over existing circuit wires. It
first emits one shared AND gate per coefficient/input pair and then applies the
linear-size parity fragment to those products and one constant coefficient.
-/


@[expose] public section

namespace Complexity

namespace PairwiseIndependentHash

namespace AffineCircuit

/-- Semantic value of one affine Boolean form. -/
def linearValue {width : ℕ} (coefficients input : BitString width)
    (constant : Bool) : Bool :=
  CircuitCode.Parity.foldXor (width + 1) <|
    Fin.lastCases constant fun coordinate =>
      coefficients coordinate && input coordinate

/-- One product gate per coefficient/input coordinate. -/
def productGates : (width : ℕ) →
    (Fin width → ℕ) → (Fin width → ℕ) → CircuitCode.RawCircuit
  | 0, _, _ => []
  | width + 1, coefficientRefs, inputRefs =>
      { op := .and
        input₀ := coefficientRefs 0
        input₁ := inputRefs 0
        negated₀ := false
        negated₁ := false } ::
      productGates width (fun coordinate => coefficientRefs coordinate.succ)
        (fun coordinate => inputRefs coordinate.succ)

/-- Wire emitted for one coefficient/input product. -/
def productWire (available : ℕ) {width : ℕ} (coordinate : Fin width) : ℕ :=
  available + coordinate.val

/-- Inputs to the parity stage: all product wires followed by the constant
coefficient. -/
def parityRefs (available constantRef : ℕ) {width : ℕ} :
    Fin (width + 1) → ℕ :=
  Fin.lastCases constantRef (productWire available)

/-- Exact gate count of one compiled affine Boolean form. -/
def linearGateCount (width : ℕ) : ℕ :=
  width + (1 + 3 * (width + 1))

/-- Absolute wire carrying the compiled affine-form value. -/
def outputWire (available width : ℕ) : ℕ :=
  CircuitCode.Parity.outputWire (available + width) (width + 1)

/-- Compile one affine Boolean form over existing coefficient, input, and
constant wires. -/
def compileLinearRaw (available : ℕ) {width : ℕ}
    (coefficientRefs inputRefs : Fin width → ℕ) (constantRef : ℕ) :
    CircuitCode.RawCircuit :=
  productGates width coefficientRefs inputRefs ++
    CircuitCode.Parity.compileRaw (inputCount := width + 1)
      (available + width) (parityRefs (width := width) available constantRef)

end AffineCircuit

end PairwiseIndependentHash

end Complexity
