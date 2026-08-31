/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.Hashing.Affine.Defs
public import Complexitylib.Circuits.Encoding.Parity.Defs
public import Complexitylib.Circuits.Encoding.Threshold.Defs

/-!
# Circuit fragments for affine Boolean forms -- definitions

This module compiles affine Boolean forms over existing circuit wires. Each row
uses one shared AND gate per coefficient/input pair followed by the linear-size
parity fragment. The multi-row builder appends a linear threshold test deciding
whether every affine output bit is zero.
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

/-- Wire count available before compiling the selected affine row. -/
def rowAvailable (available width row : ℕ) : ℕ :=
  available + row * linearGateCount width

/-- Absolute output wire of one row in a sequential affine matrix build. -/
def rowOutputWire (available width : ℕ) {rowCount : ℕ}
    (row : Fin rowCount) : ℕ :=
  outputWire (rowAvailable available width row.val) width

/-- Compile every row of an affine Boolean matrix, retaining one output wire
per row. -/
def compileRowsRaw (available width : ℕ) :
    (rowCount : ℕ) →
      (Fin rowCount → Fin (width + 1) → ℕ) →
      (Fin width → ℕ) → CircuitCode.RawCircuit
  | 0, _, _ => []
  | rowCount + 1, coefficientRefs, inputRefs =>
      compileLinearRaw available
          (fun coordinate => coefficientRefs 0 coordinate.castSucc)
          inputRefs (coefficientRefs 0 (Fin.last width)) ++
        compileRowsRaw (available + linearGateCount width) width rowCount
          (fun row coordinate => coefficientRefs row.succ coordinate)
          inputRefs

/-- Boolean value asserting that every coordinate of a fixed-width output is
zero. -/
def zeroValue {width : ℕ} (output : BitString width) : Bool :=
  !(decide (1 ≤ Fin.countP output))

/-- Wire count available after all affine rows have been compiled. -/
def rowsAvailable (available width rowCount : ℕ) : ℕ :=
  available + rowCount * linearGateCount width

/-- Exact gate count of the full affine-zero fragment. -/
def zeroGateCount (width rowCount : ℕ) : ℕ :=
  rowCount * linearGateCount width + (4 + 2 * rowCount)

/-- Absolute wire carrying the full affine-zero decision. -/
def zeroOutputWire (available width rowCount : ℕ) : ℕ :=
  CircuitCode.Threshold.outputWire
      (rowsAvailable available width rowCount) rowCount 1 + 1

/-- Compile all affine rows and return true exactly when every row is zero. -/
def compileZeroRaw (available width rowCount : ℕ)
    (coefficientRefs : Fin rowCount → Fin (width + 1) → ℕ)
    (inputRefs : Fin width → ℕ) : CircuitCode.RawCircuit :=
  let afterRows := rowsAvailable available width rowCount
  let outputs : Fin rowCount → ℕ := rowOutputWire available width
  compileRowsRaw available width rowCount coefficientRefs inputRefs ++
    CircuitCode.Threshold.compileRaw (inputCount := rowCount)
      afterRows 1 outputs ++
      [CircuitCode.RawGate.copy
        (CircuitCode.Threshold.outputWire afterRows rowCount 1) true]

end AffineCircuit

end PairwiseIndependentHash

end Complexity
