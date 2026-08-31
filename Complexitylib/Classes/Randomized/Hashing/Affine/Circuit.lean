/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.Hashing.Affine.Circuit.Defs
import Complexitylib.Classes.Randomized.Hashing.Affine.Circuit.Internal

/-!
# Circuit fragments for affine Boolean forms

One fragment computes a Boolean affine form over arbitrary existing wires. It
uses one AND gate per linear coefficient and the shared linear-size parity
compiler. Sequential row compilation plus a threshold fragment yields a
linear-size circuit deciding whether the complete affine output is zero.
-/


public section

namespace Complexity

namespace PairwiseIndependentHash

namespace AffineCircuit

/-- The fragment semantics is the usual Boolean-ring dot product plus its
constant coefficient. -/
theorem linearValue_eq_sum_add {width : ℕ}
    (coefficients input : BitString width) (constant : Bool) :
    linearValue coefficients input constant =
      (∑ coordinate, coefficients coordinate * input coordinate) + constant :=
  linearValue_eq_sum_add_internal coefficients input constant

/-- The executable all-zero test agrees with extensional equality to the zero
bit string. -/
theorem zeroValue_eq_decide {width : ℕ} (output : BitString width) :
    zeroValue output = decide (output = fun _ => false) :=
  zeroValue_eq_decide_internal output

/-- An affine-form fragment uses exactly four gates per linear coordinate and
four additional gates. -/
@[simp] theorem length_compileLinearRaw (available : ℕ) {width : ℕ}
    (coefficientRefs inputRefs : Fin width → ℕ) (constantRef : ℕ) :
    (compileLinearRaw available coefficientRefs inputRefs constantRef).length =
      linearGateCount width :=
  length_compileLinearRaw_internal available coefficientRefs inputRefs
    constantRef

/-- The final gate emitted by affine-form compilation carries its value. -/
theorem outputWire_eq (available : ℕ) {width : ℕ}
    (coefficientRefs inputRefs : Fin width → ℕ) (constantRef : ℕ) :
    outputWire available width =
      available +
        (compileLinearRaw available coefficientRefs inputRefs constantRef).length - 1 :=
  outputWire_eq_internal available coefficientRefs inputRefs constantRef

/-- The fragment is topologically ordered when all source references name
pre-existing wires. -/
theorem topologicallyWellFormed_compileLinearRaw
    (available : ℕ) [NeZero available] {width : ℕ}
    (coefficientRefs inputRefs : Fin width → ℕ) (constantRef : ℕ)
    (hcoefficientRefs : ∀ i, coefficientRefs i < available)
    (hinputRefs : ∀ i, inputRefs i < available)
    (hconstantRef : constantRef < available) :
    CircuitCode.RawCircuit.TopologicallyWellFormed available
      (compileLinearRaw available coefficientRefs inputRefs constantRef) :=
  topologicallyWellFormed_compileLinearRaw_internal available
    coefficientRefs inputRefs constantRef hcoefficientRefs hinputRefs
    hconstantRef

/-- The compiled affine form is a nonempty well-formed raw circuit fragment. -/
theorem compileLinearRaw_wellFormed
    (available : ℕ) [NeZero available] {width : ℕ}
    (coefficientRefs inputRefs : Fin width → ℕ) (constantRef : ℕ)
    (hcoefficientRefs : ∀ i, coefficientRefs i < available)
    (hinputRefs : ∀ i, inputRefs i < available)
    (hconstantRef : constantRef < available) :
    CircuitCode.RawCircuit.WellFormed available
      (compileLinearRaw available coefficientRefs inputRefs constantRef) :=
  compileLinearRaw_wellFormed_internal available coefficientRefs inputRefs
    constantRef hcoefficientRefs hinputRefs hconstantRef

/-- Evaluation appends the affine-form value while preserving every existing
wire. -/
theorem evalAux?_compileLinearRaw (available : ℕ) [NeZero available]
    {width : ℕ} (coefficientRefs inputRefs : Fin width → ℕ)
    (constantRef : ℕ) (coefficients input : BitString width)
    (constant : Bool) (wires : Array Bool)
    (hsize : wires.size = available)
    (hcoefficientRefs : ∀ i, coefficientRefs i < available)
    (hinputRefs : ∀ i, inputRefs i < available)
    (hconstantRef : constantRef < available)
    (hcoefficients : ∀ i, wires[coefficientRefs i]? = some (coefficients i))
    (hinputs : ∀ i, wires[inputRefs i]? = some (input i))
    (hconstant : wires[constantRef]? = some constant) :
    ∃ result,
      CircuitCode.RawCircuit.evalAux?
          (compileLinearRaw available coefficientRefs inputRefs constantRef)
          wires = some result ∧
      result.size = wires.size + linearGateCount width ∧
      (∀ i < wires.size, result[i]? = wires[i]?) ∧
      result[outputWire available width]? =
        some (linearValue coefficients input constant) :=
  evalAux?_compileLinearRaw_internal available coefficientRefs inputRefs
    constantRef coefficients input constant wires hsize hcoefficientRefs
    hinputRefs hconstantRef hcoefficients hinputs hconstant

/-- Sequential row compilation has exact additive size. -/
@[simp] theorem length_compileRowsRaw
    (available width rowCount : ℕ)
    (coefficientRefs : Fin rowCount → Fin (width + 1) → ℕ)
    (inputRefs : Fin width → ℕ) :
    (compileRowsRaw available width rowCount coefficientRefs inputRefs).length =
      rowCount * linearGateCount width :=
  length_compileRowsRaw_internal available width rowCount coefficientRefs
    inputRefs

/-- The full affine-zero fragment has its advertised linear gate count. -/
@[simp] theorem length_compileZeroRaw
    (available width rowCount : ℕ)
    (coefficientRefs : Fin rowCount → Fin (width + 1) → ℕ)
    (inputRefs : Fin width → ℕ) :
    (compileZeroRaw available width rowCount coefficientRefs inputRefs).length =
      zeroGateCount width rowCount :=
  length_compileZeroRaw_internal available width rowCount coefficientRefs
    inputRefs

/-- The final gate of full affine-zero compilation carries its decision. -/
theorem zeroOutputWire_eq
    (available width rowCount : ℕ)
    (coefficientRefs : Fin rowCount → Fin (width + 1) → ℕ)
    (inputRefs : Fin width → ℕ) :
    zeroOutputWire available width rowCount =
      available +
        (compileZeroRaw available width rowCount coefficientRefs inputRefs).length - 1 :=
  zeroOutputWire_eq_internal available width rowCount coefficientRefs inputRefs

/-- The full affine-zero fragment is topologically ordered when all matrix and
input references name pre-existing wires. -/
theorem topologicallyWellFormed_compileZeroRaw
    (available width rowCount : ℕ) [NeZero available]
    (coefficientRefs : Fin rowCount → Fin (width + 1) → ℕ)
    (inputRefs : Fin width → ℕ)
    (hcoefficientRefs : ∀ row coordinate,
      coefficientRefs row coordinate < available)
    (hinputRefs : ∀ coordinate, inputRefs coordinate < available) :
    CircuitCode.RawCircuit.TopologicallyWellFormed available
      (compileZeroRaw available width rowCount coefficientRefs inputRefs) :=
  topologicallyWellFormed_compileZeroRaw_internal available width rowCount
    coefficientRefs inputRefs hcoefficientRefs hinputRefs

/-- The full affine-zero builder produces a nonempty well-formed raw circuit. -/
theorem compileZeroRaw_wellFormed
    (available width rowCount : ℕ) [NeZero available]
    (coefficientRefs : Fin rowCount → Fin (width + 1) → ℕ)
    (inputRefs : Fin width → ℕ)
    (hcoefficientRefs : ∀ row coordinate,
      coefficientRefs row coordinate < available)
    (hinputRefs : ∀ coordinate, inputRefs coordinate < available) :
    CircuitCode.RawCircuit.WellFormed available
      (compileZeroRaw available width rowCount coefficientRefs inputRefs) :=
  compileZeroRaw_wellFormed_internal available width rowCount
    coefficientRefs inputRefs hcoefficientRefs hinputRefs

/-- Evaluation preserves the incoming prefix and decides whether every
compiled affine form vanishes. -/
theorem evalAux?_compileZeroRaw
    (available width rowCount : ℕ) [NeZero available]
    (coefficientRefs : Fin rowCount → Fin (width + 1) → ℕ)
    (inputRefs : Fin width → ℕ)
    (coefficients : Fin rowCount → BitString (width + 1))
    (input : BitString width) (wires : Array Bool)
    (hsize : wires.size = available)
    (hcoefficientRefs : ∀ row coordinate,
      coefficientRefs row coordinate < available)
    (hinputRefs : ∀ coordinate, inputRefs coordinate < available)
    (hcoefficients : ∀ row coordinate,
      wires[coefficientRefs row coordinate]? =
        some (coefficients row coordinate))
    (hinputs : ∀ coordinate,
      wires[inputRefs coordinate]? = some (input coordinate)) :
    ∃ result,
      CircuitCode.RawCircuit.evalAux?
          (compileZeroRaw available width rowCount coefficientRefs inputRefs)
          wires = some result ∧
      result.size = wires.size + zeroGateCount width rowCount ∧
      (∀ i < wires.size, result[i]? = wires[i]?) ∧
      result[zeroOutputWire available width rowCount]? =
        some (zeroValue fun row =>
          linearValue
            (fun coordinate => coefficients row coordinate.castSucc)
            input (coefficients row (Fin.last width))) :=
  evalAux?_compileZeroRaw_internal available width rowCount coefficientRefs
    inputRefs coefficients input wires hsize hcoefficientRefs hinputRefs
    hcoefficients hinputs

/-- Direct raw evaluation returns the all-zero decision for the affine forms
selected from the primary input wires. -/
theorem eval?_compileZeroRaw
    (available width rowCount : ℕ) [NeZero available]
    (coefficientRefs : Fin rowCount → Fin (width + 1) → ℕ)
    (inputRefs : Fin width → ℕ)
    (hcoefficientRefs : ∀ row coordinate,
      coefficientRefs row coordinate < available)
    (hinputRefs : ∀ coordinate, inputRefs coordinate < available)
    (input : BitString available) :
    CircuitCode.RawCircuit.eval?
        (compileZeroRaw available width rowCount coefficientRefs inputRefs)
        input.toList =
      some (zeroValue fun row =>
        linearValue
          (fun coordinate => input ⟨coefficientRefs row coordinate.castSucc,
            hcoefficientRefs row coordinate.castSucc⟩)
          (fun coordinate => input ⟨inputRefs coordinate,
            hinputRefs coordinate⟩)
          (input ⟨coefficientRefs row (Fin.last width),
            hcoefficientRefs row (Fin.last width)⟩)) :=
  eval?_compileZeroRaw_internal available width rowCount coefficientRefs
    inputRefs hcoefficientRefs hinputRefs input

/-- Specializing the generic affine form to one row of the standard seed
matrix agrees with `affineEval`. -/
theorem linearValue_affineRow {domainWidth rangeWidth : ℕ}
    (seed : BitString (affineSeedWidth domainWidth rangeWidth))
    (input : BitString domainWidth) (row : Fin rangeWidth) :
    linearValue
        (fun coordinate => affineRows seed row coordinate.castSucc)
        input (affineRows seed row (Fin.last domainWidth)) =
      affineEval seed input row :=
  linearValue_affineRow_internal seed input row

/-- The all-zero value of the compiled matrix rows is exactly the affine
zero-cell predicate. -/
theorem zeroValue_affineEval {domainWidth rangeWidth : ℕ}
    (seed : BitString (affineSeedWidth domainWidth rangeWidth))
    (input : BitString domainWidth) :
    zeroValue (fun row =>
      linearValue
        (fun coordinate => affineRows seed row coordinate.castSucc)
        input (affineRows seed row (Fin.last domainWidth))) =
      decide (affineEval seed input = fun _ => false) :=
  zeroValue_affineEval_internal seed input

end AffineCircuit

end PairwiseIndependentHash

end Complexity
