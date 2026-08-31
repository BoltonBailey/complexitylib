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
compiler, giving exact size, topological, and evaluation guarantees.
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

end AffineCircuit

end PairwiseIndependentHash

end Complexity
