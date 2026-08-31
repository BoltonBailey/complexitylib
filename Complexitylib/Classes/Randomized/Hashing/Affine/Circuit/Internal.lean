/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.Hashing.Affine.Circuit.Defs
public import Complexitylib.Circuits.Encoding.Fragment
public import Complexitylib.Circuits.Encoding.Parity

/-!
# Circuit fragments for affine Boolean forms -- proof internals
-/


public section

namespace Complexity

namespace PairwiseIndependentHash

namespace AffineCircuit

theorem linearValue_eq_sum_add_internal {width : ℕ}
    (coefficients input : BitString width) (constant : Bool) :
    linearValue coefficients input constant =
      (∑ coordinate, coefficients coordinate * input coordinate) + constant := by
  rw [linearValue, CircuitCode.Parity.foldXor_eq_sum]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.lastCases_last]
  congr 1
  apply Finset.sum_congr rfl
  intro coordinate _
  simp only [Fin.lastCases_castSucc]
  cases coefficients coordinate <;> cases input coordinate <;> rfl

theorem length_productGates_internal (width : ℕ)
    (coefficientRefs inputRefs : Fin width → ℕ) :
    (productGates width coefficientRefs inputRefs).length = width := by
  induction width with
  | zero => simp [productGates]
  | succ width ih => simp [productGates, ih]

private theorem evalAux?_productGates (available width : ℕ)
    (coefficientRefs inputRefs : Fin width → ℕ)
    (coefficients input : BitString width) (wires : Array Bool)
    (hsize : wires.size = available)
    (hcoefficientRefs : ∀ i, coefficientRefs i < available)
    (hinputRefs : ∀ i, inputRefs i < available)
    (hcoefficients : ∀ i, wires[coefficientRefs i]? = some (coefficients i))
    (hinputs : ∀ i, wires[inputRefs i]? = some (input i)) :
    ∃ result,
      CircuitCode.RawCircuit.evalAux?
          (productGates width coefficientRefs inputRefs) wires = some result ∧
      result.size = available + width ∧
      (∀ i < wires.size, result[i]? = wires[i]?) ∧
      ∀ i, result[productWire available i]? =
        some (coefficients i && input i) := by
  induction width generalizing available wires with
  | zero =>
      refine ⟨wires, by simp [productGates, CircuitCode.RawCircuit.evalAux?],
        by simpa using hsize, fun _ _ => rfl, ?_⟩
      exact fun i => Fin.elim0 i
  | succ width ih =>
      let value := coefficients 0 && input 0
      let middle := wires.push value
      have hmiddleSize : middle.size = available + 1 := by
        simp [middle, hsize]
      have hcoefficientTail : ∀ i : Fin width,
          middle[coefficientRefs i.succ]? = some (coefficients i.succ) := by
        intro i
        have hne : coefficientRefs i.succ ≠ wires.size := by
          rw [hsize]
          exact ne_of_lt (hcoefficientRefs i.succ)
        dsimp only [middle]
        rw [Array.getElem?_push, if_neg hne]
        exact hcoefficients i.succ
      have hinputTail : ∀ i : Fin width,
          middle[inputRefs i.succ]? = some (input i.succ) := by
        intro i
        have hne : inputRefs i.succ ≠ wires.size := by
          rw [hsize]
          exact ne_of_lt (hinputRefs i.succ)
        dsimp only [middle]
        rw [Array.getElem?_push, if_neg hne]
        exact hinputs i.succ
      obtain ⟨result, hevalTail, hresultSize, hresultPreserved,
          hresultProducts⟩ :=
        ih (available + 1) (fun i => coefficientRefs i.succ)
          (fun i => inputRefs i.succ) (fun i => coefficients i.succ)
          (fun i => input i.succ) middle hmiddleSize
          (fun i => by exact lt_trans (hcoefficientRefs i.succ) (by omega))
          (fun i => by exact lt_trans (hinputRefs i.succ) (by omega))
          hcoefficientTail hinputTail
      refine ⟨result, ?_, ?_, ?_, ?_⟩
      · simp only [productGates, CircuitCode.RawCircuit.evalAux?,
          CircuitCode.RawGate.eval, hcoefficients 0, hinputs 0,
          Bool.false_xor]
        exact hevalTail
      · omega
      · intro i hi
        have hiMiddle : i < middle.size := by
          rw [hmiddleSize, ← hsize]
          omega
        rw [hresultPreserved i hiMiddle]
        dsimp only [middle]
        rw [Array.getElem?_push, if_neg (ne_of_lt hi)]
      · intro coordinate
        refine Fin.cases ?_ (fun i => ?_) coordinate
        · have hwire : productWire available (0 : Fin (width + 1)) =
              wires.size := by
            simp [productWire, hsize]
          have hwireLt :
              productWire available (0 : Fin (width + 1)) < middle.size := by
            rw [hwire]
            simp [middle]
          rw [hresultPreserved _ hwireLt]
          rw [hwire]
          exact Array.getElem?_push_size
        · have hwire : productWire (available + 1) i =
              productWire available i.succ := by
            simp only [productWire, Fin.val_succ]
            omega
          rw [← hwire]
          exact hresultProducts i

theorem length_compileLinearRaw_internal (available : ℕ) {width : ℕ}
    (coefficientRefs inputRefs : Fin width → ℕ) (constantRef : ℕ) :
    (compileLinearRaw available coefficientRefs inputRefs constantRef).length =
      linearGateCount width := by
  simp [compileLinearRaw, length_productGates_internal,
    CircuitCode.Parity.length_compileRaw, linearGateCount]

theorem outputWire_eq_internal (available : ℕ) {width : ℕ}
    (coefficientRefs inputRefs : Fin width → ℕ) (constantRef : ℕ) :
    outputWire available width =
      available +
        (compileLinearRaw available coefficientRefs inputRefs constantRef).length - 1 := by
  rw [length_compileLinearRaw_internal]
  simp only [outputWire, CircuitCode.Parity.outputWire,
    CircuitCode.Parity.accumulatorWire, linearGateCount]
  omega

theorem evalAux?_compileLinearRaw_internal (available : ℕ) [NeZero available]
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
        some (linearValue coefficients input constant) := by
  obtain ⟨middle, hevalProducts, hmiddleSize, hmiddlePreserved,
      hmiddleProducts⟩ :=
    evalAux?_productGates available width coefficientRefs inputRefs
      coefficients input wires hsize hcoefficientRefs hinputRefs
      hcoefficients hinputs
  let bits : Fin (width + 1) → Bool :=
    Fin.lastCases constant fun coordinate =>
      coefficients coordinate && input coordinate
  have hparityRefs : ∀ i,
      parityRefs (width := width) available constantRef i < available + width := by
    intro i
    refine Fin.lastCases ?_ (fun coordinate => ?_) i
    · simp only [parityRefs, Fin.lastCases_last]
      omega
    · simp only [parityRefs, Fin.lastCases_castSucc, productWire]
      omega
  have hparityInputs : ∀ i,
      middle[parityRefs (width := width) available constantRef i]? =
        some (bits i) := by
    intro i
    refine Fin.lastCases ?_ (fun coordinate => ?_) i
    · simp only [parityRefs, Fin.lastCases_last, bits, Fin.lastCases_last]
      rw [hmiddlePreserved constantRef (by rw [hsize]; exact hconstantRef)]
      exact hconstant
    · simp only [parityRefs, Fin.lastCases_castSucc, bits,
        Fin.lastCases_castSucc]
      exact hmiddleProducts coordinate
  letI : NeZero (available + width) := ⟨by
    have := NeZero.ne available
    omega⟩
  obtain ⟨result, hevalParity, hresultSize, hresultPreserved,
      hresultOutput⟩ :=
    CircuitCode.Parity.evalAux?_compileRaw (available + width)
      (parityRefs (width := width) available constantRef) bits middle
      hmiddleSize hparityRefs hparityInputs
  refine ⟨result, ?_, ?_, ?_, ?_⟩
  · rw [compileLinearRaw, CircuitCode.RawCircuit.evalAux?_append,
      hevalProducts]
    exact hevalParity
  · rw [hresultSize, hmiddleSize, hsize]
    simp only [linearGateCount]
    omega
  · intro i hi
    have hiMiddle : i < middle.size := by
      rw [hmiddleSize]
      rw [hsize] at hi
      omega
    rw [hresultPreserved i hiMiddle]
    exact hmiddlePreserved i hi
  · simpa only [outputWire, linearValue, bits] using hresultOutput

theorem topologicallyWellFormed_compileLinearRaw_internal
    (available : ℕ) [NeZero available] {width : ℕ}
    (coefficientRefs inputRefs : Fin width → ℕ) (constantRef : ℕ)
    (hcoefficientRefs : ∀ i, coefficientRefs i < available)
    (hinputRefs : ∀ i, inputRefs i < available)
    (hconstantRef : constantRef < available) :
    CircuitCode.RawCircuit.TopologicallyWellFormed available
      (compileLinearRaw available coefficientRefs inputRefs constantRef) := by
  let wires := Array.replicate available false
  have hsize : wires.size = available := by simp [wires]
  have hcoefficients : ∀ i, wires[coefficientRefs i]? = some false := by
    intro i
    simp [wires, hcoefficientRefs i]
  have hinputs : ∀ i, wires[inputRefs i]? = some false := by
    intro i
    simp [wires, hinputRefs i]
  have hconstant : wires[constantRef]? = some false := by
    simp [wires, hconstantRef]
  obtain ⟨result, heval, _⟩ :=
    evalAux?_compileLinearRaw_internal available coefficientRefs inputRefs
      constantRef (fun _ => false) (fun _ => false) false wires hsize
      hcoefficientRefs hinputRefs hconstantRef hcoefficients hinputs hconstant
  have htop :=
    (CircuitCode.RawCircuit.evalAux?_isSome_iff
      (compileLinearRaw available coefficientRefs inputRefs constantRef)
      wires).mp (by simp [heval])
  simpa [hsize] using htop

theorem compileLinearRaw_wellFormed_internal
    (available : ℕ) [NeZero available] {width : ℕ}
    (coefficientRefs inputRefs : Fin width → ℕ) (constantRef : ℕ)
    (hcoefficientRefs : ∀ i, coefficientRefs i < available)
    (hinputRefs : ∀ i, inputRefs i < available)
    (hconstantRef : constantRef < available) :
    CircuitCode.RawCircuit.WellFormed available
      (compileLinearRaw available coefficientRefs inputRefs constantRef) := by
  constructor
  · intro hempty
    have hlength := congrArg List.length hempty
    rw [length_compileLinearRaw_internal] at hlength
    simp [linearGateCount] at hlength
  · exact topologicallyWellFormed_compileLinearRaw_internal available
      coefficientRefs inputRefs constantRef hcoefficientRefs hinputRefs
      hconstantRef

theorem linearValue_affineRow_internal {domainWidth rangeWidth : ℕ}
    (seed : BitString (affineSeedWidth domainWidth rangeWidth))
    (input : BitString domainWidth) (row : Fin rangeWidth) :
    linearValue
        (fun coordinate => affineRows seed row coordinate.castSucc)
        input (affineRows seed row (Fin.last domainWidth)) =
      affineEval seed input row := by
  rw [linearValue_eq_sum_add_internal]
  simp only [affineEval]
  rw [Fin.sum_univ_castSucc]
  simp [affineAugment]
  cases affineRows seed row (Fin.last domainWidth) <;> rfl

end AffineCircuit

end PairwiseIndependentHash

end Complexity
