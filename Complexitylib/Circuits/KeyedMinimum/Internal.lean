/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.KeyedMinimum.Defs
public import Complexitylib.Circuits.Composition
public import Complexitylib.Circuits.InputProjection
public import Complexitylib.Circuits.InputReindexing
public import Complexitylib.Circuits.Multiplexer

/-!
# Keyed unsigned minimum -- proof internals
-/


public section

namespace Complexity

namespace Circuit

private theorem keyedMinimumComparisonInput_precompose
    {keyWidth payloadWidth : ℕ}
    (leftKey : BitString keyWidth) (leftPayload : BitString payloadWidth)
    (rightKey : BitString keyWidth) (rightPayload : BitString payloadWidth) :
    BitString.keyedMinimumInput leftKey leftPayload rightKey rightPayload ∘
        keyedMinimumComparisonInput keyWidth payloadWidth =
      Fin.append leftKey rightKey := by
  funext input
  refine Fin.addCases ?_ ?_ input
  · intro key
    simp [BitString.keyedMinimumInput, keyedMinimumComparisonInput]
  · intro key
    simp only [keyedMinimumComparisonInput, Fin.addCases_right,
      BitString.keyedMinimumInput, Function.comp_apply,
      Fin.append_right, Fin.append_left]

theorem eval_unsignedLEWithKeyedPayload_internal
    (keyWidth payloadWidth : ℕ) [NeZero keyWidth]
    (leftKey : BitString keyWidth) (leftPayload : BitString payloadWidth)
    (rightKey : BitString keyWidth) (rightPayload : BitString payloadWidth) :
    (unsignedLEWithKeyedPayload keyWidth payloadWidth).eval
        (BitString.keyedMinimumInput
          leftKey leftPayload rightKey rightPayload) =
      BitString.multiplexerInput
        (decide (leftKey.unsignedValue ≤ rightKey.unsignedValue))
        (Fin.append leftKey leftPayload) (Fin.append rightKey rightPayload) := by
  unfold unsignedLEWithKeyedPayload
  rw [Circuit.eval_parallel]
  rw [Circuit.eval_reindexInputs]
  rw [Circuit.eval_projectInputs]
  rw [keyedMinimumComparisonInput_precompose]
  funext index
  refine Fin.addCases ?_ ?_ index
  · intro comparison
    have hcomparison : comparison = 0 := Subsingleton.elim _ _
    subst comparison
    simp [BitString.multiplexerInput]
  · intro payload
    simp [BitString.keyedMinimumInput, BitString.multiplexerInput,
      Function.comp_def]

theorem eval_unsignedKeyedMin_internal
    (keyWidth payloadWidth : ℕ) [NeZero keyWidth]
    (leftKey : BitString keyWidth) (leftPayload : BitString payloadWidth)
    (rightKey : BitString keyWidth) (rightPayload : BitString payloadWidth) :
    (unsignedKeyedMin keyWidth payloadWidth).eval
        (BitString.keyedMinimumInput
          leftKey leftPayload rightKey rightPayload) =
      BitString.unsignedKeyedMin
        leftKey leftPayload rightKey rightPayload := by
  unfold unsignedKeyedMin
  rw [Circuit.eval_compose]
  rw [eval_unsignedLEWithKeyedPayload_internal]
  rw [Circuit.eval_multiplexer]
  simp [BitString.unsignedKeyedMin]

end Circuit

end Complexity
