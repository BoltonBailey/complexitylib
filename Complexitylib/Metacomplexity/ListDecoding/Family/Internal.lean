/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.ListDecoding.Family.Defs
import Complexitylib.Metacomplexity.ListDecoding.Internal

/-!
# Uniform families of finite Boolean list codes -- proof internals
-/


public section

namespace Complexity

namespace BooleanListCodeFamily

theorem length_truthTableBits_internal {coordinateLength : ℕ}
    (word : (Fin coordinateLength → Bool) → Bool) :
    (truthTableBits word).length = 2 ^ coordinateLength := by
  simp [truthTableBits]

theorem length_encoderOutput_internal (family : BooleanListCodeFamily)
    (messageLength inverseAccuracy : ℕ)
    (message : Fin messageLength → Bool) :
    (family.encoderOutput messageLength inverseAccuracy message).length =
      2 ^ family.coordinateLength messageLength inverseAccuracy := by
  exact length_truthTableBits_internal _

theorem length_decoderOutput_internal (family : BooleanListCodeFamily)
    (messageLength inverseAccuracy : ℕ)
    (received :
      (Fin (family.coordinateLength messageLength inverseAccuracy) → Bool) →
        Bool) :
    (family.decoderOutput messageLength inverseAccuracy received).length =
      family.listSize messageLength inverseAccuracy * messageLength := by
  simp [decoderOutput, List.length_flatten, Function.comp_def]

theorem exists_indexBits_of_half_add_inverseAccuracy_internal
    (family : BooleanListCodeFamily)
    (hfamily : family.IsListDecodableAtInverseAccuracy)
    {messageLength inverseAccuracy : ℕ} (haccuracy : 2 ≤ inverseAccuracy)
    (message : Fin messageLength → Bool)
    (received :
      (Fin (family.coordinateLength messageLength inverseAccuracy) → Bool) →
        Bool)
    (hagreement : 1 / 2 + 1 / (inverseAccuracy : ℚ) ≤
      BooleanListCode.agreementProbability
        ((family.code messageLength inverseAccuracy).encode message) received) :
    ∃ bits : List Bool,
      bits.length = BooleanListCode.decoderIndexBitWidth
          (family.listSize messageLength inverseAccuracy) ∧
        (family.code messageLength inverseAccuracy).decodeAtIndexBits?
          received bits = some message := by
  exact BooleanListCode.exists_indexBits_of_half_add_margin_internal
    (hfamily messageLength inverseAccuracy haccuracy) message received hagreement

theorem decoderIndexBitWidth_le_polynomialBound_internal
    {family : BooleanListCodeFamily}
    (bounds : family.PolynomialParameterBounds)
    (messageLength inverseAccuracy : ℕ) :
    BooleanListCode.decoderIndexBitWidth
        (family.listSize messageLength inverseAccuracy) ≤
      Nat.clog 2
        (bounds.listConstant * (inverseAccuracy + 1) ^ bounds.listDegree) := by
  exact Nat.clog_mono_right 2
    (bounds.listSize_le messageLength inverseAccuracy)

theorem length_encoderOutput_le_internal
    {family : BooleanListCodeFamily}
    (bounds : family.PolynomialParameterBounds)
    (messageLength inverseAccuracy : ℕ)
    (message : Fin messageLength → Bool) :
    (family.encoderOutput messageLength inverseAccuracy message).length ≤
      bounds.codewordConstant *
        (messageLength + inverseAccuracy + 1) ^ bounds.codewordDegree := by
  rw [length_encoderOutput_internal]
  exact bounds.codewordLength_le messageLength inverseAccuracy

theorem length_decoderOutput_le_internal
    {family : BooleanListCodeFamily}
    (bounds : family.PolynomialParameterBounds)
    (messageLength inverseAccuracy : ℕ)
    (received :
      (Fin (family.coordinateLength messageLength inverseAccuracy) → Bool) →
        Bool) :
    (family.decoderOutput messageLength inverseAccuracy received).length ≤
      (bounds.listConstant *
        (inverseAccuracy + 1) ^ bounds.listDegree) * messageLength := by
  rw [length_decoderOutput_internal]
  exact Nat.mul_le_mul_right messageLength
    (bounds.listSize_le messageLength inverseAccuracy)

theorem UniformPolynomialTimeRealization.encoder_spec_internal
    {family : BooleanListCodeFamily}
    (realization : family.UniformPolynomialTimeRealization)
    (messageLength inverseAccuracy : ℕ)
    (message : Fin messageLength → Bool) :
    realization.encoderMachine.ProducesInTime
        (encoderInput messageLength inverseAccuracy message)
        (family.encoderOutput messageLength inverseAccuracy message)
        (realization.encoderTime messageLength inverseAccuracy) ∧
      realization.encoderTime messageLength inverseAccuracy ≤
        realization.timeConstant *
          (messageLength + inverseAccuracy + 1) ^ realization.timeDegree := by
  exact ⟨realization.encoder_correct messageLength inverseAccuracy message,
    realization.encoderTime_le messageLength inverseAccuracy⟩

theorem UniformPolynomialTimeRealization.decoder_spec_internal
    {family : BooleanListCodeFamily}
    (realization : family.UniformPolynomialTimeRealization)
    (messageLength inverseAccuracy : ℕ)
    (received :
      (Fin (family.coordinateLength messageLength inverseAccuracy) → Bool) →
        Bool) :
    realization.decoderMachine.ProducesInTime
        (family.decoderInput messageLength inverseAccuracy received)
        (family.decoderOutput messageLength inverseAccuracy received)
        (realization.decoderTime messageLength inverseAccuracy) ∧
      realization.decoderTime messageLength inverseAccuracy ≤
        realization.timeConstant *
          (messageLength + inverseAccuracy + 1) ^ realization.timeDegree := by
  exact ⟨realization.decoder_correct messageLength inverseAccuracy received,
    realization.decoderTime_le messageLength inverseAccuracy⟩

end BooleanListCodeFamily

end Complexity
