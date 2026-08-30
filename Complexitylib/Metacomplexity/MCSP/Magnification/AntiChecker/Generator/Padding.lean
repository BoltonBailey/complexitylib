/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Padding.Defs
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Padding.Internal

/-!
# Anti-checker generator output padding

This module exposes the exact semantics and size of the circuit that prepends
zero sample rows to the selected inputs. The padded circuit therefore prints
the canonical `AntiChecker.padInputsTo` list at the published sample count.
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- Unpacking one row after packed zero padding gives the corresponding row
of the appended zero-and-source tuple. -/
theorem unpackSample_padPackedSamples
    {sourceCount targetCount arity : ℕ}
    (hbudget : sourceCount ≤ targetCount)
    (input : BitString (sourceCount * arity)) (sample : Fin targetCount) :
    unpackSample (padPackedSamples hbudget input) sample =
      Fin.append
        (fun _ : Fin (targetCount - sourceCount) =>
          (fun _ : Fin arity => false))
        (unpackSample input)
        (Fin.cast (Nat.sub_add_cancel hbudget).symm sample) :=
  unpackSample_padPackedSamples_internal hbudget input sample

/-- Unpacking every row after packed zero padding agrees exactly with the
canonical list-level padding operation. -/
theorem unpackSamples_padPackedSamples
    {sourceCount targetCount arity : ℕ}
    (hbudget : sourceCount ≤ targetCount)
    (input : BitString (sourceCount * arity)) :
    unpackSamples (padPackedSamples hbudget input) =
      AntiChecker.padInputsTo targetCount (unpackSamples input) :=
  unpackSamples_padPackedSamples_internal hbudget input

/-- The zero-internal-gate padding circuit computes packed zero padding
exactly. -/
@[simp] theorem eval_packedSamplePaddingCircuit
    {sourceCount targetCount arity : ℕ}
    [NeZero (sourceCount * arity)] [NeZero (targetCount * arity)]
    (hbudget : sourceCount ≤ targetCount)
    (input : BitString (sourceCount * arity)) :
    (packedSamplePaddingCircuit (arity := arity) hbudget).eval input =
      padPackedSamples hbudget input :=
  eval_packedSamplePaddingCircuit_internal hbudget input

/-- Packed padding costs exactly one output gate per target output bit and no
internal gates. -/
@[simp] theorem size_packedSamplePaddingCircuit
    {sourceCount targetCount arity : ℕ}
    [NeZero (sourceCount * arity)] [NeZero (targetCount * arity)]
    (hbudget : sourceCount ≤ targetCount) :
    (packedSamplePaddingCircuit (arity := arity) hbudget).size =
      targetCount * arity :=
  size_packedSamplePaddingCircuit_internal hbudget

/-- The padded selection circuit first computes the required-round samples
and then prepends their packed zero rows. -/
@[simp] theorem eval_paddedSelectionCircuit
    {overhead arity : ℕ} {beta : PositiveRationalScale} [NeZero arity]
    (family : ApproximateCounterFamily overhead beta arity)
    (hbudget : requiredRoundCount beta arity ≤ sampleCount beta arity)
    (table : BitString (2 ^ arity)) :
    (paddedSelectionCircuit family hbudget).2.eval table =
      padPackedSamples hbudget
        ((fullSelectionSamplesCircuit family).2.eval table) :=
  eval_paddedSelectionCircuit_internal family hbudget table

/-- Padding adds exactly the published output width to the unpadded selection
circuit's size. -/
@[simp] theorem size_paddedSelectionCircuit
    {overhead arity : ℕ} {beta : PositiveRationalScale} [NeZero arity]
    (family : ApproximateCounterFamily overhead beta arity)
    (hbudget : requiredRoundCount beta arity ≤ sampleCount beta arity) :
    (paddedSelectionCircuit family hbudget).2.size =
      (fullSelectionSamplesCircuit family).2.size +
        outputBitCount beta arity :=
  size_paddedSelectionCircuit_internal family hbudget

/-- On a target truth table, the padded circuit prints the canonical padding
of a full greedy estimate-selection trace. -/
theorem exists_eval_paddedSelectionCircuit_isEstimateSelectionTrace
    {overhead arity : ℕ} {beta : PositiveRationalScale} [NeZero arity]
    (family : ApproximateCounterFamily overhead beta arity)
    (hbudget : requiredRoundCount beta arity ≤ sampleCount beta arity)
    (target : BitString arity → Bool) :
    ∃ inputs : Fin (requiredRoundCount beta arity) → BitString arity,
      unpackSamples
          ((paddedSelectionCircuit family hbudget).2.eval
            (truthTable target)) =
          AntiChecker.padInputsTo (sampleCount beta arity)
            (List.ofFn inputs) ∧
        AntiChecker.IsEstimateSelectionTrace
          (family.extensionEstimator target) (List.ofFn inputs) :=
  exists_eval_paddedSelectionCircuit_isEstimateSelectionTrace_internal
    family hbudget target

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
