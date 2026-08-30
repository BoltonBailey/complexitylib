/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Encoding.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Encoding.Internal

/-!
# Anti-checker counter encodings

This module exposes the exact fixed-width interface between labeled sample
prefixes and the approximate counter circuits used by the Anti-Checker Lemma.
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- Input coordinate `j` of packed sample `i` is stored at row-major position
`(i, j)`. -/
@[simp] theorem packLabeledSamples_input {count arity : ℕ}
    (samples : Fin count → SuccinctMCSP.Sample arity)
    (sample : Fin count) (coordinate : Fin arity) :
    packLabeledSamples samples
        (finProdFinEquiv (sample, coordinate.castSucc)) =
      (samples sample).input coordinate :=
  packLabeledSamples_input_internal samples sample coordinate

/-- The last coordinate of each packed sample row stores its output label. -/
@[simp] theorem packLabeledSamples_output {count arity : ℕ}
    (samples : Fin count → SuccinctMCSP.Sample arity)
    (sample : Fin count) :
    packLabeledSamples samples
        (finProdFinEquiv (sample, Fin.last arity)) =
      (samples sample).output :=
  packLabeledSamples_output_internal samples sample

/-- Unpacking one row after packing recovers the original labeled sample. -/
@[simp] theorem unpackLabeledSample_packLabeledSamples
    {count arity : ℕ}
    (samples : Fin count → SuccinctMCSP.Sample arity)
    (sample : Fin count) :
    unpackLabeledSample (packLabeledSamples samples) sample =
      samples sample :=
  unpackLabeledSample_packLabeledSamples_internal samples sample

/-- Unpacking after packing recovers the complete labeled-sample vector. -/
@[simp] theorem unpackLabeledSamples_packLabeledSamples
    {count arity : ℕ}
    (samples : Fin count → SuccinctMCSP.Sample arity) :
    unpackLabeledSamples (packLabeledSamples samples) = samples :=
  unpackLabeledSamples_packLabeledSamples_internal samples

/-- Packing after unpacking recovers every fixed-width input string. -/
@[simp] theorem packLabeledSamples_unpackLabeledSamples
    {count arity : ℕ}
    (input : BitString (count * (arity + 1))) :
    packLabeledSamples (unpackLabeledSamples input) = input :=
  packLabeledSamples_unpackLabeledSamples_internal input

/-- A target-labeled packed row preserves every input coordinate. -/
@[simp] theorem packTargetSamples_input {count arity : ℕ}
    (target : BitString arity → Bool)
    (inputs : Fin count → BitString arity)
    (sample : Fin count) (coordinate : Fin arity) :
    packTargetSamples target inputs
        (finProdFinEquiv (sample, coordinate.castSucc)) =
      inputs sample coordinate :=
  packTargetSamples_input_internal target inputs sample coordinate

/-- A target-labeled packed row stores the target's value as its final bit. -/
@[simp] theorem packTargetSamples_output {count arity : ℕ}
    (target : BitString arity → Bool)
    (inputs : Fin count → BitString arity)
    (sample : Fin count) :
    packTargetSamples target inputs
        (finProdFinEquiv (sample, Fin.last arity)) =
      target (inputs sample) :=
  packTargetSamples_output_internal target inputs sample

/-- A `width`-bit counter output always denotes a number below `2^width`. -/
theorem counterValue_lt_two_pow {width : ℕ}
    (output : BitString width) :
    counterValue output < 2 ^ width :=
  counterValue_lt_two_pow_internal output

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
