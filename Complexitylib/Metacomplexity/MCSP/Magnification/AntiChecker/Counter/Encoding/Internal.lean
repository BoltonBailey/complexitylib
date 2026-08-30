/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Encoding.Defs

/-!
# Anti-checker counter encodings -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

theorem packLabeledSamples_input_internal {count arity : ℕ}
    (samples : Fin count → SuccinctMCSP.Sample arity)
    (sample : Fin count) (coordinate : Fin arity) :
    packLabeledSamples samples
        (finProdFinEquiv (sample, coordinate.castSucc)) =
      (samples sample).input coordinate := by
  simp [packLabeledSamples]

theorem packLabeledSamples_output_internal {count arity : ℕ}
    (samples : Fin count → SuccinctMCSP.Sample arity)
    (sample : Fin count) :
    packLabeledSamples samples
        (finProdFinEquiv (sample, Fin.last arity)) =
      (samples sample).output := by
  simp [packLabeledSamples]

theorem unpackLabeledSample_packLabeledSamples_internal
    {count arity : ℕ}
    (samples : Fin count → SuccinctMCSP.Sample arity)
    (sample : Fin count) :
    unpackLabeledSample (packLabeledSamples samples) sample =
      samples sample := by
  cases hsample : samples sample with
  | mk sampleInput sampleOutput =>
      change
        SuccinctMCSP.Sample.mk
          (fun coordinate : Fin arity =>
            packLabeledSamples samples
              (finProdFinEquiv (sample, coordinate.castSucc)))
          (packLabeledSamples samples
            (finProdFinEquiv (sample, Fin.last arity))) =
          SuccinctMCSP.Sample.mk sampleInput sampleOutput
      congr
      · funext coordinate
        simpa only [hsample] using
          packLabeledSamples_input_internal samples sample coordinate
      · simpa only [hsample] using
          packLabeledSamples_output_internal samples sample

theorem unpackLabeledSamples_packLabeledSamples_internal
    {count arity : ℕ}
    (samples : Fin count → SuccinctMCSP.Sample arity) :
    unpackLabeledSamples (packLabeledSamples samples) = samples := by
  funext sample
  exact unpackLabeledSample_packLabeledSamples_internal samples sample

theorem packLabeledSamples_unpackLabeledSamples_internal
    {count arity : ℕ}
    (input : BitString (count * (arity + 1))) :
    packLabeledSamples (unpackLabeledSamples input) = input := by
  funext coordinate
  simp only [packLabeledSamples, unpackLabeledSamples,
    unpackLabeledSample]
  generalize hposition : finProdFinEquiv.symm coordinate = position
  have hcoordinate := congrArg finProdFinEquiv hposition
  simp only [Equiv.apply_symm_apply] at hcoordinate
  subst coordinate
  rcases position with ⟨sample, sampleCoordinate⟩
  refine Fin.lastCases ?_ (fun _ => ?_) sampleCoordinate
  · simp only [Fin.lastCases_last]
  · simp only [Fin.lastCases_castSucc]

theorem packTargetSamples_input_internal {count arity : ℕ}
    (target : BitString arity → Bool)
    (inputs : Fin count → BitString arity)
    (sample : Fin count) (coordinate : Fin arity) :
    packTargetSamples target inputs
        (finProdFinEquiv (sample, coordinate.castSucc)) =
      inputs sample coordinate := by
  exact packLabeledSamples_input_internal _ sample coordinate

theorem packTargetSamples_output_internal {count arity : ℕ}
    (target : BitString arity → Bool)
    (inputs : Fin count → BitString arity)
    (sample : Fin count) :
    packTargetSamples target inputs
        (finProdFinEquiv (sample, Fin.last arity)) =
      target (inputs sample) := by
  exact packLabeledSamples_output_internal _ sample

theorem counterValue_lt_two_pow_internal {width : ℕ}
    (output : BitString width) :
    counterValue output < 2 ^ width :=
  (MCSP.Instance.inputIndex output).isLt

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
