/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Iteration.Defs
import Complexitylib.Circuits.Composition
import Complexitylib.Circuits.InputProjection
import Complexitylib.Metacomplexity.MCSP
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Encoding
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Estimator
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Internal

/-!
# Finite iteration of anti-checker selection rounds -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

theorem eval_selectionPrefixCircuit_zero_internal
    {overhead arity : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (hrounds : 0 ≤ requiredRoundCount beta arity)
    (table : BitString (2 ^ arity)) :
    (selectionPrefixCircuit family 0 hrounds).2.eval table =
      selectionRoundInput table (emptyLabeledPrefix arity) := by
  simp only [selectionPrefixCircuit]
  rw [Circuit.eval_projectInputs]
  funext coordinate
  change table (selectionEmptyStateInputMap arity coordinate) =
    Fin.append table (emptyLabeledPrefix arity) coordinate
  have hcoordinate : coordinate =
      Fin.castAdd (0 * (arity + 1))
        (selectionEmptyStateInputMap arity coordinate) := by
    apply Fin.ext
    rfl
  rw [hcoordinate, Fin.append_left]
  apply congrArg table
  apply Fin.ext
  rfl

theorem size_selectionPrefixCircuit_zero_internal
    {overhead arity : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (hrounds : 0 ≤ requiredRoundCount beta arity) :
    (selectionPrefixCircuit family 0 hrounds).2.size = 2 ^ arity := by
  simp only [selectionPrefixCircuit]
  rw [Circuit.size_projectInputs]
  simp [selectionRoundInputWidth]

theorem eval_selectionPrefixCircuit_succ_internal
    {overhead arity rounds : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (hrounds : rounds + 1 ≤ requiredRoundCount beta arity)
    (table : BitString (2 ^ arity)) :
    (selectionPrefixCircuit family (rounds + 1) hrounds).2.eval table =
      (selectionRoundStateCircuit
        (family.counter (selectionPrefixCounterIndex hrounds))).2.eval
          ((selectionPrefixCircuit family rounds
            (selectionPrefixPriorBound hrounds)).2.eval table) := by
  simp only [selectionPrefixCircuit]
  exact Circuit.eval_compose
    (selectionRoundStateCircuit
      (family.counter (selectionPrefixCounterIndex hrounds))).2
    (selectionPrefixCircuit family rounds
      (selectionPrefixPriorBound hrounds)).2 table

theorem size_selectionPrefixCircuit_succ_internal
    {overhead arity rounds : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (hrounds : rounds + 1 ≤ requiredRoundCount beta arity) :
    (selectionPrefixCircuit family (rounds + 1) hrounds).2.size =
      (selectionPrefixCircuit family rounds
          (selectionPrefixPriorBound hrounds)).2.size +
        (selectionRoundStateCircuit
          (family.counter (selectionPrefixCounterIndex hrounds))).2.size := by
  simp only [selectionPrefixCircuit]
  exact Circuit.size_compose
    (selectionRoundStateCircuit
      (family.counter (selectionPrefixCounterIndex hrounds))).2
    (selectionPrefixCircuit family rounds
      (selectionPrefixPriorBound hrounds)).2

theorem candidateLabeledSamples_truthTable_packTargetSamples_internal
    {arity prefixLength : ℕ} (target : BitString arity → Bool)
    (inputs : Fin prefixLength → BitString arity)
    (input : BitString arity) :
    candidateLabeledSamples (MCSP.Instance.inputIndex input)
        (truthTable target) (packTargetSamples target inputs) =
      fun sample =>
        SuccinctMCSP.Sample.ofFunction target
          ((Fin.cons input inputs :
            Fin (prefixLength + 1) → BitString arity) sample) := by
  funext sample
  refine Fin.cases ?_ (fun previous => ?_) sample
  · simp [candidateLabeledSamples, candidateSample,
      SuccinctMCSP.Sample.ofFunction, truthTable_inputIndex_internal]
  · simp [candidateLabeledSamples, packTargetSamples]

theorem selectionRoundSuccessorInput_truthTable_packTargetSamples_internal
    {arity prefixLength : ℕ} (target : BitString arity → Bool)
    (inputs : Fin prefixLength → BitString arity)
    (candidate : Fin (2 ^ arity)) :
    selectionRoundSuccessorInput candidate (truthTable target)
        (packTargetSamples target inputs) =
      selectionTraceState target
        (Fin.cons (MCSP.Instance.inputOfIndex candidate) inputs) := by
  unfold selectionRoundSuccessorInput selectionTraceState
  apply congrArg (selectionRoundInput (truthTable target))
  unfold packTargetSamples
  apply congrArg packLabeledSamples
  have hsamples :=
    candidateLabeledSamples_truthTable_packTargetSamples_internal
      target inputs (MCSP.Instance.inputOfIndex candidate)
  simpa [packTargetSamples] using hsamples

theorem counterRoundEstimate_truthTable_packTargetSamples_internal
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength)
    (target : BitString arity → Bool)
    (inputs : Fin prefixLength → BitString arity)
    (input : BitString arity) :
    counterRoundEstimate counter (truthTable target)
        (packTargetSamples target inputs) input =
      counter.estimate (packTargetSamples target (Fin.cons input inputs)) := by
  unfold counterRoundEstimate
  apply congrArg counter.estimate
  unfold packTargetSamples
  apply congrArg packLabeledSamples
  simpa [packTargetSamples] using
    candidateLabeledSamples_truthTable_packTargetSamples_internal
      target inputs input

private theorem finCons_heq_get_cons_ofFn
    {count : ℕ} {alpha : Type} (head : alpha)
    (tail : Fin count → alpha) :
    (Fin.cons head tail : Fin (count + 1) → alpha) ≍
      (head :: List.ofFn tail).get := by
  apply (Fin.heq_fun_iff (by simp)).2
  intro index
  refine Fin.cases ?_ (fun previous => ?_) index
  · simp
  · simp

theorem counterRoundEstimate_eq_extensionEstimator_internal
    {overhead arity rounds : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (target : BitString arity → Bool)
    (inputs : Fin rounds → BitString arity)
    (hrounds : rounds + 1 ≤ requiredRoundCount beta arity) :
    counterRoundEstimate
        (family.counter (selectionPrefixCounterIndex hrounds))
        (truthTable target) (packTargetSamples target inputs) =
      family.extensionEstimator target (List.ofFn inputs) := by
  funext input
  rw [counterRoundEstimate_truthTable_packTargetSamples_internal]
  unfold ApproximateCounterFamily.extensionEstimator
  split_ifs with hlength
  · let ExtensionData :=
      Σ index : Fin (requiredRoundCount beta arity),
        Fin (index.val + 1) → BitString arity
    let left : ExtensionData :=
      ⟨selectionPrefixCounterIndex hrounds, Fin.cons input inputs⟩
    let right : ExtensionData :=
      ⟨⟨(List.ofFn inputs).length, hlength⟩,
        (input :: List.ofFn inputs).get⟩
    let evaluate : ExtensionData → ℕ := fun data =>
      (family.counter data.1).estimate
        (packTargetSamples target data.2)
    change evaluate left = evaluate right
    apply congrArg evaluate
    have hindex : left.1 = right.1 := by
      apply Fin.ext
      simp [left, right, selectionPrefixCounterIndex]
    exact Sigma.ext hindex (finCons_heq_get_cons_ofFn input inputs)
  · exfalso
    apply hlength
    simp
    omega

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
