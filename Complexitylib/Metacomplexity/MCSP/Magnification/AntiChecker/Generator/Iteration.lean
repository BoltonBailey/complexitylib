/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Iteration.Defs
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Iteration.Internal

/-!
# Finite iteration of anti-checker selection rounds

This module exposes exact base and successor equations for the dependent
composition of prefix-length counter-selection circuits.
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- Zero selection rounds preserve the truth table and attach the empty
labeled prefix. -/
@[simp] theorem eval_selectionPrefixCircuit_zero
    {overhead arity : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (hrounds : 0 ≤ requiredRoundCount beta arity)
    (table : BitString (2 ^ arity)) :
    (selectionPrefixCircuit family 0 hrounds).2.eval table =
      selectionRoundInput table (emptyLabeledPrefix arity) :=
  eval_selectionPrefixCircuit_zero_internal family hrounds table

/-- The initial state-copy circuit has exactly one output gate per truth-table
bit. -/
@[simp] theorem size_selectionPrefixCircuit_zero
    {overhead arity : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (hrounds : 0 ≤ requiredRoundCount beta arity) :
    (selectionPrefixCircuit family 0 hrounds).2.size = 2 ^ arity :=
  size_selectionPrefixCircuit_zero_internal family hrounds

/-- A nonempty prefix circuit evaluates the previous prefix circuit and then
the counter-selection round indexed by that prefix length. -/
@[simp] theorem eval_selectionPrefixCircuit_succ
    {overhead arity rounds : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (hrounds : rounds + 1 ≤ requiredRoundCount beta arity)
    (table : BitString (2 ^ arity)) :
    (selectionPrefixCircuit family (rounds + 1) hrounds).2.eval table =
      (selectionRoundStateCircuit
        (family.counter (selectionPrefixCounterIndex hrounds))).2.eval
          ((selectionPrefixCircuit family rounds
            (selectionPrefixPriorBound hrounds)).2.eval table) :=
  eval_selectionPrefixCircuit_succ_internal family hrounds table

/-- Serial composition gives exact additive size at every successor round. -/
@[simp] theorem size_selectionPrefixCircuit_succ
    {overhead arity rounds : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (hrounds : rounds + 1 ≤ requiredRoundCount beta arity) :
    (selectionPrefixCircuit family (rounds + 1) hrounds).2.size =
      (selectionPrefixCircuit family rounds
          (selectionPrefixPriorBound hrounds)).2.size +
        (selectionRoundStateCircuit
          (family.counter (selectionPrefixCounterIndex hrounds))).2.size :=
  size_selectionPrefixCircuit_succ_internal family hrounds

/-- Prepending a candidate to a target-labeled packed vector agrees exactly
with the candidate-prefix encoding used by the counter circuit. -/
theorem candidateLabeledSamples_truthTable_packTargetSamples
    {arity prefixLength : ℕ} (target : BitString arity → Bool)
    (inputs : Fin prefixLength → BitString arity)
    (input : BitString arity) :
    candidateLabeledSamples (MCSP.Instance.inputIndex input)
        (truthTable target) (packTargetSamples target inputs) =
      fun sample =>
        SuccinctMCSP.Sample.ofFunction target
          ((Fin.cons input inputs :
            Fin (prefixLength + 1) → BitString arity) sample) :=
  candidateLabeledSamples_truthTable_packTargetSamples_internal
    target inputs input

/-- On a canonical target truth table, the round successor state is precisely
the state obtained by consing the selected input. -/
theorem selectionRoundSuccessorInput_truthTable_packTargetSamples
    {arity prefixLength : ℕ} (target : BitString arity → Bool)
    (inputs : Fin prefixLength → BitString arity)
    (candidate : Fin (2 ^ arity)) :
    selectionRoundSuccessorInput candidate (truthTable target)
        (packTargetSamples target inputs) =
      selectionTraceState target
        (Fin.cons (MCSP.Instance.inputOfIndex candidate) inputs) :=
  selectionRoundSuccessorInput_truthTable_packTargetSamples_internal
    target inputs candidate

/-- The circuit-level counter estimate on a canonical state is the counter's
semantic estimate of the target-labeled cons extension. -/
theorem counterRoundEstimate_truthTable_packTargetSamples
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength)
    (target : BitString arity → Bool)
    (inputs : Fin prefixLength → BitString arity)
    (input : BitString arity) :
    counterRoundEstimate counter (truthTable target)
        (packTargetSamples target inputs) input =
      counter.estimate (packTargetSamples target (Fin.cons input inputs)) :=
  counterRoundEstimate_truthTable_packTargetSamples_internal
    counter target inputs input

/-- At every bounded prefix, the circuit-level round estimate is exactly the
existing total estimator induced by the counter family. -/
theorem counterRoundEstimate_eq_extensionEstimator
    {overhead arity rounds : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (target : BitString arity → Bool)
    (inputs : Fin rounds → BitString arity)
    (hrounds : rounds + 1 ≤ requiredRoundCount beta arity) :
    counterRoundEstimate
        (family.counter (selectionPrefixCounterIndex hrounds))
        (truthTable target) (packTargetSamples target inputs) =
      family.extensionEstimator target (List.ofFn inputs) :=
  counterRoundEstimate_eq_extensionEstimator_internal
    family target inputs hrounds

/-- Every bounded prefix circuit realizes a sequence of genuine greedy
estimate-minimizing choices for the counter family's induced estimator. -/
theorem exists_eval_selectionPrefixCircuit_isEstimateSelectionTrace
    {overhead arity rounds : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (target : BitString arity → Bool)
    (hrounds : rounds ≤ requiredRoundCount beta arity) :
    ∃ inputs : Fin rounds → BitString arity,
      (selectionPrefixCircuit family rounds hrounds).2.eval
          (truthTable target) = selectionTraceState target inputs ∧
        AntiChecker.IsEstimateSelectionTrace
          (family.extensionEstimator target) (List.ofFn inputs) :=
  exists_eval_selectionPrefixCircuit_isEstimateSelectionTrace_internal
    family target hrounds

/-- The full state circuit realizes an estimate-selection trace of the exact
length required by the anti-checker argument. -/
theorem exists_eval_fullSelectionStateCircuit_isEstimateSelectionTrace
    {overhead arity : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (target : BitString arity → Bool) :
    ∃ inputs : Fin (requiredRoundCount beta arity) → BitString arity,
      (fullSelectionStateCircuit family).2.eval (truthTable target) =
          selectionTraceState target inputs ∧
        AntiChecker.IsEstimateSelectionTrace
          (family.extensionEstimator target) (List.ofFn inputs) :=
  exists_eval_fullSelectionStateCircuit_isEstimateSelectionTrace_internal
    family target

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
