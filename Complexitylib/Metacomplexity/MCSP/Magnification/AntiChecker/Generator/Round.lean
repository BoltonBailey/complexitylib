/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Round.Defs
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Round.Internal

/-!
# Iterable anti-checker selection rounds

This module exposes one state-preserving circuit round suitable for sequential
composition across the finite approximate-counter family.
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- A round's combined circuit preserves the complete state before appending
the exhaustive minimum record. -/
@[simp] theorem eval_selectionRoundCombinedCircuit
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength)
    (table : BitString (2 ^ arity))
    (packedPrefix : BitString (prefixLength * (arity + 1))) :
    (selectionRoundCombinedCircuit counter).2.eval
        (selectionRoundInput table packedPrefix) =
      Fin.append (selectionRoundInput table packedPrefix)
        ((minimumCounterRecordCircuit counter).2.eval
          (selectionRoundInput table packedPrefix)) :=
  eval_selectionRoundCombinedCircuit_internal counter table packedPrefix

/-- Exact cost of preserving the state beside exhaustive minimization. -/
@[simp] theorem size_selectionRoundCombinedCircuit
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength) :
    (selectionRoundCombinedCircuit counter).2.size =
      selectionRoundInputWidth arity prefixLength +
        (minimumCounterRecordCircuit counter).2.size :=
  size_selectionRoundCombinedCircuit_internal counter

/-- One round preserves the table, prepends a genuine labeled candidate, and
that candidate globally minimizes the counter estimate. -/
theorem exists_eval_selectionRoundStateCircuit_eq_successor
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength)
    (table : BitString (2 ^ arity))
    (packedPrefix : BitString (prefixLength * (arity + 1))) :
    ∃ candidate : Fin (2 ^ arity),
      (selectionRoundStateCircuit counter).2.eval
          (selectionRoundInput table packedPrefix) =
          selectionRoundSuccessorInput candidate table packedPrefix ∧
        AntiChecker.IsEstimateMinimizer
          (counterRoundEstimate counter table packedPrefix)
          (MCSP.Instance.inputOfIndex candidate) :=
  exists_eval_selectionRoundStateCircuit_eq_successor_internal
    counter table packedPrefix

/-- Exact round-state cost: preserved input state, exhaustive minimization,
and the projected successor state. -/
@[simp] theorem size_selectionRoundStateCircuit
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength) :
    (selectionRoundStateCircuit counter).2.size =
      selectionRoundInputWidth arity prefixLength +
        (minimumCounterRecordCircuit counter).2.size +
          selectionRoundInputWidth arity (prefixLength + 1) :=
  size_selectionRoundStateCircuit_internal counter

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
