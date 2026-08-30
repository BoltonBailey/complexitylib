/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Selection.Defs
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Selection.Internal

/-!
# Circuit-level anti-checker selection rounds

This module exposes the exact semantics and size of the fixed-candidate record
circuit used by exhaustive approximate-counter minimization.
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- A fixed-candidate counter input is exactly the row-major encoding of that
candidate prepended to the carried labeled prefix. -/
@[simp] theorem eval_candidateCounterInputCircuit
    {arity prefixLength : ℕ} (candidate : Fin (2 ^ arity))
    (table : BitString (2 ^ arity))
    (packedPrefix : BitString (prefixLength * (arity + 1))) :
    (candidateCounterInputCircuit arity prefixLength candidate).eval
        (selectionRoundInput table packedPrefix) =
      packLabeledSamples
        (candidateLabeledSamples candidate table packedPrefix) :=
  eval_candidateCounterInputCircuit_internal candidate table packedPrefix

/-- A fixed-candidate payload contains its input bits followed by the live
truth-table label. -/
@[simp] theorem eval_candidateSampleCircuit
    {arity prefixLength : ℕ} (candidate : Fin (2 ^ arity))
    (table : BitString (2 ^ arity))
    (packedPrefix : BitString (prefixLength * (arity + 1))) :
    (candidateSampleCircuit arity prefixLength candidate).eval
        (selectionRoundInput table packedPrefix) =
      candidateSampleBits candidate table :=
  eval_candidateSampleCircuit_internal candidate table packedPrefix

/-- A fixed-candidate record emits the counter bits as its key and the labeled
candidate as its payload. -/
@[simp] theorem eval_candidateCounterRecordCircuit
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength)
    (candidate : Fin (2 ^ arity)) (table : BitString (2 ^ arity))
    (packedPrefix : BitString (prefixLength * (arity + 1))) :
    (candidateCounterRecordCircuit counter candidate).2.eval
        (selectionRoundInput table packedPrefix) =
      Fin.append
        (counter.circuit.eval
          (packLabeledSamples
            (candidateLabeledSamples candidate table packedPrefix)))
        (candidateSampleBits candidate table) :=
  eval_candidateCounterRecordCircuit_internal
    counter candidate table packedPrefix

/-- Exact cost of one fixed-candidate record: the supplied counter plus the
materialized counter input and labeled payload. -/
@[simp] theorem size_candidateCounterRecordCircuit
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength)
    (candidate : Fin (2 ^ arity)) :
    (candidateCounterRecordCircuit counter candidate).2.size =
      counter.circuit.size +
        (prefixLength + 1) * (arity + 1) + (arity + 1) :=
  size_candidateCounterRecordCircuit_internal counter candidate

/-- The recursive tournament contains exactly one record for every truth-table
input. -/
@[simp] theorem selectionCandidateCount_add_one (arity : ℕ) :
    selectionCandidateCount arity + 1 = 2 ^ arity :=
  selectionCandidateCount_add_one_internal arity

/-- Parallel candidate evaluation produces the exact recursive record layout
expected by the minimum tournament. -/
@[simp] theorem eval_packedCandidateCounterRecords
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength)
    (table : BitString (2 ^ arity))
    (packedPrefix : BitString (prefixLength * (arity + 1))) :
    (packedCandidateCounterRecords counter).2.eval
        (selectionRoundInput table packedPrefix) =
      BitString.packKeyedRecords (selectionCandidateCount arity)
        (candidateCounterKeys counter table packedPrefix)
        (candidateCounterPayloads table) :=
  eval_packedCandidateCounterRecords_internal counter table packedPrefix

/-- Exact parallel-evaluation cost: one fixed-candidate record circuit for
each truth-table input. -/
@[simp] theorem size_packedCandidateCounterRecords
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength) :
    (packedCandidateCounterRecords counter).2.size =
      (selectionCandidateCount arity + 1) *
        (counter.circuit.size +
          (prefixLength + 1) * (arity + 1) + (arity + 1)) :=
  size_packedCandidateCounterRecords_internal counter

/-- Exhaustive selection evaluates to the semantic minimum counter record. -/
@[simp] theorem eval_minimumCounterRecordCircuit
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength)
    (table : BitString (2 ^ arity))
    (packedPrefix : BitString (prefixLength * (arity + 1))) :
    (minimumCounterRecordCircuit counter).2.eval
        (selectionRoundInput table packedPrefix) =
      Fin.append (minimumCounterRecord counter table packedPrefix).1
        (minimumCounterRecord counter table packedPrefix).2 :=
  eval_minimumCounterRecordCircuit_internal counter table packedPrefix

/-- Exact exhaustive-selector cost, separating parallel candidate evaluation
from the sequential keyed-minimum tournament. -/
@[simp] theorem size_minimumCounterRecordCircuit
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength) :
    (minimumCounterRecordCircuit counter).2.size =
      (selectionCandidateCount arity + 1) *
          (counter.circuit.size +
            (prefixLength + 1) * (arity + 1) + (arity + 1)) +
        ((selectionCandidateCount arity + 1) *
            (counterOutputWidth beta arity + (arity + 1)) +
          selectionCandidateCount arity *
            (20 * counterOutputWidth beta arity +
              5 * (arity + 1) + 1)) :=
  size_minimumCounterRecordCircuit_internal counter

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
