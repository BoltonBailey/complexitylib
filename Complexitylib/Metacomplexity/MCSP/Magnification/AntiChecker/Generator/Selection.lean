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

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
