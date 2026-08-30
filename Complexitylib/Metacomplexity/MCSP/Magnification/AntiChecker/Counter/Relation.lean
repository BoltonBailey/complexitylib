/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Relation.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Relation.Internal

/-!
# Anti-checker counter relation

This module exposes the exact finite relation estimated by the conditional
approximate counter circuits in the Anti-Checker Lemma construction.
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- Explicit target labels recover the existing target-relative consistency
predicate on the corresponding input list. -/
theorem codeMatchesTargetSamples_iff {count arity : ℕ}
    (target : BitString arity → Bool)
    (inputs : Fin count → BitString arity) (code : List Bool) :
    CodeMatchesLabeledSamples
        (fun sample =>
          SuccinctMCSP.Sample.ofFunction target (inputs sample)) code ↔
      AntiChecker.ConsistentCode target (List.ofFn inputs) code :=
  codeMatchesTargetSamples_iff_internal target inputs code

/-- Counting target-labeled vectors agrees exactly with the canonical survivor
count on the corresponding input list. -/
theorem candidateLabeledSurvivorCount_targetSamples
    {count arity threshold : ℕ} (target : BitString arity → Bool)
    (inputs : Fin count → BitString arity) :
    candidateLabeledSurvivorCount arity threshold
        (fun sample =>
          SuccinctMCSP.Sample.ofFunction target (inputs sample)) =
      AntiChecker.candidateSurvivorCount target threshold
        (List.ofFn inputs) :=
  candidateLabeledSurvivorCount_targetSamples_internal target inputs

/-- The fixed-width sample codec preserves the survivor count exactly. -/
theorem candidateLabeledSurvivorCount_unpack_pack
    {count arity threshold : ℕ}
    (samples : Fin count → SuccinctMCSP.Sample arity) :
    candidateLabeledSurvivorCount arity threshold
        (unpackLabeledSamples (packLabeledSamples samples)) =
      candidateLabeledSurvivorCount arity threshold samples :=
  candidateLabeledSurvivorCount_unpack_pack_internal samples

/-- Decoding a packed target-labeled vector recovers the existing canonical
survivor count on its input list. -/
@[simp] theorem candidateLabeledSurvivorCount_unpack_packTargetSamples
    {count arity threshold : ℕ} (target : BitString arity → Bool)
    (inputs : Fin count → BitString arity) :
    candidateLabeledSurvivorCount arity threshold
        (unpackLabeledSamples (packTargetSamples target inputs)) =
      AntiChecker.candidateSurvivorCount target threshold
        (List.ofFn inputs) :=
  candidateLabeledSurvivorCount_unpack_packTargetSamples_internal
    target inputs

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
