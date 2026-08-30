/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Relation.Defs
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Encoding.Internal

/-!
# Anti-checker counter relation -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

theorem codeMatchesTargetSamples_iff_internal {count arity : ℕ}
    (target : BitString arity → Bool)
    (inputs : Fin count → BitString arity) (code : List Bool) :
    CodeMatchesLabeledSamples
        (fun sample =>
          SuccinctMCSP.Sample.ofFunction target (inputs sample)) code ↔
      AntiChecker.ConsistentCode target (List.ofFn inputs) code := by
  unfold CodeMatchesLabeledSamples CodeMatchesLabeledSample
  unfold AntiChecker.ConsistentCode AntiChecker.CodeAgreesAt
  rw [List.forall_iff_forall_mem, List.forall_mem_ofFn_iff]
  rfl

theorem candidateLabeledSurvivorCount_targetSamples_internal
    {count arity threshold : ℕ} (target : BitString arity → Bool)
    (inputs : Fin count → BitString arity) :
    candidateLabeledSurvivorCount arity threshold
        (fun sample =>
          SuccinctMCSP.Sample.ofFunction target (inputs sample)) =
      AntiChecker.candidateSurvivorCount target threshold
        (List.ofFn inputs) := by
  unfold candidateLabeledSurvivorCount candidateLabeledSurvivorCodes
  unfold AntiChecker.candidateSurvivorCount AntiChecker.survivorCount
  unfold AntiChecker.ConsistentCodes
  congr 1
  ext code
  simp only [Finset.mem_filter]
  rw [codeMatchesTargetSamples_iff_internal]

theorem candidateLabeledSurvivorCount_unpack_pack_internal
    {count arity threshold : ℕ}
    (samples : Fin count → SuccinctMCSP.Sample arity) :
    candidateLabeledSurvivorCount arity threshold
        (unpackLabeledSamples (packLabeledSamples samples)) =
      candidateLabeledSurvivorCount arity threshold samples := by
  rw [unpackLabeledSamples_packLabeledSamples_internal]

theorem candidateLabeledSurvivorCount_unpack_packTargetSamples_internal
    {count arity threshold : ℕ} (target : BitString arity → Bool)
    (inputs : Fin count → BitString arity) :
    candidateLabeledSurvivorCount arity threshold
        (unpackLabeledSamples (packTargetSamples target inputs)) =
      AntiChecker.candidateSurvivorCount target threshold
        (List.ofFn inputs) := by
  unfold packTargetSamples
  rw [unpackLabeledSamples_packLabeledSamples_internal]
  exact candidateLabeledSurvivorCount_targetSamples_internal target inputs

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
