/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeCleanup.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BlankWorkPrefixMany
import Complexitylib.Models.TuringMachine.Subroutines.RewindInputSpace

/-!
# Restartable output-probe cleanup -- proof internals
-/

namespace Complexity

namespace TM

theorem outputProbeCleanupSourceIdx_injective_internal {n : ℕ} :
    Function.Injective (@outputProbeCleanupSourceIdx n) := by
  intro left right heq
  apply Fin.ext
  exact Fin.mk.inj heq

theorem outputProbeCleanupTargets_nodup_internal (n : ℕ) :
    (outputProbeCleanupTargets n).Nodup := by
  rw [outputProbeCleanupTargets, List.nodup_append]
  refine ⟨List.nodup_ofFn_ofInjective
    outputProbeCleanupSourceIdx_injective_internal, by simp, ?_⟩
  intro idx hsource capture hcapture heq
  obtain ⟨source, rfl⟩ := List.mem_ofFn.mp hsource
  simp only [List.mem_singleton] at hcapture
  have hbad := heq.trans hcapture
  apply congrArg Fin.val at hbad
  simp [outputProbeCleanupSourceIdx, outputProbeCleanupCaptureIdx] at hbad
  omega

theorem outputProbeCleanupSourceIdx_mem_internal {n : ℕ} (idx : Fin n) :
    outputProbeCleanupSourceIdx idx ∈ outputProbeCleanupTargets n := by
  simp [outputProbeCleanupTargets, List.mem_ofFn]

theorem outputProbeCleanupCaptureIdx_mem_internal (n : ℕ) :
    outputProbeCleanupCaptureIdx n ∈ outputProbeCleanupTargets n := by
  simp [outputProbeCleanupTargets]

theorem outputProbeCleanupTarget_lt_counter_internal {n : ℕ}
    {idx : Fin (n + 4)} (hidx : idx ∈ outputProbeCleanupTargets n) :
    idx.val < (outputProbeCleanupCounterIdx n).val := by
  rw [outputProbeCleanupTargets, List.mem_append] at hidx
  rcases hidx with hsource | hcapture
  · obtain ⟨source, rfl⟩ := List.mem_ofFn.mp hsource
    simp only [outputProbeCleanupSourceIdx, outputProbeCleanupCounterIdx,
      Fin.val_mk]
    omega
  · simp only [List.mem_singleton] at hcapture
    subst idx
    simp [outputProbeCleanupCaptureIdx, outputProbeCleanupCounterIdx]

theorem outputProbeCleanupTarget_distinct_internal {n : ℕ}
    {idx : Fin (n + 4)} (hidx : idx ∈ outputProbeCleanupTargets n) :
    BlankWorkPrefixDistinct idx (outputProbeCleanupCounterIdx n)
      (outputProbeCleanupLimitIdx n) := by
  have hlt := outputProbeCleanupTarget_lt_counter_internal hidx
  constructor
  · exact Fin.ne_of_lt hlt
  constructor
  · apply Fin.ne_of_lt
    exact lt_trans hlt (by
      simp [outputProbeCleanupCounterIdx, outputProbeCleanupLimitIdx])
  · apply Fin.ne_of_lt
    simp [outputProbeCleanupCounterIdx, outputProbeCleanupLimitIdx]

private theorem outputProbeRewoundInput_parked (tape : Tape)
    (hinvariant : tape.StartInvariant) :
    Parked (outputProbeRewoundInput tape) := by
  constructor
  · simp [outputProbeRewoundInput]
  · intro index hindex
    exact hinvariant.2 index hindex

theorem outputProbeCleanupTM_hoareTimeSpace_frame_internal
    (n inputHeadBound limit inputLength initialSpace : ℕ)
    (headBound : Fin (n + 4) → ℕ)
    (inp₀ : Tape) (work₀ : Fin (n + 4) → Tape) (out₀ : Tape)
    (hinputInvariant : inp₀.StartInvariant) (hinput : Parked inp₀)
    (hinputHead : inp₀.head ≤ inputHeadBound)
    (hwork : ∀ i, Parked (work₀ i))
    (htargetInvariant : ∀ i, i ∈ outputProbeCleanupTargets n →
      (work₀ i).StartInvariant)
    (htargetHead : ∀ i, i ∈ outputProbeCleanupTargets n →
      (work₀ i).head ≤ headBound i)
    (hcounter : (work₀ (outputProbeCleanupCounterIdx n)).HasBinaryNat 0)
    (hlimit : (work₀ (outputProbeCleanupLimitIdx n)).HasBinaryNat limit)
    (houtput : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (outputProbeCleanupTM n).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = outputProbeRewoundInput inp₀ ∧
        work = rewindBlankWorkPrefixManyResult limit work₀
          (outputProbeCleanupTargets n) ∧
        out = out₀)
      (outputProbeCleanupTime n inputHeadBound limit headBound)
      inputLength (outputProbeCleanupSpace n initialSpace limit headBound) := by
  let inp₁ := outputProbeRewoundInput inp₀
  let cleanup := rewindBlankWorkPrefixManyTM
    (outputProbeCleanupCounterIdx n) (outputProbeCleanupLimitIdx n)
    (outputProbeCleanupTargets n)
  have hrewindBase := rewindInputTM_hoareTimeSpace_frame inputHeadBound
    inputLength initialSpace inp₀ work₀ out₀ hinputInvariant hinput
    hinputHead hwork houtput hworkSpace hinputSpace
  have hrewind : (rewindInputTM (n := n + 4)).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₁ ∧ work = work₀ ∧ out = out₀)
      (inputHeadBound + 2) inputLength initialSpace :=
    hrewindBase.consequence (fun _ _ _ h => h) (by
      rintro inp work out ⟨hhead, hcells, hworkEq, houtputEq⟩
      refine ⟨?_, hworkEq, houtputEq⟩
      apply Tape.ext
      · simpa [inp₁, outputProbeRewoundInput] using hhead
      · simpa [inp₁, outputProbeRewoundInput] using hcells) le_rfl le_rfl
      le_rfl
  have hinput₁ : Parked inp₁ := by
    exact outputProbeRewoundInput_parked inp₀ hinputInvariant
  have hcleanup := rewindBlankWorkPrefixManyTM_hoareTimeSpace_frame
    (outputProbeCleanupCounterIdx n) (outputProbeCleanupLimitIdx n)
    (outputProbeCleanupTargets n) headBound limit inputLength initialSpace
    inp₁ work₀ out₀ (outputProbeCleanupTargets_nodup_internal n)
    (fun _ hi => outputProbeCleanupTarget_distinct_internal hi)
    htargetInvariant htargetHead hinput₁ hwork hcounter hlimit houtput
    hworkSpace (by simp [inp₁, outputProbeRewoundInput])
  have hseq := seqTM_hoareTimeSpace (rewindInputTM (n := n + 4)) cleanup
    hrewind (by
      rintro inp work out ⟨rfl, rfl, rfl⟩
      exact ⟨hinput₁.transitionInput_eq_self,
        funext fun i => (hwork i).transitionTape_eq_self,
        houtput.transitionTape_eq_self⟩) hcleanup
  simpa [outputProbeCleanupTM, outputProbeCleanupTime,
    outputProbeCleanupSpace, cleanup, inp₁] using hseq

theorem outputProbeCleanupTM_isTransducer_internal (n : ℕ) :
    (outputProbeCleanupTM n).IsTransducer := by
  unfold outputProbeCleanupTM
  exact (rewindInputTM_isTransducer (n := n + 4)).seqTM
    (rewindBlankWorkPrefixManyTM_isTransducer
      (outputProbeCleanupCounterIdx n) (outputProbeCleanupLimitIdx n)
      (outputProbeCleanupTargets n))

end TM

end Complexity
