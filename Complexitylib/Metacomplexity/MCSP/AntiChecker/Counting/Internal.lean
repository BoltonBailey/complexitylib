/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Counting.Defs
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Enumeration.Internal
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Extraction.Internal
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Internal

/-!
# Anti-checker survivor counts -- proof internals
-/


public section

namespace Complexity

namespace AntiChecker

theorem survivorCount_nil_internal {arity : ℕ}
    (target : BitString arity → Bool) (codes : Finset (List Bool)) :
    survivorCount target [] codes = codes.card := by
  rw [survivorCount, consistentCodes_nil_internal]

theorem survivorCount_cons_internal {arity : ℕ}
    (target : BitString arity → Bool) (input : BitString arity)
    (inputs : List (BitString arity)) (codes : Finset (List Bool)) :
    survivorCount target (input :: inputs) codes =
      ((ConsistentCodes target inputs codes).filter
        (CodeAgreesAt target · input)).card := by
  rw [survivorCount, consistentCodes_cons_internal]

theorem survivorCount_le_card_internal {arity : ℕ}
    (target : BitString arity → Bool)
    (inputs : List (BitString arity)) (codes : Finset (List Bool)) :
    survivorCount target inputs codes ≤ codes.card := by
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem survivorCount_samples_anti_internal {arity : ℕ}
    {target : BitString arity → Bool}
    {first second : List (BitString arity)}
    {codes : Finset (List Bool)}
    (hsub : ∀ input ∈ first, input ∈ second) :
    survivorCount target second codes ≤
      survivorCount target first codes := by
  exact Finset.card_le_card
    (consistentCodes_samples_anti_internal hsub)

theorem survivorCount_eq_zero_iff_internal {arity : ℕ}
    (target : BitString arity → Bool)
    (inputs : List (BitString arity)) (codes : Finset (List Bool)) :
    survivorCount target inputs codes = 0 ↔
      ConsistentCodes target inputs codes = ∅ := by
  simp [survivorCount]

theorem candidateSurvivorCount_nil_internal {arity threshold : ℕ}
    (target : BitString arity → Bool) :
    candidateSurvivorCount target threshold [] =
      (candidateCodes arity threshold).card := by
  exact survivorCount_nil_internal target (candidateCodes arity threshold)

theorem candidateSurvivorCount_cons_internal {arity threshold : ℕ}
    (target : BitString arity → Bool) (input : BitString arity)
    (inputs : List (BitString arity)) :
    candidateSurvivorCount target threshold (input :: inputs) =
      ((ConsistentCodes target inputs (candidateCodes arity threshold)).filter
        (CodeAgreesAt target · input)).card := by
  exact survivorCount_cons_internal target input inputs
    (candidateCodes arity threshold)

theorem candidateSurvivorCount_le_card_internal {arity threshold : ℕ}
    (target : BitString arity → Bool)
    (inputs : List (BitString arity)) :
    candidateSurvivorCount target threshold inputs ≤
      (candidateCodes arity threshold).card := by
  exact survivorCount_le_card_internal target inputs
    (candidateCodes arity threshold)

theorem candidateSurvivorCount_samples_anti_internal
    {arity threshold : ℕ} {target : BitString arity → Bool}
    {first second : List (BitString arity)}
    (hsub : ∀ input ∈ first, input ∈ second) :
    candidateSurvivorCount target threshold second ≤
      candidateSurvivorCount target threshold first := by
  exact survivorCount_samples_anti_internal hsub

private theorem consistentCodes_candidateCodes_eq_empty_of_isFor
    {arity threshold : ℕ} [NeZero arity]
    (target : BitString arity → Bool) (inputs : List (BitString arity))
    (hanti : IsFor target threshold inputs) :
    ConsistentCodes target inputs (candidateCodes arity threshold) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro code hcode
  rw [mem_consistentCodes_iff_internal] at hcode
  have hsmall := (mem_candidateCodes_iff_internal.mp hcode.1).2
  unfold IsSmallCircuitCode at hsmall
  cases hdecode : CircuitCode.RawCircuit.decode? code with
  | none => simp [hdecode] at hsmall
  | some circuit =>
      simp only [hdecode] at hsmall
      obtain ⟨hwell, hsize⟩ := hsmall
      have hcircuitSize :
          (circuit.toCircuit arity hwell).size ≤ threshold := by
        rw [CircuitCode.RawCircuit.size_toCircuit]
        exact hsize
      obtain ⟨input, hinput, hdiff⟩ :=
        hanti (circuit.length - 1)
          (circuit.toCircuit arity hwell) hcircuitSize
      have hagrees :=
        (consistentCode_iff_forall_mem_internal
          target inputs code).mp hcode.2 input hinput
      unfold CodeAgreesAt at hagrees
      simp [CircuitCode.evalCode, BitString.length_toList,
        hdecode] at hagrees
      have heval := CircuitCode.RawCircuit.eval?_toCircuit
        arity circuit hwell input
      rw [heval] at hagrees
      exact hdiff (Option.some.inj hagrees)

theorem candidateSurvivorCount_eq_zero_iff_isFor_internal
    {arity threshold : ℕ} [NeZero arity]
    (target : BitString arity → Bool) (inputs : List (BitString arity)) :
    candidateSurvivorCount target threshold inputs = 0 ↔
      IsFor target threshold inputs := by
  rw [candidateSurvivorCount, survivorCount_eq_zero_iff_internal]
  constructor
  · intro hempty
    exact isFor_of_consistentCodes_eq_empty_internal
      target inputs (candidateCodes arity threshold)
        (candidateCodes_coversThreshold_internal arity threshold) hempty
  · exact consistentCodes_candidateCodes_eq_empty_of_isFor
      target inputs

end AntiChecker

end Complexity
