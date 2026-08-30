/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Extraction.Defs
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Internal

/-!
# Finite anti-checker extraction -- proof internals
-/


public section

namespace Complexity

namespace AntiChecker

theorem consistentCode_iff_forall_mem_internal {arity : ℕ}
    (target : BitString arity → Bool) (inputs : List (BitString arity))
    (code : List Bool) :
    ConsistentCode target inputs code ↔
      ∀ input ∈ inputs, CodeAgreesAt target code input := by
  rw [ConsistentCode, List.forall_iff_forall_mem]

theorem mem_consistentCodes_iff_internal {arity : ℕ}
    (target : BitString arity → Bool) (inputs : List (BitString arity))
    (codes : Finset (List Bool)) (code : List Bool) :
    code ∈ ConsistentCodes target inputs codes ↔
      code ∈ codes ∧ ConsistentCode target inputs code := by
  simp [ConsistentCodes]

theorem consistentCodes_nil_internal {arity : ℕ}
    (target : BitString arity → Bool) (codes : Finset (List Bool)) :
    ConsistentCodes target [] codes = codes := by
  ext code
  simp [ConsistentCodes, ConsistentCode]

theorem consistentCodes_cons_internal {arity : ℕ}
    (target : BitString arity → Bool) (input : BitString arity)
    (inputs : List (BitString arity)) (codes : Finset (List Bool)) :
    ConsistentCodes target (input :: inputs) codes =
      (ConsistentCodes target inputs codes).filter
        (CodeAgreesAt target · input) := by
  ext code
  simp [ConsistentCodes, ConsistentCode, and_left_comm, and_comm]

theorem consistentCodes_samples_anti_internal {arity : ℕ}
    {target : BitString arity → Bool}
    {first second : List (BitString arity)}
    {codes : Finset (List Bool)}
    (hsub : ∀ input ∈ first, input ∈ second) :
    ConsistentCodes target second codes ⊆
      ConsistentCodes target first codes := by
  intro code hcode
  rw [mem_consistentCodes_iff_internal] at hcode ⊢
  refine ⟨hcode.1, ?_⟩
  rw [consistentCode_iff_forall_mem_internal] at hcode ⊢
  intro input hinput
  exact hcode.2 input (hsub input hinput)

theorem exists_inputs_consistentCodes_eq_empty_internal {arity : ℕ}
    (target : BitString arity → Bool) (codes : Finset (List Bool))
    (hfail : AllFailSomewhere target codes) :
    ∃ inputs : List (BitString arity),
      inputs.length ≤ codes.card ∧
        ConsistentCodes target inputs codes = ∅ := by
  classical
  induction codes using Finset.induction with
  | empty =>
      exact ⟨[], by simp, consistentCodes_nil_internal target ∅⟩
  | @insert code codes hcode ih =>
      obtain ⟨input, hinput⟩ :=
        hfail code (Finset.mem_insert_self code codes)
      have hfailTail : AllFailSomewhere target codes := by
        intro candidate hcandidate
        exact hfail candidate (Finset.mem_insert_of_mem hcandidate)
      obtain ⟨inputs, hlength, hempty⟩ := ih hfailTail
      refine ⟨input :: inputs, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hcode]
        simp only [List.length_cons]
        omega
      · apply Finset.eq_empty_iff_forall_notMem.mpr
        intro candidate hcandidate
        rw [mem_consistentCodes_iff_internal] at hcandidate
        rcases Finset.mem_insert.mp hcandidate.1 with rfl | hcandidateTail
        · apply hinput
          exact
            (consistentCode_iff_forall_mem_internal
              target (input :: inputs) candidate).mp hcandidate.2 input
                (by simp)
        · have hconsistentTail :
              ConsistentCode target inputs candidate := by
            rw [consistentCode_iff_forall_mem_internal] at hcandidate ⊢
            intro found hfound
            exact hcandidate.2 found (by simp [hfound])
          have hsurvives :
              candidate ∈ ConsistentCodes target inputs codes :=
            (mem_consistentCodes_iff_internal
              target inputs codes candidate).mpr
                ⟨hcandidateTail, hconsistentTail⟩
          rw [hempty] at hsurvives
          simp at hsurvives

theorem isFor_of_consistentCodes_eq_empty_internal {arity threshold : ℕ}
    [NeZero arity] (target : BitString arity → Bool)
    (inputs : List (BitString arity)) (codes : Finset (List Bool))
    (hcovers : CoversThreshold (arity := arity) threshold codes)
    (hempty : ConsistentCodes target inputs codes = ∅) :
    IsFor target threshold inputs := by
  rw [isFor_iff_forall_not_agreesOn_internal]
  intro internalGates circuit hsize hagrees
  have hconsistent :
      ConsistentCode target inputs
        (CircuitCode.encodeCircuit circuit) := by
    rw [consistentCode_iff_forall_mem_internal]
    intro input hinput
    unfold CodeAgreesAt
    rw [CircuitCode.evalCode_encodeCircuit]
    exact congrArg some (hagrees input hinput)
  have hsurvives :
      CircuitCode.encodeCircuit circuit ∈
        ConsistentCodes target inputs codes :=
    (mem_consistentCodes_iff_internal target inputs codes
      (CircuitCode.encodeCircuit circuit)).mpr
        ⟨hcovers internalGates circuit hsize, hconsistent⟩
  rw [hempty] at hsurvives
  simp at hsurvives

theorem exists_isFor_length_le_card_internal {arity threshold : ℕ}
    [NeZero arity] (target : BitString arity → Bool)
    (codes : Finset (List Bool))
    (hcovers : CoversThreshold (arity := arity) threshold codes)
    (hfail : AllFailSomewhere target codes) :
    ∃ inputs : List (BitString arity),
      inputs.length ≤ codes.card ∧ IsFor target threshold inputs := by
  obtain ⟨inputs, hlength, hempty⟩ :=
    exists_inputs_consistentCodes_eq_empty_internal target codes hfail
  exact ⟨inputs, hlength,
    isFor_of_consistentCodes_eq_empty_internal
      target inputs codes hcovers hempty⟩

theorem exists_encode_not_mem_length_le_card_internal
    {arity threshold : ℕ} [NeZero arity]
    (target : BitString arity → Bool) (codes : Finset (List Bool))
    (hcovers : CoversThreshold (arity := arity) threshold codes)
    (hfail : AllFailSomewhere target codes) :
    ∃ inputs : List (BitString arity),
      inputs.length ≤ codes.card ∧
        (SuccinctMCSP.Instance.ofInputs threshold target inputs).encode ∉
          Complexity.SuccinctMCSP := by
  obtain ⟨inputs, hlength, hanti⟩ :=
    exists_isFor_length_le_card_internal target codes hcovers hfail
  exact ⟨inputs, hlength,
    (encode_not_mem_iff_isFor_internal target inputs).mpr hanti⟩

end AntiChecker

end Complexity
