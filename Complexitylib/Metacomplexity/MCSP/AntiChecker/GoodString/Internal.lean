/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.GoodString.Defs
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Counting.Internal
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Enumeration.Internal
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Extraction.Internal

/-!
# Good-string combinatorics -- proof internals
-/


public section

namespace Complexity

namespace AntiChecker

theorem survivorCodeOutput_eq_target_iff_internal {arity : ℕ}
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity))
    (code : SurvivorCode target threshold inputs)
    (input : BitString arity) :
    survivorCodeOutput target threshold inputs code input = target input ↔
      CodeAgreesAt target code.1 input := by
  have hcandidate : code.1 ∈ candidateCodes arity threshold :=
    (Finset.mem_filter.mp code.2).1
  have hsmall := (mem_candidateCodes_iff_internal.mp hcandidate).2
  unfold IsSmallCircuitCode at hsmall
  cases hdecode : CircuitCode.RawCircuit.decode? code.1 with
  | none => simp [hdecode] at hsmall
  | some circuit =>
      simp only [hdecode] at hsmall
      obtain ⟨hwell, -⟩ := hsmall
      have heval :
          (circuit.eval? input.toList).isSome :=
        (CircuitCode.RawCircuit.eval?_isSome_iff circuit input.toList).mpr
          (by simpa [BitString.length_toList] using hwell)
      obtain ⟨output, houtput⟩ := Option.isSome_iff_exists.mp heval
      have hevalCode :
          CircuitCode.evalCode arity code.1 input.toList = some output := by
        simp [CircuitCode.evalCode, BitString.length_toList, hdecode, houtput]
      unfold survivorCodeOutput CodeAgreesAt
      rw [hevalCode]
      simp

theorem card_survivorCode_internal {arity : ℕ}
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity)) :
    Fintype.card (SurvivorCode target threshold inputs) =
      candidateSurvivorCount target threshold inputs := by
  simp [SurvivorCode, candidateSurvivorCount, survivorCount]

theorem isSurvivorTupleCaughtAt_iff_agreementCount_le_internal
    {arity : ℕ} (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity)) (input : BitString arity)
    (tuple : Fin arity → SurvivorCode target threshold inputs) :
    IsSurvivorTupleCaughtAt target threshold inputs input tuple ↔
      survivorTupleAgreementCount target threshold inputs input tuple ≤
        arity / 2 := by
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin arity)))
    (fun i => CodeAgreesAt target (tuple i).1 input)
  have hdisagreements :
      tupleEventCount
          (disagreeingSurvivors target threshold inputs input) tuple =
        (Finset.univ.filter
          (fun i => ¬ CodeAgreesAt target (tuple i).1 input)).card := by
    unfold tupleEventCount disagreeingSurvivors
    congr 1
    ext i
    simp
  unfold IsSurvivorTupleCaughtAt survivorTupleAgreementCount
  rw [hdisagreements, Finset.mem_Icc]
  simp only [Finset.card_univ, Fintype.card_fin] at hpartition
  omega

theorem survivorTupleMajority_eq_target_of_not_caught_internal
    {arity : ℕ} (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity)) (input : BitString arity)
    (tuple : Fin arity → SurvivorCode target threshold inputs)
    (hnotCaught :
      ¬ IsSurvivorTupleCaughtAt target threshold inputs input tuple) :
    majority
        (fun i => survivorCodeOutput target threshold inputs (tuple i) input) =
      target input := by
  have hagreement : arity / 2 <
      survivorTupleAgreementCount target threshold inputs input tuple := by
    have hiff := isSurvivorTupleCaughtAt_iff_agreementCount_le_internal
      target threshold inputs input tuple
    have hnotLe :
        ¬ survivorTupleAgreementCount target threshold inputs input tuple ≤
          arity / 2 := fun hle => hnotCaught (hiff.mpr hle)
    omega
  unfold survivorTupleAgreementCount at hagreement
  have hagreementEq :
      (Finset.univ.filter
          (fun i => CodeAgreesAt target (tuple i).1 input)).card =
        (Finset.univ.filter (fun i =>
          survivorCodeOutput target threshold inputs (tuple i) input =
            target input)).card := by
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (survivorCodeOutput_eq_target_iff_internal
      target threshold inputs (tuple i) input).symm
  rw [hagreementEq] at hagreement
  cases htarget : target input with
  | false =>
      rw [majority_eq_false_iff]
      change
        (Finset.univ.filter (fun i =>
          survivorCodeOutput target threshold inputs (tuple i) input = true)).card ≤
            arity / 2
      have hpartition := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin arity)))
        (fun i =>
          survivorCodeOutput target threshold inputs (tuple i) input = true)
      have hfalseFilter :
          Finset.univ.filter (fun i =>
              survivorCodeOutput target threshold inputs (tuple i) input =
                false) =
            Finset.univ.filter (fun i =>
              ¬ survivorCodeOutput target threshold inputs (tuple i) input =
                true) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        cases survivorCodeOutput target threshold inputs (tuple i) input <;>
          simp
      have hpartition' :
          (Finset.univ.filter (fun i =>
              survivorCodeOutput target threshold inputs (tuple i) input =
                true)).card +
            (Finset.univ.filter (fun i =>
              survivorCodeOutput target threshold inputs (tuple i) input =
                false)).card = arity := by
        rw [hfalseFilter]
        simpa only [Finset.card_univ, Fintype.card_fin] using hpartition
      simp only [htarget] at hagreement
      omega
  | true =>
      rw [majority_eq_true_iff]
      change arity / 2 <
        (Finset.univ.filter (fun i =>
          survivorCodeOutput target threshold inputs (tuple i) input = true)).card
      simpa only [htarget] using hagreement

theorem everySurvivorTupleCaught_of_no_majorityComputes_internal
    {arity : ℕ} (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity))
    (hnoMajority :
      ∀ tuple : Fin arity → SurvivorCode target threshold inputs,
        ¬ SurvivorTupleMajorityComputes target threshold inputs tuple) :
    EverySurvivorTupleCaught target threshold inputs := by
  intro tuple
  by_contra hmissing
  apply hnoMajority tuple
  intro input
  apply survivorTupleMajority_eq_target_of_not_caught_internal
  intro hcaught
  exact hmissing ⟨input, hcaught⟩

theorem card_caughtSurvivorTuples_internal {arity : ℕ}
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity)) (input : BitString arity) :
    (caughtSurvivorTuples target threshold inputs input).card =
      ∑ disagreements ∈ Finset.Icc (arity - arity / 2) arity,
        arity.choose disagreements *
          (disagreeingSurvivors target threshold inputs input).card ^
            disagreements *
          (candidateSurvivorCount target threshold inputs -
              (disagreeingSurvivors target threshold inputs input).card) ^
            (arity - disagreements) := by
  unfold caughtSurvivorTuples IsSurvivorTupleCaughtAt
  simpa only [card_survivorCode_internal] using
    card_tupleEventCount_mem
      (k := arity)
      (disagreeingSurvivors target threshold inputs input)
      (Finset.Icc (arity - arity / 2) arity)

theorem card_disagreeingSurvivors_add_next_internal {arity : ℕ}
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity)) (input : BitString arity) :
    (disagreeingSurvivors target threshold inputs input).card +
        candidateSurvivorCount target threshold (input :: inputs) =
      candidateSurvivorCount target threshold inputs := by
  let current :=
    ConsistentCodes target inputs (candidateCodes arity threshold)
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := current) (CodeAgreesAt target · input)
  have hdisagree :
      (disagreeingSurvivors target threshold inputs input).card =
        (current.filter
          (fun code => ¬ CodeAgreesAt target code input)).card := by
    let codes :=
      ConsistentCodes target inputs (candidateCodes arity threshold)
    have hattach := Finset.filter_attach
      (fun code : List Bool => ¬ CodeAgreesAt target code input) codes
    have hcard := congrArg Finset.card hattach
    simpa [disagreeingSurvivors, SurvivorCode, current, codes] using hcard
  simp only [candidateSurvivorCount, survivorCount]
  rw [consistentCodes_cons_internal, hdisagree]
  simpa [current, add_comm] using hpartition

theorem isShrinkExtension_iff_survivorCount_le_mul_disagreements_internal
    {arity denominator threshold : ℕ} (hdenominator : 0 < denominator)
    (target : BitString arity → Bool)
    (inputs : List (BitString arity)) (input : BitString arity) :
    IsShrinkExtension denominator target threshold inputs input ↔
      candidateSurvivorCount target threshold inputs ≤
        denominator *
          (disagreeingSurvivors target threshold inputs input).card := by
  have hpartition :=
    card_disagreeingSurvivors_add_next_internal
      target threshold inputs input
  have hdenominatorEq :
      denominator = (denominator - 1) + 1 := by
    omega
  unfold IsShrinkExtension
  constructor <;> intro h
  · rw [← hpartition, hdenominatorEq] at h ⊢
    simp only [Nat.add_sub_cancel] at h ⊢
    ring_nf at h ⊢
    omega
  · rw [← hpartition, hdenominatorEq] at h ⊢
    simp only [Nat.add_sub_cancel] at h ⊢
    ring_nf at h ⊢
    omega

theorem exists_input_many_caughtSurvivorTuples_internal {arity : ℕ}
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity))
    (hall : EverySurvivorTupleCaught target threshold inputs) :
    ∃ input : BitString arity,
      candidateSurvivorCount target threshold inputs ^ arity ≤
        2 ^ arity *
          (caughtSurvivorTuples target threshold inputs input).card := by
  classical
  let Tuple := Fin arity → SurvivorCode target threshold inputs
  let witness : Tuple → BitString arity :=
    fun tuple => Classical.choose (hall tuple)
  have hwitness (tuple : Tuple) :
      IsSurvivorTupleCaughtAt target threshold inputs
        (witness tuple) tuple :=
    Classical.choose_spec (hall tuple)
  let fiber (input : BitString arity) : Finset Tuple :=
    Finset.univ.filter (fun tuple => witness tuple = input)
  let values :=
    (Finset.univ : Finset (BitString arity)).image
      (fun input => (fiber input).card)
  have hvalues : values.Nonempty := by
    simp [values]
  have hmaximum := Finset.max'_mem values hvalues
  rw [Finset.mem_image] at hmaximum
  obtain ⟨chosen, _, hchosen⟩ := hmaximum
  have hfiberMax (input : BitString arity) :
      (fiber input).card ≤ (fiber chosen).card := by
    rw [hchosen]
    exact Finset.le_max' values (fiber input).card (by simp [values])
  have hfiberSubset :
      fiber chosen ⊆ caughtSurvivorTuples target threshold inputs chosen := by
    intro tuple htuple
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at htuple
    simp only [caughtSurvivorTuples, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rw [← htuple]
    exact hwitness tuple
  have hsum :
      ∑ input : BitString arity, (fiber input).card =
        (Finset.univ : Finset Tuple).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    simp
  refine ⟨chosen, ?_⟩
  calc
    candidateSurvivorCount target threshold inputs ^ arity =
        (Finset.univ : Finset Tuple).card := by
      simp only [Finset.card_univ, Tuple, Fintype.card_fun,
        Fintype.card_fin]
      rw [card_survivorCode_internal]
    _ = ∑ input : BitString arity, (fiber input).card := hsum.symm
    _ ≤ ∑ _input : BitString arity, (fiber chosen).card := by
      apply Finset.sum_le_sum
      intro input _
      exact hfiberMax input
    _ = 2 ^ arity * (fiber chosen).card := by
      simp
    _ ≤ 2 ^ arity *
          (caughtSurvivorTuples target threshold inputs chosen).card :=
      Nat.mul_le_mul_left (2 ^ arity)
        (Finset.card_le_card hfiberSubset)

end AntiChecker

end Complexity
