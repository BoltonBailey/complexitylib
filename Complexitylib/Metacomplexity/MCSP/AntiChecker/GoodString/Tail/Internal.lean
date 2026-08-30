/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.GoodString.Tail.Defs
import Complexitylib.Metacomplexity.MCSP.AntiChecker.GoodString.Internal

/-!
# Good-string binomial-tail bound -- proof internals
-/


public section

namespace Complexity

namespace AntiChecker

private theorem weighted_tail_term_le
    {arity survivors disagreements index : ℕ}
    (hdisagreements : disagreements ≤ survivors)
    (hlower : arity - arity / 2 ≤ index) (hupper : index ≤ arity) :
    arity.choose index * disagreements ^ index *
        (survivors - disagreements) ^ (arity - index) ≤
      arity.choose index *
        (disagreements ^ (arity - arity / 2) *
          survivors ^ (arity / 2)) := by
  let half := arity / 2
  let upperHalf := arity - half
  have hdisagreementPower :
      disagreements ^ index ≤
        disagreements ^ upperHalf * survivors ^ (index - upperHalf) := by
    calc
      disagreements ^ index =
          disagreements ^ (upperHalf + (index - upperHalf)) := by
        congr 1
        omega
      _ = disagreements ^ upperHalf *
          disagreements ^ (index - upperHalf) := by
        rw [pow_add]
      _ ≤ disagreements ^ upperHalf *
          survivors ^ (index - upperHalf) :=
        Nat.mul_le_mul_left _
          (Nat.pow_le_pow_left hdisagreements _)
  have hremainingPower :
      (survivors - disagreements) ^ (arity - index) ≤
        survivors ^ (arity - index) :=
    Nat.pow_le_pow_left (Nat.sub_le survivors disagreements) _
  calc
    arity.choose index * disagreements ^ index *
          (survivors - disagreements) ^ (arity - index) ≤
        arity.choose index *
            (disagreements ^ upperHalf *
              survivors ^ (index - upperHalf)) *
          survivors ^ (arity - index) :=
      Nat.mul_le_mul
        (Nat.mul_le_mul_left (arity.choose index) hdisagreementPower)
        hremainingPower
    _ = arity.choose index *
          (disagreements ^ upperHalf * survivors ^ half) := by
      have hexponents :
          (index - upperHalf) + (arity - index) = half := by
        dsimp only [upperHalf, half]
        omega
      rw [mul_assoc, mul_assoc, ← pow_add, hexponents]

private theorem sum_choose_Icc_le_pow_two (arity lower : ℕ) :
    ∑ index ∈ Finset.Icc lower arity, arity.choose index ≤
      2 ^ arity := by
  calc
    ∑ index ∈ Finset.Icc lower arity, arity.choose index ≤
        ∑ index ∈ Finset.range (arity + 1), arity.choose index := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro index hindex
        simp only [Finset.mem_Icc] at hindex
        exact Finset.mem_range.mpr (by omega)
      · intro index _ _
        exact Nat.zero_le _
    _ = 2 ^ arity := Nat.sum_range_choose arity

theorem card_caughtSurvivorTuples_le_upperBound_internal {arity : ℕ}
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity)) (input : BitString arity) :
    (caughtSurvivorTuples target threshold inputs input).card ≤
      caughtTupleUpperBound arity
        (candidateSurvivorCount target threshold inputs)
        (disagreeingSurvivors target threshold inputs input).card := by
  let survivors := candidateSurvivorCount target threshold inputs
  let disagreements :=
    (disagreeingSurvivors target threshold inputs input).card
  let half := arity / 2
  let upperHalf := arity - half
  have hdisagreements : disagreements ≤ survivors := by
    have hpartition :=
      card_disagreeingSurvivors_add_next_internal
        target threshold inputs input
    dsimp only [disagreements, survivors]
    omega
  rw [card_caughtSurvivorTuples_internal]
  unfold caughtTupleUpperBound
  change
    ∑ index ∈ Finset.Icc upperHalf arity,
        arity.choose index * disagreements ^ index *
          (survivors - disagreements) ^ (arity - index) ≤
      2 ^ arity * disagreements ^ upperHalf * survivors ^ half
  calc
    ∑ index ∈ Finset.Icc upperHalf arity,
          arity.choose index * disagreements ^ index *
            (survivors - disagreements) ^ (arity - index) ≤
        ∑ index ∈ Finset.Icc upperHalf arity,
          arity.choose index *
            (disagreements ^ upperHalf * survivors ^ half) := by
      apply Finset.sum_le_sum
      intro index hindex
      exact weighted_tail_term_le hdisagreements
        (Finset.mem_Icc.mp hindex).1 (Finset.mem_Icc.mp hindex).2
    _ = (∑ index ∈ Finset.Icc upperHalf arity,
          arity.choose index) *
        (disagreements ^ upperHalf * survivors ^ half) := by
      rw [Finset.sum_mul]
    _ ≤ 2 ^ arity *
        (disagreements ^ upperHalf * survivors ^ half) :=
      Nat.mul_le_mul_right _ (sum_choose_Icc_le_pow_two arity upperHalf)
    _ = 2 ^ arity * disagreements ^ upperHalf * survivors ^ half := by
      ring

theorem exists_input_survivorCount_le_sixteen_mul_disagreements_internal
    {arity : ℕ} (harity : 0 < arity)
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity))
    (hall : EverySurvivorTupleCaught target threshold inputs) :
    ∃ input : BitString arity,
      candidateSurvivorCount target threshold inputs ≤
        16 * (disagreeingSurvivors target threshold inputs input).card := by
  obtain ⟨input, havg⟩ :=
    exists_input_many_caughtSurvivorTuples_internal
      target threshold inputs hall
  refine ⟨input, ?_⟩
  let survivors := candidateSurvivorCount target threshold inputs
  let disagreements :=
    (disagreeingSurvivors target threshold inputs input).card
  let half := arity / 2
  let upperHalf := arity - half
  have htail :=
    card_caughtSurvivorTuples_le_upperBound_internal
      target threshold inputs input
  have hcombined :
      survivors ^ arity ≤
        4 ^ arity * disagreements ^ upperHalf * survivors ^ half := by
    calc
      survivors ^ arity ≤
          2 ^ arity *
            (caughtSurvivorTuples target threshold inputs input).card :=
        havg
      _ ≤ 2 ^ arity *
          (2 ^ arity * disagreements ^ upperHalf * survivors ^ half) :=
        Nat.mul_le_mul_left (2 ^ arity) htail
      _ = 4 ^ arity * disagreements ^ upperHalf * survivors ^ half := by
        calc
          2 ^ arity *
                (2 ^ arity * disagreements ^ upperHalf * survivors ^ half) =
              (2 ^ arity * 2 ^ arity) *
                disagreements ^ upperHalf * survivors ^ half := by
            ring
          _ = (2 * 2) ^ arity *
                disagreements ^ upperHalf * survivors ^ half := by
            rw [mul_pow]
          _ = 4 ^ arity * disagreements ^ upperHalf * survivors ^ half := by
            norm_num
  by_cases hsurvivors : survivors = 0
  · simp [survivors, hsurvivors]
  have hsplit : upperHalf + half = arity := by
    dsimp only [upperHalf, half]
    exact Nat.sub_add_cancel (Nat.div_le_self arity 2)
  have hcancel :
      survivors ^ upperHalf ≤
        4 ^ arity * disagreements ^ upperHalf := by
    apply Nat.le_of_mul_le_mul_right (c := survivors ^ half)
    · calc
        survivors ^ upperHalf * survivors ^ half = survivors ^ arity := by
          rw [← pow_add, hsplit]
        _ ≤ 4 ^ arity * disagreements ^ upperHalf * survivors ^ half :=
          hcombined
    · exact pow_pos (Nat.pos_of_ne_zero hsurvivors) _
  have harityLe : arity ≤ 2 * upperHalf := by
    dsimp only [upperHalf, half]
    omega
  have hfourPower : 4 ^ arity ≤ 16 ^ upperHalf := by
    calc
      4 ^ arity ≤ 4 ^ (2 * upperHalf) :=
        pow_le_pow_right' (by omega) harityLe
      _ = (4 ^ 2) ^ upperHalf := by
        rw [pow_mul]
      _ = 16 ^ upperHalf := by
        norm_num
  have hpower :
      survivors ^ upperHalf ≤ (16 * disagreements) ^ upperHalf := by
    calc
      survivors ^ upperHalf ≤
          4 ^ arity * disagreements ^ upperHalf := hcancel
      _ ≤ 16 ^ upperHalf * disagreements ^ upperHalf :=
        Nat.mul_le_mul_right (disagreements ^ upperHalf) hfourPower
      _ = (16 * disagreements) ^ upperHalf := by
        rw [mul_pow]
  have hupperHalf : upperHalf ≠ 0 := by
    dsimp only [upperHalf, half]
    omega
  exact (Nat.pow_le_pow_iff_left hupperHalf).mp hpower

theorem hasShrinkExtension_two_mul_arity_internal
    {arity : ℕ} (harity : 8 ≤ arity)
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity))
    (hall : EverySurvivorTupleCaught target threshold inputs) :
    HasShrinkExtension (2 * arity) target threshold inputs := by
  obtain ⟨input, hdisagreements⟩ :=
    exists_input_survivorCount_le_sixteen_mul_disagreements_internal
      (by omega) target threshold inputs hall
  refine ⟨input, ?_⟩
  apply
    (isShrinkExtension_iff_survivorCount_le_mul_disagreements_internal
      (by omega) target inputs input).mpr
  exact hdisagreements.trans <|
    Nat.mul_le_mul_right
      (disagreeingSurvivors target threshold inputs input).card (by omega)

end AntiChecker

end Complexity
