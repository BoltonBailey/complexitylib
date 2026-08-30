/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.Hashing.Defs

/-!
# Pairwise-independent hashing -- proof internals
-/


public section

namespace Complexity

namespace PairwiseIndependentHash

/-- Internal double-counting identity for total target-cell mass. -/
private theorem sum_cellSize_eq_sum_fiberCard
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth) :
    ∑ seed : BitString seedWidth, (hash.cellSize set target seed : ℚ) =
      ∑ input ∈ set,
        ((Finset.univ.filter fun seed : BitString seedWidth =>
          hash.eval seed input = target).card : ℚ) := by
  classical
  simp only [cellSize, cell, Finset.card_filter]
  push_cast
  rw [Finset.sum_comm]

/-- Internal first-moment identity for one hash cell. -/
theorem averageCellSize_eq_internal
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth) :
    hash.averageCellSize set target =
      (set.card : ℚ) / (2 : ℚ) ^ rangeWidth := by
  classical
  rw [averageCellSize, sum_cellSize_eq_sum_fiberCard, Finset.sum_div]
  calc
    ∑ input ∈ set,
        (Finset.univ.filter fun seed : BitString seedWidth =>
          hash.eval seed input = target).card / (2 : ℚ) ^ seedWidth =
        ∑ _input ∈ set, 1 / (2 : ℚ) ^ rangeWidth := by
          apply Finset.sum_congr rfl
          intro input _
          exact hash.uniform input target
    _ = (set.card : ℚ) * (1 / (2 : ℚ) ^ rangeWidth) := by simp
    _ = (set.card : ℚ) / (2 : ℚ) ^ rangeWidth := by ring

/-- Internal double-counting identity for total ordered pair mass. -/
private theorem sum_orderedPairCellSize_eq_sum_pairFiberCard
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth) :
    ∑ seed : BitString seedWidth,
        (hash.orderedPairCellSize set target seed : ℚ) =
      ∑ pair ∈ set.offDiag,
        ((Finset.univ.filter fun seed : BitString seedWidth =>
          hash.eval seed pair.1 = target ∧
            hash.eval seed pair.2 = target).card : ℚ) := by
  classical
  simp only [orderedPairCellSize, Finset.card_filter]
  push_cast
  rw [Finset.sum_comm]

/-- Internal second factorial moment for one hash cell. -/
theorem averageOrderedPairCellSize_eq_internal
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth) :
    hash.averageOrderedPairCellSize set target =
      ((set.card * set.card - set.card : ℕ) : ℚ) /
        (2 : ℚ) ^ (2 * rangeWidth) := by
  classical
  rw [averageOrderedPairCellSize,
    sum_orderedPairCellSize_eq_sum_pairFiberCard, Finset.sum_div]
  calc
    ∑ pair ∈ set.offDiag,
        (Finset.univ.filter fun seed : BitString seedWidth =>
          hash.eval seed pair.1 = target ∧
            hash.eval seed pair.2 = target).card /
              (2 : ℚ) ^ seedWidth =
        ∑ _pair ∈ set.offDiag,
          1 / (2 : ℚ) ^ (2 * rangeWidth) := by
            apply Finset.sum_congr rfl
            intro pair hpair
            have hne : pair.1 ≠ pair.2 := (Finset.mem_offDiag.mp hpair).2.2
            exact hash.pairwise hne target target
    _ = (set.offDiag.card : ℚ) *
        (1 / (2 : ℚ) ^ (2 * rangeWidth)) := by simp
    _ = ((set.card * set.card - set.card : ℕ) : ℚ) /
        (2 : ℚ) ^ (2 * rangeWidth) := by
          rw [Finset.offDiag_card]
          ring

/-- Internal pointwise relation between cell squares and ordered distinct
pairs. -/
theorem orderedPairCellSize_eq_internal
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth)
    (seed : BitString seedWidth) :
    hash.orderedPairCellSize set target seed =
      hash.cellSize set target seed * hash.cellSize set target seed -
        hash.cellSize set target seed := by
  classical
  have hfilter :
      set.offDiag.filter (fun pair =>
        hash.eval seed pair.1 = target ∧ hash.eval seed pair.2 = target) =
        (hash.cell set target seed).offDiag := by
    ext pair
    simp only [Finset.mem_filter, Finset.mem_offDiag, cell]
    aesop
  rw [orderedPairCellSize, hfilter, Finset.offDiag_card, cellSize]

/-- Internal decomposition of the second moment into the first and second
factorial moments. -/
theorem averageCellSizeSquare_eq_add_internal
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth) :
    hash.averageCellSizeSquare set target =
      hash.averageCellSize set target +
        hash.averageOrderedPairCellSize set target := by
  classical
  unfold averageCellSizeSquare averageCellSize averageOrderedPairCellSize
  rw [← add_div]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro seed _
  rw [hash.orderedPairCellSize_eq_internal set target seed]
  let count := hash.cellSize set target seed
  have hle : count ≤ count * count := by
    cases count with
    | zero => simp
    | succ count =>
        exact Nat.le_mul_of_pos_right (count + 1) (by omega)
  dsimp only [count] at hle ⊢
  rw [Nat.cast_sub hle]
  push_cast
  ring

/-- Internal closed form for the second cell-size moment. -/
theorem averageCellSizeSquare_eq_internal
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth) :
    hash.averageCellSizeSquare set target =
      (set.card : ℚ) / (2 : ℚ) ^ rangeWidth +
        ((set.card * set.card - set.card : ℕ) : ℚ) /
          (2 : ℚ) ^ (2 * rangeWidth) := by
  rw [hash.averageCellSizeSquare_eq_add_internal set target,
    hash.averageCellSize_eq_internal set target,
    hash.averageOrderedPairCellSize_eq_internal set target]

/-- Internal variance identity for a finite uniform hash family. -/
theorem cellSizeVariance_eq_sub_internal
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth) :
    hash.cellSizeVariance set target =
      hash.averageCellSizeSquare set target -
        hash.averageCellSize set target ^ 2 := by
  classical
  unfold cellSizeVariance averageCellSizeSquare
  have hsum :
      ∑ seed : BitString seedWidth,
          (hash.cellSize set target seed : ℚ) =
        hash.averageCellSize set target * (2 : ℚ) ^ seedWidth := by
    rw [averageCellSize]
    field_simp
  have hcard :
      (Fintype.card (BitString seedWidth) : ℚ) =
        (2 : ℚ) ^ seedWidth := by
    rw [card_finArrowBool]
    norm_num
  field_simp
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  rw [← Finset.sum_mul, ← Finset.mul_sum, hsum, hcard]
  ring

/-- Internal closed form for the variance of one target-cell size. -/
theorem cellSizeVariance_eq_internal
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth) :
    hash.cellSizeVariance set target =
      (set.card : ℚ) / (2 : ℚ) ^ rangeWidth *
        (1 - 1 / (2 : ℚ) ^ rangeWidth) := by
  rw [hash.cellSizeVariance_eq_sub_internal set target,
    hash.averageCellSizeSquare_eq_internal set target,
    hash.averageCellSize_eq_internal set target]
  have hle : set.card ≤ set.card * set.card := by
    cases set.card with
    | zero => simp
    | succ count =>
        exact Nat.le_mul_of_pos_right (count + 1) (by omega)
  rw [Nat.cast_sub hle]
  push_cast
  rw [pow_mul']
  ring

/-- Internal nonnegativity of finite uniform variance. -/
theorem cellSizeVariance_nonneg_internal
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth) :
    0 ≤ hash.cellSizeVariance set target := by
  unfold cellSizeVariance
  positivity

/-- Internal pairwise-independence variance bound. -/
theorem cellSizeVariance_le_averageCellSize_internal
    {domainWidth rangeWidth seedWidth : ℕ}
    (hash : PairwiseIndependentHash domainWidth rangeWidth seedWidth)
    (set : Finset (BitString domainWidth)) (target : BitString rangeWidth) :
    hash.cellSizeVariance set target ≤ hash.averageCellSize set target := by
  rw [hash.cellSizeVariance_eq_internal set target,
    hash.averageCellSize_eq_internal set target]
  have hmean : 0 ≤ (set.card : ℚ) / (2 : ℚ) ^ rangeWidth := by positivity
  have hinv : 0 ≤ 1 / (2 : ℚ) ^ rangeWidth := by positivity
  nlinarith

end PairwiseIndependentHash

end Complexity
