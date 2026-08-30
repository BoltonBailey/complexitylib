/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Hamming.Defs

/-!
# Finite Boolean Hamming geometry -- proof internals
-/


public section

namespace Complexity

namespace BooleanHamming

theorem mem_disagreement_internal {length : ℕ} (left right : Word length)
    (coordinate : Fin length) :
    coordinate ∈ disagreement left right ↔
      left coordinate ≠ right coordinate := by
  simp [disagreement]

theorem distance_refl_internal {length : ℕ} (word : Word length) :
    distance word word = 0 := by
  simp [distance, disagreement]

theorem distance_comm_internal {length : ℕ} (left right : Word length) :
    distance left right = distance right left := by
  apply congrArg Finset.card
  ext coordinate
  simp [disagreement, ne_comm]

theorem distance_eq_zero_iff_internal {length : ℕ} (left right : Word length) :
    distance left right = 0 ↔ left = right := by
  constructor
  · intro hzero
    funext coordinate
    by_contra hne
    have hmem : coordinate ∈ disagreement left right :=
      (mem_disagreement_internal left right coordinate).mpr hne
    have hempty : disagreement left right = ∅ :=
      Finset.card_eq_zero.mp hzero
    rw [hempty] at hmem
    simp at hmem
  · rintro rfl
    exact distance_refl_internal left

theorem distance_triangle_internal {length : ℕ}
    (first second third : Word length) :
    distance first third ≤ distance first second + distance second third := by
  unfold distance
  calc
    (disagreement first third).card ≤
        (disagreement first second ∪ disagreement second third).card := by
      apply Finset.card_le_card
      intro coordinate hcoordinate
      have hne :=
        (mem_disagreement_internal first third coordinate).mp hcoordinate
      apply Finset.mem_union.mpr
      by_cases hfirst : first coordinate = second coordinate
      · right
        apply (mem_disagreement_internal second third coordinate).mpr
        intro hsecond
        exact hne (hfirst.trans hsecond)
      · exact Or.inl <|
          (mem_disagreement_internal first second coordinate).mpr hfirst
    _ ≤ (disagreement first second).card +
        (disagreement second third).card :=
      Finset.card_union_le (disagreement first second)
        (disagreement second third)

theorem distance_le_length_internal {length : ℕ} (left right : Word length) :
    distance left right ≤ length := by
  unfold distance
  calc
    (disagreement left right).card ≤
        (Finset.univ : Finset (Fin length)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = length := by simp

theorem distance_eq_popCount_translate_internal {length : ℕ}
    (left right : Word length) :
    distance left right = popCount (translate right left) := by
  apply congrArg Finset.card
  ext coordinate
  simp [disagreement, translate]

theorem translate_translate_internal {length : ℕ}
    (center word : Word length) :
    translate center (translate center word) = word := by
  funext coordinate
  simp [translate]

theorem relativeDistance_eq_distance_div_internal {length : ℕ}
    (left right : Word length) :
    BooleanListCode.relativeDistance left right =
      (distance left right : ℚ) / length := by
  simp [BooleanListCode.relativeDistance, uniformProbability,
    distance, disagreement]

theorem mem_sphere_internal {length : ℕ} (center word : Word length)
    (radius : ℕ) :
    word ∈ sphere center radius ↔ distance word center = radius := by
  simp [sphere]

theorem mem_ball_internal {length : ℕ} (center word : Word length)
    (radius : ℕ) :
    word ∈ ball center radius ↔ distance word center ≤ radius := by
  simp [ball]

theorem ball_mono_internal {length : ℕ} (center : Word length)
    {first second : ℕ} (hradius : first ≤ second) :
    ball center first ⊆ ball center second := by
  intro word hword
  exact (mem_ball_internal center word second).mpr <|
    (mem_ball_internal center word first).mp hword |>.trans hradius

theorem card_distance_filter_eq_popCount_filter_internal {length : ℕ}
    (center : Word length) (predicate : ℕ → Prop) [DecidablePred predicate] :
    (Finset.univ.filter fun word : Word length =>
      predicate (distance word center)).card =
    (Finset.univ.filter fun word : Word length =>
      predicate (popCount word)).card := by
  apply Finset.card_bij'
      (fun word _ => translate center word)
      (fun word _ => translate center word)
  · intro word hword
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hword ⊢
    rw [← distance_eq_popCount_translate_internal]
    exact hword
  · intro word hword
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hword ⊢
    rw [distance_eq_popCount_translate_internal,
      translate_translate_internal]
    exact hword
  · intro word _
    exact translate_translate_internal center word
  · intro word _
    exact translate_translate_internal center word

theorem card_sphere_internal {length : ℕ} (center : Word length)
    (radius : ℕ) :
    (sphere center radius).card = length.choose radius := by
  calc
    (sphere center radius).card =
        (Finset.univ.filter fun word : Word length =>
          distance word center = radius).card := rfl
    _ = (Finset.univ.filter fun word : Word length =>
          popCount word = radius).card :=
      card_distance_filter_eq_popCount_filter_internal center
        (fun weight => weight = radius)
    _ = length.choose radius := card_filter_popCount_eq length radius

theorem card_ball_internal {length : ℕ} (center : Word length)
    (radius : ℕ) :
    (ball center radius).card = volume length radius := by
  calc
    (ball center radius).card =
        (Finset.univ.filter fun word : Word length =>
          distance word center ≤ radius).card := rfl
    _ = (Finset.univ.filter fun word : Word length =>
          popCount word ≤ radius).card :=
      card_distance_filter_eq_popCount_filter_internal center
        (fun weight => weight ≤ radius)
    _ = (Finset.univ.filter fun word : Word length =>
          popCount word ∈ Finset.range (radius + 1)).card := by
      congr 1
      ext word
      simp
    _ = ∑ weight ∈ Finset.range (radius + 1), length.choose weight :=
      card_filter_popCount_mem length (Finset.range (radius + 1))
    _ = volume length radius := rfl

theorem volume_le_two_pow_internal (length radius : ℕ) :
    volume length radius ≤ 2 ^ length := by
  let center : Word length := fun _ => false
  rw [← card_ball_internal center radius]
  calc
    (ball center radius).card ≤
        (Finset.univ : Finset (Word length)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = 2 ^ length := by
      rw [Finset.card_univ, card_finArrowBool]

theorem volume_eq_two_pow_of_length_le_radius_internal
    {length radius : ℕ} (hradius : length ≤ radius) :
    volume length radius = 2 ^ length := by
  let center : Word length := fun _ => false
  rw [← card_ball_internal center radius]
  have hball : ball center radius = Finset.univ := by
    ext word
    simp [ball, (distance_le_length_internal word center).trans hradius]
  rw [hball, Finset.card_univ, card_finArrowBool]

theorem disjoint_balls_of_two_mul_radius_lt_distance_internal
    {length radius : ℕ} {left right : Word length}
    (hfar : 2 * radius < distance left right) :
    Disjoint (ball left radius) (ball right radius) := by
  apply Finset.disjoint_left.mpr
  intro word hleft hright
  have hwordLeft : distance word left ≤ radius :=
    (mem_ball_internal left word radius).mp hleft
  have hleftWord : distance left word ≤ radius := by
    rw [distance_comm_internal]
    exact hwordLeft
  have hwordRight : distance word right ≤ radius :=
    (mem_ball_internal right word radius).mp hright
  have htriangle := distance_triangle_internal left word right
  omega

theorem pairwiseDisjoint_balls_of_isSeparated_internal
    {length minimumDistance radius : ℕ} {code : Finset (Word length)}
    (hcode : IsSeparated code minimumDistance)
    (hradius : 2 * radius < minimumDistance) :
    (code : Set (Word length)).PairwiseDisjoint fun center =>
      ball center radius := by
  intro left hleft right hright hne
  apply disjoint_balls_of_two_mul_radius_lt_distance_internal
  exact hradius.trans_le (hcode hleft hright hne)

theorem packing_bound_internal
    {length minimumDistance radius : ℕ} {code : Finset (Word length)}
    (hcode : IsSeparated code minimumDistance)
    (hradius : 2 * radius < minimumDistance) :
    code.card * volume length radius ≤ 2 ^ length := by
  have hdisjoint :
      (code : Set (Word length)).PairwiseDisjoint fun center =>
        ball center radius :=
    pairwiseDisjoint_balls_of_isSeparated_internal hcode hradius
  calc
    code.card * volume length radius =
        ∑ center ∈ code, (ball center radius).card := by
      simp [card_ball_internal]
    _ = (code.biUnion fun center => ball center radius).card :=
      (Finset.card_biUnion hdisjoint).symm
    _ ≤ (Finset.univ : Finset (Word length)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = 2 ^ length := by
      rw [Finset.card_univ, card_finArrowBool]

end BooleanHamming

end Complexity
