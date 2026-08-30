/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Hamming.Defs
public import Complexitylib.Metacomplexity.Hamming.Internal
public import Complexitylib.Metacomplexity.Hamming.Code

/-!
# Finite Boolean Hamming geometry

This module supplies the exact finite geometry used by coding-based
metacomplexity and hardness magnification: a metric on Boolean words, exact
binomial sphere and ball counts, and the Hamming packing bound. Absolute and
rational relative distance are connected explicitly. `BooleanCode` then packages
injective finite encodings, exact rate, minimum distance, and exhaustive unique
decoding without asserting an efficient implementation.
-/


public section

namespace Complexity

namespace BooleanHamming

/-- Membership in the disagreement support is pointwise inequality. -/
@[simp] theorem mem_disagreement {length : ℕ} (left right : Word length)
    (coordinate : Fin length) :
    coordinate ∈ disagreement left right ↔
      left coordinate ≠ right coordinate :=
  mem_disagreement_internal left right coordinate

/-- Every word has distance zero from itself. -/
@[simp] theorem distance_refl {length : ℕ} (word : Word length) :
    distance word word = 0 :=
  distance_refl_internal word

/-- Boolean Hamming distance is symmetric. -/
theorem distance_comm {length : ℕ} (left right : Word length) :
    distance left right = distance right left :=
  distance_comm_internal left right

/-- Distance zero characterizes equality of words. -/
@[simp] theorem distance_eq_zero_iff {length : ℕ} (left right : Word length) :
    distance left right = 0 ↔ left = right :=
  distance_eq_zero_iff_internal left right

/-- Boolean Hamming distance satisfies the triangle inequality. -/
theorem distance_triangle {length : ℕ}
    (first second third : Word length) :
    distance first third ≤ distance first second + distance second third :=
  distance_triangle_internal first second third

/-- Hamming distance never exceeds the word length. -/
theorem distance_le_length {length : ℕ} (left right : Word length) :
    distance left right ≤ length :=
  distance_le_length_internal left right

/-- Distance from `right` is the Hamming weight after XOR translation. -/
theorem distance_eq_popCount_translate {length : ℕ}
    (left right : Word length) :
    distance left right = popCount (translate right left) :=
  distance_eq_popCount_translate_internal left right

/-- XOR translation by a fixed center is an involution. -/
@[simp] theorem translate_translate {length : ℕ}
    (center word : Word length) :
    translate center (translate center word) = word :=
  translate_translate_internal center word

/-- The list-decoding relative distance is absolute Hamming distance divided by
the coordinate count. This remains valid at length zero under rational
division's total convention. -/
theorem relativeDistance_eq_distance_div {length : ℕ}
    (left right : Word length) :
    BooleanListCode.relativeDistance left right =
      (distance left right : ℚ) / length :=
  relativeDistance_eq_distance_div_internal left right

/-- Membership in a Hamming sphere. -/
@[simp] theorem mem_sphere {length : ℕ} (center word : Word length)
    (radius : ℕ) :
    word ∈ sphere center radius ↔ distance word center = radius :=
  mem_sphere_internal center word radius

/-- Membership in a closed Hamming ball. -/
@[simp] theorem mem_ball {length : ℕ} (center word : Word length)
    (radius : ℕ) :
    word ∈ ball center radius ↔ distance word center ≤ radius :=
  mem_ball_internal center word radius

/-- Increasing the radius enlarges a Hamming ball. -/
theorem ball_mono {length : ℕ} (center : Word length)
    {first second : ℕ} (hradius : first ≤ second) :
    ball center first ⊆ ball center second :=
  ball_mono_internal center hradius

/-- XOR translation makes every distance-profile count center-independent. -/
theorem card_distance_filter_eq_popCount_filter {length : ℕ}
    (center : Word length) (predicate : ℕ → Prop) [DecidablePred predicate] :
    (Finset.univ.filter fun word : Word length =>
      predicate (distance word center)).card =
    (Finset.univ.filter fun word : Word length =>
      predicate (popCount word)).card :=
  card_distance_filter_eq_popCount_filter_internal center predicate

/-- A radius-`r` sphere in the Boolean cube has exactly `length.choose r`
words, independently of its center. -/
theorem card_sphere {length : ℕ} (center : Word length) (radius : ℕ) :
    (sphere center radius).card = length.choose radius :=
  card_sphere_internal center radius

/-- A radius-`r` Boolean Hamming ball has its exact binomial volume. -/
theorem card_ball {length : ℕ} (center : Word length) (radius : ℕ) :
    (ball center radius).card = volume length radius :=
  card_ball_internal center radius

/-- A Hamming ball contains at most all `2^length` Boolean words. -/
theorem volume_le_two_pow (length radius : ℕ) :
    volume length radius ≤ 2 ^ length :=
  volume_le_two_pow_internal length radius

/-- Once the radius reaches the word length, the ball is the entire cube. -/
theorem volume_eq_two_pow_of_length_le_radius
    {length radius : ℕ} (hradius : length ≤ radius) :
    volume length radius = 2 ^ length :=
  volume_eq_two_pow_of_length_le_radius_internal hradius

/-- Balls of radius `r` around centers farther than `2r` are disjoint. -/
theorem disjoint_balls_of_two_mul_radius_lt_distance
    {length radius : ℕ} {left right : Word length}
    (hfar : 2 * radius < distance left right) :
    Disjoint (ball left radius) (ball right radius) :=
  disjoint_balls_of_two_mul_radius_lt_distance_internal hfar

/-- A separated finite code induces pairwise-disjoint decoding balls below
half its minimum distance. -/
theorem pairwiseDisjoint_balls_of_isSeparated
    {length minimumDistance radius : ℕ} {code : Finset (Word length)}
    (hcode : IsSeparated code minimumDistance)
    (hradius : 2 * radius < minimumDistance) :
    (code : Set (Word length)).PairwiseDisjoint fun center =>
      ball center radius :=
  pairwiseDisjoint_balls_of_isSeparated_internal hcode hradius

/-- Finite Boolean Hamming packing bound. -/
theorem packing_bound
    {length minimumDistance radius : ℕ} {code : Finset (Word length)}
    (hcode : IsSeparated code minimumDistance)
    (hradius : 2 * radius < minimumDistance) :
    code.card * volume length radius ≤ 2 ^ length :=
  packing_bound_internal hcode hradius

end BooleanHamming

end Complexity
