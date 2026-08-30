/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.FiniteCounting
public import Complexitylib.Metacomplexity.ListDecoding.Defs
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Finite Boolean Hamming geometry -- definitions

This module fixes absolute Hamming distance on `n`-bit words, finite spheres
and balls, their binomial volume, and a minimum-distance predicate for finite
codes. The rational relative-distance bridge remains compatible with the
existing Boolean list-decoding API.
-/


@[expose] public section

namespace Complexity

namespace BooleanHamming

/-- A fixed-length Boolean word. -/
abbrev Word (length : ℕ) := Fin length → Bool

/-- Coordinates on which two Boolean words disagree. -/
def disagreement {length : ℕ} (left right : Word length) : Finset (Fin length) :=
  Finset.univ.filter fun coordinate => left coordinate ≠ right coordinate

/-- Absolute Hamming distance. -/
def distance {length : ℕ} (left right : Word length) : ℕ :=
  (disagreement left right).card

/-- Translate a Boolean word by coordinatewise XOR with a fixed center. -/
def translate {length : ℕ} (center word : Word length) : Word length :=
  fun coordinate => Bool.xor (word coordinate) (center coordinate)

/-- Words at absolute distance exactly `radius` from `center`. -/
def sphere {length : ℕ} (center : Word length) (radius : ℕ) :
    Finset (Word length) :=
  Finset.univ.filter fun word => distance word center = radius

/-- Words at absolute distance at most `radius` from `center`. -/
def ball {length : ℕ} (center : Word length) (radius : ℕ) :
    Finset (Word length) :=
  Finset.univ.filter fun word => distance word center ≤ radius

/-- Binomial volume of a Boolean Hamming ball. Terms above `length` vanish. -/
def volume (length radius : ℕ) : ℕ :=
  ∑ weight ∈ Finset.range (radius + 1), length.choose weight

/-- A finite code has pairwise distance at least `minimumDistance`. -/
def IsSeparated {length : ℕ} (code : Finset (Word length))
    (minimumDistance : ℕ) : Prop :=
  (code : Set (Word length)).Pairwise fun left right =>
    minimumDistance ≤ distance left right

end BooleanHamming

end Complexity
