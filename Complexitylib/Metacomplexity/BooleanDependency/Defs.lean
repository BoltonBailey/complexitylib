/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Data.Finset.Card

/-!
# Finite Boolean dependency tables -- definitions

This module gives canonical restriction, extension, and table operations for a
function of Boolean coordinates that depends on only a finite set. The table is
indexed by assignments to exactly those coordinates, making its entry count an
explicit resource rather than merely asserting that the function factors.
-/


@[expose] public section

namespace Complexity

namespace BooleanDependency

/-- Restrict a total Boolean assignment to a finite set of coordinates. -/
def restrict {coordinate : Type*} (coordinates : Finset coordinate)
    (input : coordinate → Bool) : coordinates → Bool :=
  fun index => input index

/-- Extend an assignment on selected coordinates by `false` everywhere else. -/
def extendByFalse {coordinate : Type*} [DecidableEq coordinate]
    (coordinates : Finset coordinate) (input : coordinates → Bool) :
    coordinate → Bool :=
  fun index => if hindex : index ∈ coordinates then input ⟨index, hindex⟩ else false

/-- The canonical table obtained by evaluating a function on extensions of all
assignments to a selected finite coordinate set. -/
def table {coordinate result : Type*} [DecidableEq coordinate]
    (coordinates : Finset coordinate) (function : (coordinate → Bool) → result) :
    (coordinates → Bool) → result :=
  fun input => function (extendByFalse coordinates input)

end BooleanDependency

end Complexity
