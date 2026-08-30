/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.AverageCase.FiniteEnsemble.Defs
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.BooleanAlgebra

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

/-- Merge Boolean assignments on a finite coordinate set and its complement. -/
def mergeAssignments {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate]
    (coordinates : Finset coordinate)
    (assignments : (coordinates → Bool) ×
      ((coordinatesᶜ : Finset coordinate) → Bool)) : coordinate → Bool :=
  fun index =>
    if hindex : index ∈ coordinates then
      assignments.1 ⟨index, hindex⟩
    else
      assignments.2 ⟨index, by simpa using hindex⟩

/-- A total Boolean assignment is equivalently its restrictions to a finite
coordinate set and its complement. -/
def assignmentSplitEquiv {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate]
    (coordinates : Finset coordinate) :
    (coordinate → Bool) ≃
      (coordinates → Bool) ×
        ((coordinatesᶜ : Finset coordinate) → Bool) where
  toFun input :=
    (restrict coordinates input, restrict coordinatesᶜ input)
  invFun := mergeAssignments coordinates
  left_inv input := by
    funext index
    by_cases hindex : index ∈ coordinates
    · simp [mergeAssignments, restrict, hindex]
    · simp [mergeAssignments, restrict, hindex]
  right_inv assignments := by
    apply Prod.ext <;> funext index
    · simp [mergeAssignments, restrict, index.property]
    · have hindex : index.val ∉ coordinates := by
        exact Finset.mem_compl.mp index.property
      simp [mergeAssignments, restrict, hindex]

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
