/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.BooleanDependency.Defs
public import Complexitylib.Metacomplexity.BooleanDependency.Internal

/-!
# Finite Boolean dependency tables

A function depending on a finite coordinate set can be represented by its
canonical table on assignments to that set. This module exposes exact
reconstruction, the `2^|S|` table-entry count, finiteness of the function's
range, and the corresponding range-cardinality bound. It also splits total
assignments bijectively across a coordinate set and its complement and proves
that uniform restriction is exactly uniform.
-/


public section

namespace Complexity

namespace BooleanDependency

/-- Splitting and then merging a total assignment recovers it exactly. -/
@[simp] theorem mergeAssignments_split {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate]
    (coordinates : Finset coordinate) (input : coordinate → Bool) :
    mergeAssignments coordinates
        (restrict coordinates input, restrict coordinatesᶜ input) = input :=
  (assignmentSplitEquiv coordinates).left_inv input

/-- Restricting a merged assignment to its selected coordinates recovers the
selected component. -/
@[simp] theorem restrict_mergeAssignments_left {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate]
    (coordinates : Finset coordinate)
    (selected : coordinates → Bool)
    (outside : (coordinatesᶜ : Finset coordinate) → Bool) :
    restrict coordinates (mergeAssignments coordinates (selected, outside)) =
      selected :=
  congrArg Prod.fst ((assignmentSplitEquiv coordinates).right_inv
    (selected, outside))

/-- Restricting a merged assignment to the complement recovers the complement
component. -/
@[simp] theorem restrict_mergeAssignments_right {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate]
    (coordinates : Finset coordinate)
    (selected : coordinates → Bool)
    (outside : (coordinatesᶜ : Finset coordinate) → Bool) :
    restrict coordinatesᶜ
        (mergeAssignments coordinates (selected, outside)) = outside :=
  congrArg Prod.snd ((assignmentSplitEquiv coordinates).right_inv
    (selected, outside))

/-- Restricting a uniformly random total Boolean assignment to any finite
coordinate subset produces the exact uniform distribution on subset
assignments. -/
theorem uniformProbability_restrict {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate]
    (coordinates : Finset coordinate)
    (event : (coordinates → Bool) → Prop) [DecidablePred event] :
    uniformProbability (Finset.univ.filter fun input : coordinate → Bool =>
        event (restrict coordinates input)) =
      uniformProbability (Finset.univ.filter event) :=
  uniformProbability_restrict_internal coordinates event

/-- Extending a restricted assignment recovers every selected coordinate. -/
@[simp] theorem extendByFalse_restrict_apply {coordinate : Type*}
    [DecidableEq coordinate] (coordinates : Finset coordinate)
    (input : coordinate → Bool) (index : coordinate)
    (hindex : index ∈ coordinates) :
    extendByFalse coordinates (restrict coordinates input) index = input index :=
  extendByFalse_restrict_apply_internal coordinates input index hindex

/-- If a function depends only on the selected coordinates, its canonical
table reconstructs its value on every total input. -/
@[simp] theorem table_restrict {coordinate result : Type*}
    [DecidableEq coordinate] (coordinates : Finset coordinate)
    (function : (coordinate → Bool) → result)
    (hdepends : DependsOn function (coordinates : Set coordinate))
    (input : coordinate → Bool) :
    table coordinates function (restrict coordinates input) = function input :=
  table_restrict_internal coordinates function hdepends input

/-- A table on `|S|` Boolean coordinates has exactly `2^|S|` entries. -/
theorem card_assignments {coordinate : Type*} (coordinates : Finset coordinate) :
    Nat.card (coordinates → Bool) = 2 ^ coordinates.card :=
  card_assignments_internal coordinates

/-- A function depending on finitely many Boolean coordinates has finite range. -/
theorem finite_range_of_dependsOn {coordinate result : Type*}
    [DecidableEq coordinate] (coordinates : Finset coordinate)
    (function : (coordinate → Bool) → result)
    (hdepends : DependsOn function (coordinates : Set coordinate)) :
    (Set.range function).Finite :=
  finite_range_of_dependsOn_internal coordinates function hdepends

/-- A function depending on `S` has at most `2^|S|` distinct values. -/
theorem card_range_le_pow_card_of_dependsOn
    {coordinate result : Type*} [DecidableEq coordinate]
    (coordinates : Finset coordinate)
    (function : (coordinate → Bool) → result)
    (hdepends : DependsOn function (coordinates : Set coordinate)) :
    Nat.card (Set.range function) ≤ 2 ^ coordinates.card :=
  card_range_le_pow_card_of_dependsOn_internal coordinates function hdepends

end BooleanDependency

end Complexity
