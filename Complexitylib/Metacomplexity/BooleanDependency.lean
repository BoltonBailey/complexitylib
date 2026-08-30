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
range, and the corresponding range-cardinality bound.
-/


public section

namespace Complexity

namespace BooleanDependency

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
