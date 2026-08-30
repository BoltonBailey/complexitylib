/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Hardwiring.Defs
public import Complexitylib.Metacomplexity.NisanWigderson.Hardwiring.Internal

/-!
# Nisan--Wigderson overlap hardwiring

When one NW block is replaced by a challenge, each predecessor block depends on
only the challenge coordinates in their intersection. Its observed Boolean
value is therefore recoverable from a canonical table with exactly
`2^|S_i ∩ S_j|` entries. Summing these entry counts gives precisely the
predecessor term in the design's overlap cost.
-/


public section

namespace Complexity

namespace NWDesign

/-- Mapping overlap coordinates through the current block embedding produces
exactly the intersection of the two block supports. -/
theorem map_challengeOverlap
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength) :
    (design.challengeOverlap current previous).map
        (design.coordinates current) =
      design.support current ∩ design.support previous :=
  map_challengeOverlap_internal design current previous

/-- Challenge overlap has exactly the design's recorded intersection size. -/
@[simp] theorem card_challengeOverlap
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength) :
    (design.challengeOverlap current previous).card =
      design.overlap current previous :=
  card_challengeOverlap_internal design current previous

/-- Inserting a challenge makes the current block read exactly that challenge. -/
@[simp] theorem seedWithChallenge_apply_coordinates
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) (outside : Fin seedLength → Bool)
    (challenge : Fin inputLength → Bool) (input : Fin inputLength) :
    design.seedWithChallenge current outside challenge
        (design.coordinates current input) =
      challenge input :=
  seedWithChallenge_apply_coordinates_internal
    design current outside challenge input

/-- Challenge insertion leaves every coordinate outside the current support
unchanged. -/
theorem seedWithChallenge_apply_of_not_mem_support
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) (outside : Fin seedLength → Bool)
    (challenge : Fin inputLength → Bool) (coordinate : Fin seedLength)
    (hcoordinate : coordinate ∉ design.support current) :
    design.seedWithChallenge current outside challenge coordinate =
      outside coordinate :=
  seedWithChallenge_apply_of_not_mem_support_internal
    design current outside challenge coordinate hcoordinate

/-- The challenged current block is definitionally faithful to the challenge. -/
@[simp] theorem challengedBlock_current
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) (outside : Fin seedLength → Bool)
    (challenge : Fin inputLength → Bool) :
    design.challengedBlock current current outside challenge = challenge :=
  challengedBlock_current_internal design current outside challenge

/-- A predecessor block depends on the challenge only through the two blocks'
intersection coordinates. -/
theorem challengedBlock_dependsOn_overlap
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength)
    (outside : Fin seedLength → Bool) :
    DependsOn (design.challengedBlock current previous outside)
      (design.challengeOverlap current previous : Set (Fin inputLength)) :=
  challengedBlock_dependsOn_overlap_internal
    design current previous outside

/-- Any Boolean observation of a predecessor block has the same overlap-only
dependency. -/
theorem challengedValue_dependsOn_overlap
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength)
    (outside : Fin seedLength → Bool)
    (observe : (Fin inputLength → Bool) → Bool) :
    DependsOn
      (fun challenge =>
        observe (design.challengedBlock current previous outside challenge))
      (design.challengeOverlap current previous : Set (Fin inputLength)) :=
  challengedValue_dependsOn_overlap_internal
    design current previous outside observe

/-- Looking up the actual overlap restriction in the canonical predecessor
table recovers the observed predecessor value. -/
@[simp] theorem predecessorTable_restrict
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength)
    (outside : Fin seedLength → Bool)
    (observe : (Fin inputLength → Bool) → Bool)
    (challenge : Fin inputLength → Bool) :
    design.predecessorTable current previous outside observe
        (BooleanDependency.restrict
          (design.challengeOverlap current previous) challenge) =
      observe (design.challengedBlock current previous outside challenge) :=
  predecessorTable_restrict_internal
    design current previous outside observe challenge

/-- The assignment space indexing one predecessor table has exactly one entry
for every Boolean assignment to the intersection. -/
theorem card_predecessorAssignments
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength) :
    Fintype.card (design.challengeOverlap current previous → Bool) =
      2 ^ design.overlap current previous :=
  card_predecessorAssignments_internal design current previous

/-- Total predecessor-table entries equal the sum of the standard exponential
intersection costs. -/
theorem predecessorTableEntriesAt_eq
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    design.predecessorTableEntriesAt current =
      ∑ previous ∈ Finset.Iio current,
        2 ^ design.overlap current previous :=
  predecessorTableEntriesAt_eq_internal design current

/-- The exact design overlap cost is the predecessor-table cost plus one unit
for every later output coordinate. -/
theorem overlapCostAt_eq_predecessorTableEntriesAt_add
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    design.overlapCostAt current =
      design.predecessorTableEntriesAt current +
        (outputLength - (current.val + 1)) :=
  overlapCostAt_eq_predecessorTableEntriesAt_add_internal design current

/-- Predecessor tables fit within the exact overlap cost. -/
theorem predecessorTableEntriesAt_le_overlapCostAt
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    design.predecessorTableEntriesAt current ≤
      design.overlapCostAt current :=
  predecessorTableEntriesAt_le_overlapCostAt_internal design current

/-- A weak-design overlap budget bounds all predecessor hardwiring tables. -/
theorem predecessorTableEntriesAt_le_of_hasOverlapBudget
    {outputLength inputLength seedLength budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (hbudget : design.HasOverlapBudget budget)
    (current : Fin outputLength) :
    design.predecessorTableEntriesAt current ≤ budget :=
  predecessorTableEntriesAt_le_of_hasOverlapBudget_internal hbudget current

end NWDesign

end Complexity
