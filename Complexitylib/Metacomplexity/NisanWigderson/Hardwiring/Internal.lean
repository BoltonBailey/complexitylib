/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Hardwiring.Defs
import Complexitylib.Metacomplexity.BooleanDependency.Internal
import Complexitylib.Metacomplexity.NisanWigderson.Internal

/-!
# Nisan--Wigderson overlap hardwiring -- proof internals
-/


public section

namespace Complexity

namespace NWDesign

theorem map_challengeOverlap_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength) :
    (design.challengeOverlap current previous).map
        (design.coordinates current) =
      design.support current ∩ design.support previous := by
  ext coordinate
  simp [challengeOverlap, support]
  aesop

theorem card_challengeOverlap_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength) :
    (design.challengeOverlap current previous).card =
      design.overlap current previous := by
  rw [overlap, ← map_challengeOverlap_internal design current previous]
  simp

theorem seedWithChallenge_apply_coordinates_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) (outside : Fin seedLength → Bool)
    (challenge : Fin inputLength → Bool) (input : Fin inputLength) :
    design.seedWithChallenge current outside challenge
        (design.coordinates current input) =
      challenge input := by
  simp [seedWithChallenge]

theorem seedWithChallenge_apply_of_not_mem_support_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) (outside : Fin seedLength → Bool)
    (challenge : Fin inputLength → Bool) (coordinate : Fin seedLength)
    (hcoordinate : coordinate ∉ design.support current) :
    design.seedWithChallenge current outside challenge coordinate =
      outside coordinate := by
  have hnotrange : coordinate ∉ Set.range (design.coordinates current) := by
    simpa [support] using hcoordinate
  simp [seedWithChallenge, hnotrange]

theorem challengedBlock_current_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) (outside : Fin seedLength → Bool)
    (challenge : Fin inputLength → Bool) :
    design.challengedBlock current current outside challenge = challenge := by
  funext input
  exact seedWithChallenge_apply_coordinates_internal
    design current outside challenge input

theorem challengedBlock_dependsOn_overlap_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength)
    (outside : Fin seedLength → Bool) :
    DependsOn (design.challengedBlock current previous outside)
      (design.challengeOverlap current previous : Set (Fin inputLength)) := by
  intro first second hagree
  funext input
  by_cases hcoordinate :
      design.coordinates previous input ∈
        Set.range (design.coordinates current)
  · simp only [challengedBlock, restrictSeed, seedWithChallenge,
      hcoordinate, dite_true]
    apply hagree
    have hsame :
        design.coordinates current
            ((design.coordinates current).toEquivRange.symm
              ⟨design.coordinates previous input, hcoordinate⟩) =
          design.coordinates previous input := by
      exact congrArg Subtype.val
        ((design.coordinates current).toEquivRange.apply_symm_apply
          ⟨design.coordinates previous input, hcoordinate⟩)
    have hmember :
        design.coordinates current
            ((design.coordinates current).toEquivRange.symm
              ⟨design.coordinates previous input, hcoordinate⟩) ∈
          design.support previous := by
      rw [hsame]
      simp [support]
    simpa [challengeOverlap] using hmember
  · simp [challengedBlock, restrictSeed, seedWithChallenge, hcoordinate]

theorem challengedValue_dependsOn_overlap_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength)
    (outside : Fin seedLength → Bool)
    (observe : (Fin inputLength → Bool) → Bool) :
    DependsOn
      (fun challenge =>
        observe (design.challengedBlock current previous outside challenge))
      (design.challengeOverlap current previous : Set (Fin inputLength)) := by
  intro first second hagree
  apply congrArg observe
  exact challengedBlock_dependsOn_overlap_internal
    design current previous outside hagree

theorem predecessorTable_restrict_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength)
    (outside : Fin seedLength → Bool)
    (observe : (Fin inputLength → Bool) → Bool)
    (challenge : Fin inputLength → Bool) :
    design.predecessorTable current previous outside observe
        (BooleanDependency.restrict
          (design.challengeOverlap current previous) challenge) =
      observe (design.challengedBlock current previous outside challenge) := by
  exact BooleanDependency.table_restrict_internal
    (design.challengeOverlap current previous)
    (fun candidate =>
      observe (design.challengedBlock current previous outside candidate))
    (challengedValue_dependsOn_overlap_internal
      design current previous outside observe)
    challenge

theorem card_predecessorAssignments_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength) :
    Fintype.card (design.challengeOverlap current previous → Bool) =
      2 ^ design.overlap current previous := by
  rw [← Nat.card_eq_fintype_card,
    BooleanDependency.card_assignments_internal,
    card_challengeOverlap_internal]

theorem predecessorTableEntriesAt_eq_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    design.predecessorTableEntriesAt current =
      ∑ previous ∈ Finset.Iio current,
        2 ^ design.overlap current previous := by
  simp [predecessorTableEntriesAt, card_challengeOverlap_internal]

theorem overlapCostAt_eq_predecessorTableEntriesAt_add_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    design.overlapCostAt current =
      design.predecessorTableEntriesAt current +
        (outputLength - (current.val + 1)) := by
  rw [overlapCostAt, predecessorTableEntriesAt_eq_internal]

theorem predecessorTableEntriesAt_le_overlapCostAt_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    design.predecessorTableEntriesAt current ≤
      design.overlapCostAt current := by
  rw [overlapCostAt_eq_predecessorTableEntriesAt_add_internal]
  exact Nat.le_add_right _ _

theorem predecessorTableEntriesAt_le_of_hasOverlapBudget_internal
    {outputLength inputLength seedLength budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (hbudget : design.HasOverlapBudget budget)
    (current : Fin outputLength) :
    design.predecessorTableEntriesAt current ≤ budget :=
  (predecessorTableEntriesAt_le_overlapCostAt_internal design current).trans
    (hbudget current)

end NWDesign

end Complexity
