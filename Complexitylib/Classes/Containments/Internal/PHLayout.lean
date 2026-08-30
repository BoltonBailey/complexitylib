/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.PHParts
public import Complexitylib.Models.TuringMachine.Combinators.Apply
public import Complexitylib.Models.TuringMachine.Subroutines.CopyToVirtualInput
public import Complexitylib.Models.TuringMachine.Subroutines.WipeRewind
public import Complexitylib.Models.TuringMachine.Subroutines.ParkRewind
public import Complexitylib.Models.TuringMachine.Placement

/-!
# The witness enumerator's tape layout

⚠️ Unreviewed by Bolton

Two placements fix where every tape sits, and they have to agree. The pair emitter is
`TM.pairInputWorkTM` on one work tape — the copy of the real input — wrapped so that it reads the
witness as a virtual input and writes onto a work tape; those wrappers append their tapes, so the
witness lands at index one and the emitted pair at index two. The matrix machine is `TM.applyTM`
placed by `TM.placeWorkTM 3 _`, which puts its own `k` scratch tapes at `3 … k + 2`, the input it
reads at `k + 3`, and the verdict it writes at `k + 4`.

The emitted pair and the input the matrix machine reads are therefore *different* tapes — the two
placements cannot be made to share one — and `TM.copyToVirtualInputTM` moves the pair from the
first to the second, which is exactly the shape `TM.retargetInputStartedCfg` demands anyway.

Seven registers follow: the counter, the horizon it is compared against, scratch for that
comparison, the two tallies the counting loop's state carries, a permanently blank tape to blank
slots from, and the unary register that drives the wipe.

## Main results

- `PolyExists.enumTapes` — the tape count, and the named indices into it
- `PolyExists.enumIdx_distinct` — the indices are pairwise distinct
- `PolyExists.matrixTapes` — the matrix machine's own scratch tapes
- `PolyExists.scratchTargets`, `PolyExists.scratchTargets_nodup` — the tapes the body blanks on
  its way out
-/

@[expose] public section

namespace Complexity

namespace PolyExists

variable {k : ℕ}

/-- The enumerator's tape count: three for the emitter, the matrix machine's `k + 2`, and six
registers. -/
abbrev enumTapes (k : ℕ) : ℕ := 3 + (k + 2) + 7

/-- The copy of the real input, which the emitter reads as the pair's first component. -/
def xIdx (k : ℕ) : Fin (enumTapes k) := ⟨0, by show 0 < 3 + (k + 2) + 7; omega⟩

/-- The witness, which the emitter reads as the pair's second component. -/
def wIdx (k : ℕ) : Fin (enumTapes k) := ⟨1, by show 1 < 3 + (k + 2) + 7; omega⟩

/-- The tape the emitter writes the pair onto. -/
def y1Idx (k : ℕ) : Fin (enumTapes k) := ⟨2, by show 2 < 3 + (k + 2) + 7; omega⟩

/-- The tape the matrix machine reads its input from. -/
def yIdx (k : ℕ) : Fin (enumTapes k) := ⟨3 + k, by show 3 + k < 3 + (k + 2) + 7; omega⟩

/-- The tape the matrix machine's verdict is redirected to. -/
def vIdx (k : ℕ) : Fin (enumTapes k) := ⟨3 + k + 1, by show 3 + k + 1 < 3 + (k + 2) + 7; omega⟩

/-- The counter, whose value denotes the witness. -/
def cIdx (k : ℕ) : Fin (enumTapes k) := ⟨3 + k + 2, by show 3 + k + 2 < 3 + (k + 2) + 7; omega⟩

/-- The horizon the counter is compared against. -/
def nIdx (k : ℕ) : Fin (enumTapes k) := ⟨3 + k + 3, by show 3 + k + 3 < 3 + (k + 2) + 7; omega⟩

/-- Scratch space for that comparison. -/
def resIdx (k : ℕ) : Fin (enumTapes k) :=
  ⟨3 + k + 4, by show 3 + k + 4 < 3 + (k + 2) + 7; omega⟩

/-- The latched answer: `1` once some witness has been accepted. -/
def aIdx (k : ℕ) : Fin (enumTapes k) := ⟨3 + k + 5, by show 3 + k + 5 < 3 + (k + 2) + 7; omega⟩

/-- A permanently blank tape, read whenever a slot must be blanked. -/
def zIdx (k : ℕ) : Fin (enumTapes k) := ⟨3 + k + 6, by show 3 + k + 6 < 3 + (k + 2) + 7; omega⟩

/-- The unary register that drives the wipe. -/
def regIdx (k : ℕ) : Fin (enumTapes k) :=
  ⟨3 + k + 7, by show 3 + k + 7 < 3 + (k + 2) + 7; omega⟩

/-- The count of witnesses that failed, which the counting loop's state carries alongside the
count of those that succeeded. -/
def rIdx (k : ℕ) : Fin (enumTapes k) :=
  ⟨3 + k + 8, by show 3 + k + 8 < 3 + (k + 2) + 7; omega⟩

/-- The matrix machine's own scratch tapes: the block `TM.placeWorkTM 3 _` puts them in. -/
def matrixTapes (k : ℕ) : List (Fin (enumTapes k)) :=
  (List.finRange (enumTapes k)).filter (fun j => decide (3 ≤ j.val ∧ j.val < 3 + k))

@[simp] theorem mem_matrixTapes_iff (k : ℕ) (j : Fin (enumTapes k)) :
    j ∈ matrixTapes k ↔ (3 ≤ j.val ∧ j.val < 3 + k) := by
  simp [matrixTapes, List.mem_filter]

theorem matrixTapes_nodup (k : ℕ) : (matrixTapes k).Nodup :=
  (List.nodup_finRange _).filter _

/-- The tapes one pass of the body leaves dirty, and must blank before the next: the emitted
pair, the matrix machine's scratch and its two placed tapes, and the verdict slot. -/
def scratchTargets (k : ℕ) : List (Fin (enumTapes k)) :=
  y1Idx k :: matrixTapes k ++ [yIdx k, vIdx k]

/-- The scratch block has no repeats, which the wipe requires of its targets. -/
theorem scratchTargets_nodup (k : ℕ) : (scratchTargets k).Nodup := by
  have hy : yIdx k ∉ matrixTapes k := by
    intro h
    have := ((mem_matrixTapes_iff k _).mp h).2
    simp only [yIdx] at this
    omega
  have hv : vIdx k ∉ matrixTapes k := by
    intro h
    have := ((mem_matrixTapes_iff k _).mp h).2
    simp only [vIdx] at this
    omega
  have hyv : yIdx k ≠ vIdx k := fun h => by
    have h' := congrArg Fin.val h
    simp only [yIdx, vIdx] at h'
    omega
  have h1 : y1Idx k ∉ matrixTapes k := by
    intro h
    have := ((mem_matrixTapes_iff k _).mp h).1
    simp only [y1Idx] at this
    omega
  refine List.nodup_cons.mpr ⟨?_, List.nodup_append.mpr ⟨matrixTapes_nodup k, ?_, ?_⟩⟩
  · intro hmem
    rcases List.mem_append.mp hmem with h | h
    · exact h1 h
    · rcases List.mem_cons.mp h with h | h
      · have h' := congrArg Fin.val h
        simp only [y1Idx, yIdx] at h'
        omega
      · rcases List.mem_cons.mp h with h | h
        · have h' := congrArg Fin.val h
          simp only [y1Idx, vIdx] at h'
          omega
        · exact absurd h (List.not_mem_nil)
  · refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · simpa using hyv
    · exact List.nodup_singleton _
  · intro a ha b hb hab
    rcases List.mem_cons.mp hb with h | h
    · exact hy (h ▸ hab ▸ ha)
    · rcases List.mem_cons.mp h with h | h
      · exact hv (h ▸ hab ▸ ha)
      · exact absurd h (List.not_mem_nil)

/-- Every tape the body wipes lies in the block between the emitter's target and the verdict
tape — which is exactly the part of the layout that rests blank. -/
theorem scratchTargets_val (k : ℕ) (j : Fin (enumTapes k)) (h : j ∈ scratchTargets k) :
    2 ≤ j.val ∧ j.val < 3 + k + 2 := by
  rw [scratchTargets] at h
  rcases List.mem_cons.mp h with h | h
  · rw [h]
    exact ⟨by show (2 : ℕ) ≤ 2; omega, by show (2 : ℕ) < 3 + k + 2; omega⟩
  · rcases List.mem_append.mp h with h | h
    · have := (mem_matrixTapes_iff k j).mp h
      omega
    · rcases List.mem_cons.mp h with h | h
      · rw [h]
        exact ⟨by show (2 : ℕ) ≤ 3 + k; omega, by show 3 + k < 3 + k + 2; omega⟩
      · rcases List.mem_cons.mp h with h | h
        · rw [h]
          exact ⟨by show (2 : ℕ) ≤ 3 + k + 1; omega, by show 3 + k + 1 < 3 + k + 2; omega⟩
        · exact absurd h (List.not_mem_nil)


/-- **The named indices are pairwise distinct.** Every frame lemma the assembly uses asks for
some of these disequalities; this states all of them at once. -/
theorem enumIdx_distinct (k : ℕ) :
    xIdx k ≠ wIdx k ∧ xIdx k ≠ y1Idx k ∧ xIdx k ≠ yIdx k ∧ xIdx k ≠ vIdx k ∧
    xIdx k ≠ cIdx k ∧ xIdx k ≠ nIdx k ∧ xIdx k ≠ resIdx k ∧ xIdx k ≠ aIdx k ∧
    xIdx k ≠ zIdx k ∧ xIdx k ≠ regIdx k ∧
    wIdx k ≠ y1Idx k ∧ wIdx k ≠ yIdx k ∧ wIdx k ≠ vIdx k ∧ wIdx k ≠ cIdx k ∧
    wIdx k ≠ nIdx k ∧ wIdx k ≠ resIdx k ∧ wIdx k ≠ aIdx k ∧ wIdx k ≠ zIdx k ∧
    wIdx k ≠ regIdx k ∧
    y1Idx k ≠ yIdx k ∧ y1Idx k ≠ vIdx k ∧ y1Idx k ≠ cIdx k ∧ y1Idx k ≠ nIdx k ∧
    y1Idx k ≠ resIdx k ∧ y1Idx k ≠ aIdx k ∧ y1Idx k ≠ zIdx k ∧ y1Idx k ≠ regIdx k ∧
    yIdx k ≠ vIdx k ∧ yIdx k ≠ cIdx k ∧ yIdx k ≠ nIdx k ∧ yIdx k ≠ resIdx k ∧
    yIdx k ≠ aIdx k ∧ yIdx k ≠ zIdx k ∧ yIdx k ≠ regIdx k ∧
    vIdx k ≠ cIdx k ∧ vIdx k ≠ nIdx k ∧ vIdx k ≠ resIdx k ∧ vIdx k ≠ aIdx k ∧
    vIdx k ≠ zIdx k ∧ vIdx k ≠ regIdx k ∧
    cIdx k ≠ nIdx k ∧ cIdx k ≠ resIdx k ∧ cIdx k ≠ aIdx k ∧ cIdx k ≠ zIdx k ∧
    cIdx k ≠ regIdx k ∧
    nIdx k ≠ resIdx k ∧ nIdx k ≠ aIdx k ∧ nIdx k ≠ zIdx k ∧ nIdx k ≠ regIdx k ∧
    resIdx k ≠ aIdx k ∧ resIdx k ≠ zIdx k ∧ resIdx k ≠ regIdx k ∧
    aIdx k ≠ zIdx k ∧ aIdx k ≠ regIdx k ∧
    zIdx k ≠ regIdx k ∧
    xIdx k ≠ rIdx k ∧ wIdx k ≠ rIdx k ∧ y1Idx k ≠ rIdx k ∧ yIdx k ≠ rIdx k ∧
    vIdx k ≠ rIdx k ∧ cIdx k ≠ rIdx k ∧ nIdx k ≠ rIdx k ∧ resIdx k ≠ rIdx k ∧
    aIdx k ≠ rIdx k ∧ zIdx k ≠ rIdx k ∧ regIdx k ≠ rIdx k := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩ <;>
    exact fun h => by
      have h' := congrArg Fin.val h
      simp only [xIdx, wIdx, y1Idx, yIdx, vIdx, cIdx, nIdx, resIdx, aIdx, zIdx, regIdx,
        rIdx] at h'
      omega

/-- The registers and the input copy are outside the scratch block, so the wipe leaves them
alone. -/
theorem not_mem_scratchTargets (k : ℕ) :
    xIdx k ∉ scratchTargets k ∧ wIdx k ∉ scratchTargets k ∧ cIdx k ∉ scratchTargets k ∧
    nIdx k ∉ scratchTargets k ∧ resIdx k ∉ scratchTargets k ∧ aIdx k ∉ scratchTargets k ∧
    zIdx k ∉ scratchTargets k ∧ regIdx k ∉ scratchTargets k ∧ rIdx k ∉ scratchTargets k := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp +decide [scratchTargets, xIdx, wIdx, cIdx, nIdx, resIdx, aIdx, zIdx, regIdx, rIdx,
      y1Idx, yIdx, vIdx, Fin.ext_iff] <;> omega

end PolyExists

end Complexity
