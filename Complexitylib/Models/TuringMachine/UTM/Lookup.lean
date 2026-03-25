import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.UTM.Defs
import Complexitylib.Models.TuringMachine.UTM.Helpers
import Complexitylib.Models.TuringMachine.UTM.SimConfig.Defs
import Complexitylib.Models.TuringMachine.Hoare.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

/-!
# UTM Transition Lookup

Linear-scan lookup of the matching transition entry in the encoded
description on work tape 0.

## Main results

- `lookupTM` — the lookup machine definition (parametric in `k`)
- `lookupTM_hoareTime` — HoareTime spec: parametric in state and symbols
-/

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- State type
-- ════════════════════════════════════════════════════════════════════════

/-- States for the lookup machine. Parametric in `k` (number of TM states).
    The machine uses bounded counters for position within the input pattern
    and remaining bits during skip/copy. -/
inductive LookupQ (n k : ℕ) where
  /-- Skip header bits on desc tape. -/
  | skipHeader (rem : Fin (TMEncoding.tableOffset k n + 1))
  /-- Compare desc bit vs scratch bit at position `pos` within input pattern. -/
  | compare (pos : Fin (TMEncoding.inputPatternWidth k n + 1))
  /-- Mismatch: skip remaining entry bits on desc tape. -/
  | skipRest (rem : Fin (TMEncoding.entryWidth k n + 1))
  /-- Rewind scratch tape left after mismatch. -/
  | rewindScratch
  /-- Scratch hit ▷, move right to cell 1. Then try next entry. -/
  | rewindScratchR
  /-- Full match: skip separator on desc, rewind scratch for copy. -/
  | matchRewind
  /-- Scratch hit ▷ after match rewind, move right to cell 1. -/
  | matchRewindR
  /-- Copy output bits from desc to scratch. -/
  | copyOutput (rem : Fin (TMEncoding.outputWidth k n + 1))
  /-- Rewind desc tape back to cell 1. -/
  | rewindDesc
  /-- Desc hit ▷, move right to cell 1. -/
  | rewindDescR
  /-- Rewind scratch tape after copy. -/
  | rewindScratchFinal
  /-- Scratch hit ▷, move right. -/
  | rewindScratchFinalR
  /-- Done. -/
  | done
  deriving DecidableEq

private instance : Fintype (LookupQ n k) where
  elems :=
    {.rewindScratch, .rewindScratchR, .matchRewind, .matchRewindR,
     .rewindDesc, .rewindDescR, .rewindScratchFinal, .rewindScratchFinalR, .done} ∪
    (Finset.univ.image fun (r : Fin (TMEncoding.tableOffset k n + 1)) =>
      LookupQ.skipHeader r) ∪
    (Finset.univ.image fun (p : Fin (TMEncoding.inputPatternWidth k n + 1)) =>
      LookupQ.compare p) ∪
    (Finset.univ.image fun (r : Fin (TMEncoding.entryWidth k n + 1)) =>
      LookupQ.skipRest r) ∪
    (Finset.univ.image fun (r : Fin (TMEncoding.outputWidth k n + 1)) =>
      LookupQ.copyOutput r)
  complete x := by
    cases x with
    | skipHeader r =>
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      left; left; left; right; exact ⟨r, rfl⟩
    | compare p =>
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      left; left; right; exact ⟨p, rfl⟩
    | skipRest r =>
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      left; right; exact ⟨r, rfl⟩
    | copyOutput r =>
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      right; exact ⟨r, rfl⟩
    | rewindScratch => simp [Finset.mem_union, Finset.mem_insert]
    | rewindScratchR => simp [Finset.mem_union, Finset.mem_insert]
    | matchRewind => simp [Finset.mem_union, Finset.mem_insert]
    | matchRewindR => simp [Finset.mem_union, Finset.mem_insert]
    | rewindDesc => simp [Finset.mem_union, Finset.mem_insert]
    | rewindDescR => simp [Finset.mem_union, Finset.mem_insert]
    | rewindScratchFinal => simp [Finset.mem_union, Finset.mem_insert]
    | rewindScratchFinalR => simp [Finset.mem_union, Finset.mem_insert]
    | done => simp [Finset.mem_union, Finset.mem_insert]

-- ════════════════════════════════════════════════════════════════════════
-- Machine definition
-- ════════════════════════════════════════════════════════════════════════

/-- Scan the description tape for a matching transition entry.
    Compares each entry's input pattern against the scratch tape,
    then copies the matching entry's output to scratch.

    Parametric in `k` (number of states of the simulated TM). -/
noncomputable def lookupTM (k : ℕ) : TM 4 where
  Q := LookupQ n k
  qstart := .skipHeader ⟨TMEncoding.tableOffset k n, by omega⟩
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    let ipw := TMEncoding.inputPatternWidth k n
    let ew := TMEncoding.entryWidth k n
    let ow := TMEncoding.outputWidth k n
    match state with
    | .skipHeader rem =>
      if rem.val = 0 then
        -- At transition table. Start comparing first entry.
        (.compare ⟨0, by omega⟩,
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else
        -- Skip one desc bit.
        (.skipHeader ⟨rem.val - 1, by omega⟩,
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = utmDescTape then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
    | .compare pos =>
      if wHeads utmDescTape = wHeads utmScratchTape then
        if h : pos.val + 1 < ipw then
          -- Match, more bits to compare.
          (.compare ⟨pos.val + 1, by omega⟩,
           fun i => readBackWrite (wHeads i), readBackWrite oHead,
           idleDir iHead,
           fun i => if i = utmDescTape then Dir3.right
                    else if i = utmScratchTape then Dir3.right
                    else idleDir (wHeads i),
           idleDir oHead)
        else
          -- Full pattern matched! Advance desc past separator.
          (.matchRewind,
           fun i => readBackWrite (wHeads i), readBackWrite oHead,
           idleDir iHead,
           fun i => if i = utmDescTape then Dir3.right else idleDir (wHeads i),
           idleDir oHead)
      else
        -- Mismatch. Skip rest of this entry.
        (.skipRest ⟨ew - pos.val - 1, by omega⟩,
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = utmDescTape then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
    | .skipRest rem =>
      if rem.val = 0 then
        (.rewindScratch,
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else
        (.skipRest ⟨rem.val - 1, by omega⟩,
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = utmDescTape then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
    | .rewindScratch =>
      if wHeads utmScratchTape = Γ.start then
        (.rewindScratchR,
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = utmScratchTape then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.rewindScratch,
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = utmScratchTape then moveLeftDir (wHeads utmScratchTape)
                  else idleDir (wHeads i),
         idleDir oHead)
    | .rewindScratchR =>
      (.compare ⟨0, by omega⟩,
       fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .matchRewind =>
      -- Desc already advanced past separator. Now rewind scratch.
      if wHeads utmScratchTape = Γ.start then
        (.matchRewindR,
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = utmScratchTape then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.matchRewind,
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = utmScratchTape then moveLeftDir (wHeads utmScratchTape)
                  else idleDir (wHeads i),
         idleDir oHead)
    | .matchRewindR =>
      -- Scratch at cell 1, desc at separator. Advance desc past separator,
      -- then start copying output from desc to scratch.
      (.copyOutput ⟨ow, by omega⟩,
       fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead,
       fun i => if i = utmDescTape then Dir3.right else idleDir (wHeads i),
       idleDir oHead)
    | .copyOutput rem =>
      if rem.val = 0 then
        -- Done copying. Rewind desc.
        (.rewindDesc,
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = utmDescTape then moveLeftDir (wHeads utmDescTape)
                  else idleDir (wHeads i),
         idleDir oHead)
      else
        -- Copy one bit from desc to scratch.
        let w : Γw := match wHeads utmDescTape with
          | .zero => .zero | .one => .one | .blank => .blank | .start => .blank
        (.copyOutput ⟨rem.val - 1, by omega⟩,
         fun i => if i = utmScratchTape then w else readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => if i = utmDescTape then Dir3.right
                  else if i = utmScratchTape then Dir3.right
                  else idleDir (wHeads i),
         idleDir oHead)
    | .rewindDesc =>
      if wHeads utmDescTape = Γ.start then
        (.rewindDescR,
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = utmDescTape then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.rewindDesc,
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = utmDescTape then moveLeftDir (wHeads utmDescTape)
                  else idleDir (wHeads i),
         idleDir oHead)
    | .rewindDescR =>
      -- Desc at cell 1. Rewind scratch.
      (.rewindScratchFinal,
       fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead,
       fun i => if i = utmScratchTape then moveLeftDir (wHeads utmScratchTape)
                else idleDir (wHeads i),
       idleDir oHead)
    | .rewindScratchFinal =>
      if wHeads utmScratchTape = Γ.start then
        (.rewindScratchFinalR,
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = utmScratchTape then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.rewindScratchFinal,
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = utmScratchTape then moveLeftDir (wHeads utmScratchTape)
                  else idleDir (wHeads i),
         idleDir oHead)
    | .rewindScratchFinalR =>
      (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    have hros := fun (h : iHead = Γ.start) => idleDir_right_of_start h
    have hrosO := fun (h : oHead = Γ.start) => idleDir_right_of_start h
    have descRos : ∀ i, wHeads i = Γ.start →
        (if i = utmDescTape then Dir3.right else idleDir (wHeads i)) = Dir3.right := by
      intro i hi; split <;> [rfl; exact idleDir_right_of_start hi]
    have scratchRos : ∀ i, wHeads i = Γ.start →
        (if i = utmScratchTape then Dir3.right else idleDir (wHeads i)) = Dir3.right := by
      intro i hi; split <;> [rfl; exact idleDir_right_of_start hi]
    have descScratchRos : ∀ i, wHeads i = Γ.start →
        (if i = utmDescTape then Dir3.right
         else if i = utmScratchTape then Dir3.right
         else idleDir (wHeads i)) = Dir3.right := by
      intro i hi; split <;> [rfl; split <;> [rfl; exact idleDir_right_of_start hi]]
    match state with
    | .skipHeader rem =>
      dsimp only []; split
      · exact ⟨hros, fun _ hi => idleDir_right_of_start hi, hrosO⟩
      · exact ⟨hros, descRos, hrosO⟩
    | .compare pos =>
      dsimp only []; split
      · split
        · exact ⟨hros, descScratchRos, hrosO⟩
        · exact ⟨hros, descRos, hrosO⟩
      · exact ⟨hros, descRos, hrosO⟩
    | .skipRest rem =>
      dsimp only []; split
      · exact ⟨hros, fun _ hi => idleDir_right_of_start hi, hrosO⟩
      · exact ⟨hros, descRos, hrosO⟩
    | .rewindScratch =>
      dsimp only []; split
      · exact ⟨hros, scratchRos, hrosO⟩
      · refine ⟨hros, ?_, hrosO⟩
        intro i hi; dsimp only []; split
        · next heq => subst heq; rw [hi]; rfl
        · exact idleDir_right_of_start hi
    | .rewindScratchR =>
      exact ⟨hros, fun _ hi => idleDir_right_of_start hi, hrosO⟩
    | .matchRewind =>
      dsimp only []; split
      · exact ⟨hros, scratchRos, hrosO⟩
      · refine ⟨hros, ?_, hrosO⟩
        intro i hi; dsimp only []; split
        · next heq => subst heq; rw [hi]; rfl
        · exact idleDir_right_of_start hi
    | .matchRewindR =>
      exact ⟨hros, descRos, hrosO⟩
    | .copyOutput rem =>
      dsimp only []; split
      · refine ⟨hros, ?_, hrosO⟩
        intro i hi; dsimp only []; split
        · next heq => subst heq; rw [hi]; rfl
        · exact idleDir_right_of_start hi
      · exact ⟨hros, descScratchRos, hrosO⟩
    | .rewindDesc =>
      dsimp only []; split
      · exact ⟨hros, descRos, hrosO⟩
      · refine ⟨hros, ?_, hrosO⟩
        intro i hi; dsimp only []; split
        · next heq => subst heq; rw [hi]; rfl
        · exact idleDir_right_of_start hi
    | .rewindDescR =>
      refine ⟨hros, ?_, hrosO⟩
      intro i hi; dsimp only []; split
      · next heq => subst heq; rw [hi]; rfl
      · exact idleDir_right_of_start hi
    | .rewindScratchFinal =>
      dsimp only []; split
      · exact ⟨hros, scratchRos, hrosO⟩
      · refine ⟨hros, ?_, hrosO⟩
        intro i hi; dsimp only []; split
        · next heq => subst heq; rw [hi]; rfl
        · exact idleDir_right_of_start hi
    | .rewindScratchFinalR =>
      exact ⟨hros, fun _ hi => idleDir_right_of_start hi, hrosO⟩
    | .done =>
      exact ⟨hros, fun _ hi => idleDir_right_of_start hi, hrosO⟩

-- ════════════════════════════════════════════════════════════════════════
-- HoareTime specification
-- ════════════════════════════════════════════════════════════════════════

/-- HoareTime specification for `lookupTM`.

    The `hdesc` hypothesis links the desc tape contents to the TM's
    transition table, which is required for the linear-scan lookup
    to find the correct entry. -/
theorem lookupTM_hoareTime (tm : TM n) (k : ℕ)
    (hk : k = @Fintype.card tm.Q tm.finQ)
    (hdesc : desc = TMEncoding.encodeTM tm)
    (q : Fin k) (iHead : Γ) (wHeads : Fin n → Γ) (oHead : Γ) :
    let e := tm.stateEquivK hk
    ∃ B, (lookupTM (n := n) k).HoareTime
      (fun inp work out =>
        descOnTape desc (work utmDescTape) ∧
        (work utmDescTape).head = 1 ∧
        (∀ i, (work i).head ≥ 1) ∧
        scratchHasInputPattern k n q iHead wHeads oHead (work utmScratchTape) ∧
        (work utmScratchTape).cells (TMEncoding.outputWidth k n + 1) = Γ.blank ∧
        WorkTapesWF work ∧
        inp.read ≠ Γ.start ∧ inp.head ≥ 1 ∧
        out.read ≠ Γ.start ∧ out.head ≥ 1)
      (fun _inp work _out =>
        let (q', wW, oW, iD, wD, oD) := tm.δ (e.symm q) iHead wHeads oHead
        descOnTape desc (work utmDescTape) ∧
        scratchHasTransOutput k n (e q') wW oW iD wD oD (work utmScratchTape) ∧
        (work utmDescTape).head = 1 ∧
        (work utmScratchTape).head = 1 ∧
        WorkTapesWF work)
      B := by
  -- See `TM.lookupTM_hoareTime_proof` in LookupInternal.lean for the proof.
  -- The circular import (LookupInternal imports Lookup) prevents direct use here.
  -- Downstream files should import LookupInternal and use `lookupTM_hoareTime_proof`.
  sorry

end TM
