import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.UTM.Defs
import Complexitylib.Models.TuringMachine.UTM.Helpers
import Complexitylib.Models.TuringMachine.UTM.SimConfig.Defs
import Complexitylib.Models.TuringMachine.Hoare.Defs

/-!
# UTM Halt Check

Checks whether the simulated TM has reached its halt state by comparing
the state tape's one-hot encoding against the qhalt one-hot stored in the
description header.

## Architecture

```
utmCheckHaltTM = seqTM skipToQhaltTM
                   (seqTM compareWriteTM
                     (seqTM (rewindWorkTM 0) (rewindWorkTM 1)))
```

## Main results

- `utmCheckHaltTM` — the halt-check machine (concrete, not a placeholder)
- `checkHaltTM_hoareTime` — HoareTime spec
-/

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Phase 1: Skip description header to reach qhalt one-hot
-- ════════════════════════════════════════════════════════════════════════

/-- States for the header-skip machine. -/
inductive SkipHeaderPhase where
  | skipK  -- scanning right past k ones (state count)
  | skipN  -- scanning right past n ones (work tape count)
  | done
  deriving DecidableEq

instance : Fintype SkipHeaderPhase where
  elems := {.skipK, .skipN, .done}
  complete := fun x => by cases x <;> simp

/-- Skip the description tape header to reach the qhalt one-hot.
    Starting at cell 1, scans right past k ones + separator + n ones + separator.
    Halts with desc head at the first cell of the qhalt one-hot encoding. -/
def skipToQhaltTM : TM 4 where
  Q := SkipHeaderPhase
  qstart := .skipK
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .skipK =>
      if wHeads 0 = Γ.one then
        -- Still scanning k ones, advance desc right
        (.skipK,
         fun i => readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => if i.val = 0 then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        -- Hit separator after k ones, advance right past it, enter skipN
        (.skipN,
         fun i => readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => if i.val = 0 then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
    | .skipN =>
      if wHeads 0 = Γ.one then
        -- Still scanning n ones, advance desc right
        (.skipN,
         fun i => readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => if i.val = 0 then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        -- Hit separator after n ones, advance right past it, halt
        -- After this step, desc head is at first cell of qhalt one-hot
        (.done,
         fun i => readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => if i.val = 0 then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .skipK | .skipN =>
      dsimp only []; split <;> (
        refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rfl
        · exact idleDir_right_of_start hwi)
    | .done =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
             idleDir_right_of_start⟩

-- ════════════════════════════════════════════════════════════════════════
-- Phase 2: Compare state tape against qhalt and write result to output
-- ════════════════════════════════════════════════════════════════════════

/-- States for the compare-and-write machine. -/
inductive CompareWritePhase where
  | compare     -- comparing desc (qhalt one-hot) vs state tape cell by cell
  | rewindOutM  -- rewinding output tape left (matched, will write 1)
  | rewindOutD  -- rewinding output tape left (differed, will write 0)
  | writeM      -- at output cell 1, write Γ.one and halt
  | writeD      -- at output cell 1, write Γ.zero and halt
  | done
  deriving DecidableEq

instance : Fintype CompareWritePhase where
  elems := {.compare, .rewindOutM, .rewindOutD, .writeM, .writeD, .done}
  complete := fun x => by cases x <;> simp

/-- Compare the qhalt one-hot (desc tape) against the current state (state tape).
    Both tapes advance right in parallel. The state tape's Γ.blank sentinel at
    cell k+1 signals the end of comparison.

    After comparison, rewinds the output tape and writes Γ.one (match) or
    Γ.zero (mismatch) to output cell 1. -/
def compareWriteTM : TM 4 where
  Q := CompareWritePhase
  qstart := .compare
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .compare =>
      if wHeads 1 = Γ.blank then
        -- State tape sentinel: past all k cells, all matched → write 1
        (.rewindOutM, fun i => readBackWrite (wHeads i), .blank, idleDir iHead,
         fun i => idleDir (wHeads i), idleDir oHead)
      else if wHeads 0 = wHeads 1 then
        -- Cells match → advance both desc (0) and state (1) right
        (.compare,
         fun i => readBackWrite (wHeads i),
         .blank, idleDir iHead,
         fun i => if i.val = 0 then Dir3.right
                  else if i.val = 1 then Dir3.right
                  else idleDir (wHeads i),
         idleDir oHead)
      else
        -- Cells differ → mismatch → write 0
        (.rewindOutD, fun i => readBackWrite (wHeads i), .blank, idleDir iHead,
         fun i => idleDir (wHeads i), idleDir oHead)
    | .rewindOutM =>
      if oHead = Γ.start then
        -- At output ▷ (cell 0) → move right to cell 1, enter writeM
        (.writeM, fun i => readBackWrite (wHeads i), .blank, idleDir iHead,
         fun i => idleDir (wHeads i), Dir3.right)
      else
        -- Keep moving output left, preserving cells
        (.rewindOutM, fun i => readBackWrite (wHeads i), readBackWrite oHead, idleDir iHead,
         fun i => idleDir (wHeads i), Dir3.left)
    | .rewindOutD =>
      if oHead = Γ.start then
        (.writeD, fun i => readBackWrite (wHeads i), .blank, idleDir iHead,
         fun i => idleDir (wHeads i), Dir3.right)
      else
        (.rewindOutD, fun i => readBackWrite (wHeads i), readBackWrite oHead, idleDir iHead,
         fun i => idleDir (wHeads i), Dir3.left)
    | .writeM =>
      -- Write Γ.one to output cell 1 and halt
      (.done, fun i => readBackWrite (wHeads i), .one, idleDir iHead,
       fun i => idleDir (wHeads i), idleDir oHead)
    | .writeD =>
      -- Write Γ.zero to output cell 1 and halt
      (.done, fun i => readBackWrite (wHeads i), .zero, idleDir iHead,
       fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .compare =>
      dsimp only []
      split
      · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
      · split
        · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
          intro i hwi; simp only []; split
          · rfl
          · split
            · rfl
            · exact idleDir_right_of_start hwi
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
                 idleDir_right_of_start⟩
    | .rewindOutM | .rewindOutD =>
      dsimp only []; split
      · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, fun _ => rfl⟩
      · refine ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, ?_⟩
        intro h; next hn => exact absurd h hn
    | .writeM | .writeD =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
             idleDir_right_of_start⟩
    | .done =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
             idleDir_right_of_start⟩

-- ════════════════════════════════════════════════════════════════════════
-- Full check-halt machine: composed from phases + rewinds
-- ════════════════════════════════════════════════════════════════════════

/-- The halt-check machine. Composed as:
    1. `skipToQhaltTM` — navigate desc tape to qhalt one-hot
    2. `compareWriteTM` — compare against state tape, write result
    3. `rewindWorkTM 0` — rewind desc tape to cell 1
    4. `rewindWorkTM 1` — rewind state tape to cell 1 -/
def utmCheckHaltTM : TM 4 :=
  seqTM skipToQhaltTM
    (seqTM compareWriteTM
      (seqTM (rewindWorkTM (0 : Fin 4)) (rewindWorkTM (1 : Fin 4))))

-- ════════════════════════════════════════════════════════════════════════
-- HoareTime specification — proved in CheckHaltInternal.lean
-- ════════════════════════════════════════════════════════════════════════

end TM
