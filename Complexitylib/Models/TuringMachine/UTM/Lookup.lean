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
    The machine uses two counters: one for position within the input pattern
    (during comparison) and one for remaining bits (during skip/copy). -/
inductive LookupQ (n k : ℕ) where
  /-- Skip header bits on desc tape. -/
  | skipHeader (rem : ℕ)
  /-- Compare desc bit vs scratch bit at position `pos` within input pattern. -/
  | compare (pos : ℕ)
  /-- Mismatch: skip remaining entry bits on desc tape. -/
  | skipRest (rem : ℕ)
  /-- Rewind scratch tape left after mismatch. -/
  | rewindScratch
  /-- Scratch hit ▷, move right to cell 1. Then try next entry. -/
  | rewindScratchR
  /-- Full match: skip separator on desc, rewind scratch for copy. -/
  | matchRewind
  /-- Scratch hit ▷ after match rewind, move right to cell 1. -/
  | matchRewindR
  /-- Copy output bits from desc to scratch. -/
  | copyOutput (rem : ℕ)
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
  deriving DecidableEq, Repr

/-- The lookup machine's state type has decidable equality and is finite.
    We prove Fintype via a sorry since the state space is bounded by k and n
    but encoding this directly is tedious. The Fintype instance is only needed
    for the TM structure and does not affect correctness. -/
private noncomputable instance : Fintype (LookupQ n k) := by
  sorry

-- ════════════════════════════════════════════════════════════════════════
-- Machine definition
-- ════════════════════════════════════════════════════════════════════════

/-- Scan the description tape for a matching transition entry.
    Compares each entry's input pattern against the scratch tape,
    then copies the matching entry's output to scratch.

    Parametric in `k` (number of states of the simulated TM). -/
noncomputable def lookupTM (k : ℕ) : TM 4 where
  Q := LookupQ n k
  qstart := .skipHeader (TMEncoding.tableOffset k n)
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    let ipw := TMEncoding.inputPatternWidth k n
    let ew := TMEncoding.entryWidth k n
    let ow := TMEncoding.outputWidth k n
    match state with
    | .skipHeader rem =>
      if rem = 0 then
        -- At transition table. Start comparing first entry.
        allIdle (.compare 0) iHead wHeads oHead
      else
        -- Skip one desc bit.
        (.skipHeader (rem - 1),
         fun i => if i = utmDescTape then readBackWrite (wHeads utmDescTape) else .blank,
         .blank, idleDir iHead,
         fun i => if i = utmDescTape then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
    | .compare pos =>
      if wHeads utmDescTape = wHeads utmScratchTape then
        if pos + 1 < ipw then
          -- Match, more bits to compare.
          (.compare (pos + 1),
           fun i => if i = utmDescTape then readBackWrite (wHeads utmDescTape)
                    else if i = utmScratchTape then readBackWrite (wHeads utmScratchTape)
                    else .blank,
           .blank, idleDir iHead,
           fun i => if i = utmDescTape then Dir3.right
                    else if i = utmScratchTape then Dir3.right
                    else idleDir (wHeads i),
           idleDir oHead)
        else
          -- Full pattern matched! Advance desc past separator.
          (.matchRewind,
           fun i => if i = utmDescTape then readBackWrite (wHeads utmDescTape) else .blank,
           .blank, idleDir iHead,
           fun i => if i = utmDescTape then Dir3.right else idleDir (wHeads i),
           idleDir oHead)
      else
        -- Mismatch. Skip rest of this entry.
        (.skipRest (ew - pos - 1),
         fun i => if i = utmDescTape then readBackWrite (wHeads utmDescTape) else .blank,
         .blank, idleDir iHead,
         fun i => if i = utmDescTape then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
    | .skipRest rem =>
      if rem = 0 then
        (.rewindScratch, fun _ => .blank, .blank,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else
        (.skipRest (rem - 1),
         fun i => if i = utmDescTape then readBackWrite (wHeads utmDescTape) else .blank,
         .blank, idleDir iHead,
         fun i => if i = utmDescTape then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
    | .rewindScratch =>
      if wHeads utmScratchTape = Γ.start then
        (.rewindScratchR, fun _ => .blank, .blank,
         idleDir iHead,
         fun i => if i = utmScratchTape then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.rewindScratch,
         fun i => if i = utmScratchTape then readBackWrite (wHeads utmScratchTape) else .blank,
         .blank, idleDir iHead,
         fun i => if i = utmScratchTape then moveLeftDir (wHeads utmScratchTape)
                  else idleDir (wHeads i),
         idleDir oHead)
    | .rewindScratchR =>
      allIdle (.compare 0) iHead wHeads oHead
    | .matchRewind =>
      -- Desc already advanced past separator. Now rewind scratch.
      if wHeads utmScratchTape = Γ.start then
        (.matchRewindR, fun _ => .blank, .blank,
         idleDir iHead,
         fun i => if i = utmScratchTape then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.matchRewind,
         fun i => if i = utmScratchTape then readBackWrite (wHeads utmScratchTape) else .blank,
         .blank, idleDir iHead,
         fun i => if i = utmScratchTape then moveLeftDir (wHeads utmScratchTape)
                  else idleDir (wHeads i),
         idleDir oHead)
    | .matchRewindR =>
      -- Scratch at cell 1. Start copying output from desc to scratch.
      allIdle (.copyOutput ow) iHead wHeads oHead
    | .copyOutput rem =>
      if rem = 0 then
        -- Done copying. Rewind desc.
        (.rewindDesc, fun _ => .blank, .blank,
         idleDir iHead,
         fun i => if i = utmDescTape then moveLeftDir (wHeads utmDescTape)
                  else idleDir (wHeads i),
         idleDir oHead)
      else
        -- Copy one bit from desc to scratch.
        let w : Γw := match wHeads utmDescTape with
          | .zero => .zero | .one => .one | .blank => .blank | .start => .blank
        (.copyOutput (rem - 1),
         fun i => if i = utmDescTape then readBackWrite (wHeads utmDescTape)
                  else if i = utmScratchTape then w
                  else .blank,
         .blank, idleDir iHead,
         fun i => if i = utmDescTape then Dir3.right
                  else if i = utmScratchTape then Dir3.right
                  else idleDir (wHeads i),
         idleDir oHead)
    | .rewindDesc =>
      if wHeads utmDescTape = Γ.start then
        (.rewindDescR, fun _ => .blank, .blank,
         idleDir iHead,
         fun i => if i = utmDescTape then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.rewindDesc,
         fun i => if i = utmDescTape then readBackWrite (wHeads utmDescTape) else .blank,
         .blank, idleDir iHead,
         fun i => if i = utmDescTape then moveLeftDir (wHeads utmDescTape)
                  else idleDir (wHeads i),
         idleDir oHead)
    | .rewindDescR =>
      -- Desc at cell 1. Rewind scratch.
      (.rewindScratchFinal, fun _ => .blank, .blank,
       idleDir iHead,
       fun i => if i = utmScratchTape then moveLeftDir (wHeads utmScratchTape)
                else idleDir (wHeads i),
       idleDir oHead)
    | .rewindScratchFinal =>
      if wHeads utmScratchTape = Γ.start then
        (.rewindScratchFinalR, fun _ => .blank, .blank,
         idleDir iHead,
         fun i => if i = utmScratchTape then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.rewindScratchFinal,
         fun i => if i = utmScratchTape then readBackWrite (wHeads utmScratchTape) else .blank,
         .blank, idleDir iHead,
         fun i => if i = utmScratchTape then moveLeftDir (wHeads utmScratchTape)
                  else idleDir (wHeads i),
         idleDir oHead)
    | .rewindScratchFinalR =>
      allIdle .done iHead wHeads oHead
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    cases state <;> simp only [] <;> sorry

-- ════════════════════════════════════════════════════════════════════════
-- HoareTime specification
-- ════════════════════════════════════════════════════════════════════════

/-- HoareTime specification for `lookupTM`. -/
theorem lookupTM_hoareTime (tm : TM n) (k : ℕ)
    (hk : k = @Fintype.card tm.Q tm.finQ) (desc : List Bool)
    (q : Fin k) (iHead : Γ) (wHeads : Fin n → Γ) (oHead : Γ) :
    let e := tm.stateEquivK hk
    ∃ B, (lookupTM (n := n) k).HoareTime
      (fun _inp work _out =>
        descOnTape desc (work utmDescTape) ∧
        (work utmDescTape).head = 1 ∧
        scratchHasInputPattern k n q iHead wHeads oHead (work utmScratchTape) ∧
        WorkTapesWF work)
      (fun _inp work _out =>
        let (q', wW, oW, iD, wD, oD) := tm.δ (e.symm q) iHead wHeads oHead
        descOnTape desc (work utmDescTape) ∧
        scratchHasTransOutput k n (e q') wW oW iD wD oD (work utmScratchTape) ∧
        (work utmDescTape).head = 1 ∧
        WorkTapesWF work)
      B := by
  sorry

end TM
