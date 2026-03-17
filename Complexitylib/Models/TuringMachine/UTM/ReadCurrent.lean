import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.UTM.Defs
import Complexitylib.Models.TuringMachine.UTM.Helpers
import Complexitylib.Models.TuringMachine.UTM.SimConfig.Defs
import Complexitylib.Models.TuringMachine.Hoare.Defs
import Mathlib.Data.Fintype.Prod

/-!
# UTM Read Current State and Symbols

Reads the current simulated state and head symbols from the UTM's work tapes
and serializes them to the scratch tape for lookup.

## Architecture

The machine operates in three phases:

1. **Copy state one-hot**: Scan state tape (work 1) right, copying each cell
   to scratch tape (work 3). Stop at the blank sentinel after k cells.

2. **Read head symbols**: For each simulated tape t (0 to n+1), scan the sim
   tape (work 2) to find tape t's head marker (Γ.one), read the 2 symbol
   cells, transcode from super-cell encoding to Γ.encode encoding, write
   2 bits to scratch, then rewind the sim tape back to cell 1.

3. **Final rewinds**: Rewind state tape and scratch tape to cell 1.

## Super-cell to Γ.encode transcoding

The sim tape uses `symToCellPair` encoding while the scratch tape needs
`Γ.encode` encoding (via `Γ.ofBool`). These differ for Γ.blank:
- `symToCellPair .blank = (blank, blank)` but `Γ.encode .blank = [true, false]`
  which maps to `(one, zero)` via `Γ.ofBool`.

## Main results

- `readCurrentTM` — the machine definition
- `readCurrentTM_hoareTime` — HoareTime spec: parametric in `simCfg`
-/

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- Transcoding helper
-- ════════════════════════════════════════════════════════════════════════

/-- Transcode a super-cell symbol pair (from `symToCellPair`) to the
    Γ.encode representation (as `Γw` values for writing to scratch).

    Valid pairs and their transcodings:
    - `(zero, zero)` → `(zero, zero)` (Γ.zero)
    - `(zero, one)`  → `(zero, one)`  (Γ.one)
    - `(blank, blank)` → `(one, zero)` (Γ.blank)
    - `(one, one)`   → `(one, one)`   (Γ.start)

    Invalid pairs default to `(blank, blank)`. -/
def transcodePair (simHi simLo : Γ) : Γw × Γw :=
  match simHi, simLo with
  | .zero, .zero   => (.zero, .zero)
  | .zero, .one    => (.zero, .one)
  | .blank, .blank => (.one, .zero)
  | .one, .one     => (.one, .one)
  | _, _           => (.blank, .blank)

-- ════════════════════════════════════════════════════════════════════════
-- State type
-- ════════════════════════════════════════════════════════════════════════

/-- States for the readCurrent machine.

    The machine processes the sim tape per-tape: for each simulated tape
    (indexed 0 to n+1), it scans the sim tape for that tape's head marker,
    reads the symbol cells, transcodes, writes to scratch, then rewinds
    the sim tape. A position counter `Fin (3*(n+2))` tracks location within
    each super-cell during the scan. -/
inductive ReadCurrentQ (n : ℕ) where
  /-- Copy state tape one-hot to scratch tape. -/
  | copyState
  /-- Scan sim tape for `target`'s head marker.
      `pos` tracks position within the current super-cell (mod `3*(n+2)`).
      Head marker for tape `target` is at position `3 * target.val`. -/
  | scan (target : Fin (n + 2)) (pos : Fin (3 * (n + 2)))
  /-- Head marker found for `target`. Reading sym_hi cell. -/
  | readHi (target : Fin (n + 2))
  /-- Read sym_lo cell, remembering `simHi`. Will transcode and write
      first scratch bit. -/
  | readLoWrite (target : Fin (n + 2)) (simHi : Γ)
  /-- Write second scratch bit (`scrLo`). -/
  | writeLo (target : Fin (n + 2)) (scrLo : Γw)
  /-- Rewind sim tape leftward after reading `target`'s symbol. -/
  | rewindSim (target : Fin (n + 2))
  /-- Sim tape hit ▷, move right one step to cell 1. -/
  | rewindSimR (target : Fin (n + 2))
  /-- Rewind state tape leftward. -/
  | rewindState
  /-- State tape hit ▷, move right one step. -/
  | rewindStateR
  /-- Rewind scratch tape leftward. -/
  | rewindScratch
  /-- Scratch tape hit ▷, move right one step. -/
  | rewindScratchR
  /-- Halt state. -/
  | done
  deriving DecidableEq

instance : Fintype (ReadCurrentQ n) where
  elems :=
    {.copyState, .rewindState, .rewindStateR,
     .rewindScratch, .rewindScratchR, .done} ∪
    (Finset.univ.image fun (p : Fin (n + 2) × Fin (3 * (n + 2))) =>
      ReadCurrentQ.scan p.1 p.2) ∪
    (Finset.univ.image fun (t : Fin (n + 2)) => ReadCurrentQ.readHi t) ∪
    (Finset.univ.image fun (p : Fin (n + 2) × Γ) =>
      ReadCurrentQ.readLoWrite p.1 p.2) ∪
    (Finset.univ.image fun (p : Fin (n + 2) × Γw) =>
      ReadCurrentQ.writeLo p.1 p.2) ∪
    (Finset.univ.image fun (t : Fin (n + 2)) => ReadCurrentQ.rewindSim t) ∪
    (Finset.univ.image fun (t : Fin (n + 2)) => ReadCurrentQ.rewindSimR t)
  complete x := by
    cases x with
    | copyState => simp [Finset.mem_union, Finset.mem_insert]
    | scan t p =>
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]
      left; left; left; left; left; right; exact ⟨t, p, rfl⟩
    | readHi t =>
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      left; left; left; left; right; exact ⟨t, rfl⟩
    | readLoWrite t g =>
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
        Prod.exists]
      left; left; left; right; exact ⟨t, g, rfl⟩
    | writeLo t w =>
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
        Prod.exists]
      left; left; right; exact ⟨t, w, rfl⟩
    | rewindSim t =>
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      left; right; exact ⟨t, rfl⟩
    | rewindSimR t =>
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      right; exact ⟨t, rfl⟩
    | rewindState => simp [Finset.mem_union, Finset.mem_insert]
    | rewindStateR => simp [Finset.mem_union, Finset.mem_insert]
    | rewindScratch => simp [Finset.mem_union, Finset.mem_insert]
    | rewindScratchR => simp [Finset.mem_union, Finset.mem_insert]
    | done => simp [Finset.mem_union, Finset.mem_insert]

-- ════════════════════════════════════════════════════════════════════════
-- Machine definition
-- ════════════════════════════════════════════════════════════════════════

/-- Read the current simulated state and head symbols to the scratch tape.

    **Phase 1 (copyState)**: Copy state tape one-hot to scratch tape.
    State tape (work 1) and scratch tape (work 3) both start at cell 1.
    At each step, reads state tape; if not blank, copies the value to
    scratch and advances both right. On blank sentinel, enters phase 2.

    **Phase 2 (scan/read/rewind)**: For each simulated tape t (0 to n+1):
    - Scan sim tape (work 2) right from cell 1
    - Navigate super-cell structure: check head marker at position `3*t`
      within each super-cell
    - On finding head marker (Γ.one): read sym_hi, then sym_lo, transcode
      to Γ.encode representation, write 2 bits to scratch
    - Rewind sim tape back to cell 1
    - Proceed to next tape (or phase 3 if all tapes done)

    **Phase 3 (rewinds)**: Rewind state tape and scratch tape to cell 1.

    Preserves desc tape (work 0), state tape cells, and sim tape cells
    (read-only on all three). Only modifies scratch tape contents. -/
def readCurrentTM : TM 4 where
  Q := ReadCurrentQ n
  qstart := .copyState
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    -- ── Phase 1: Copy state one-hot ────────────────────────────────────
    | .copyState =>
      if wHeads 1 = Γ.blank then
        -- Sentinel reached: state one-hot fully copied.
        -- Enter phase 2: scan for tape 0's head marker.
        (.scan ⟨0, by omega⟩ ⟨0, by omega⟩,
         fun i => readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => idleDir (wHeads i),
         idleDir oHead)
      else
        -- Copy state tape cell to scratch tape, advance both right.
        (.copyState,
         fun i =>
           if i = (3 : Fin 4) then readBackWrite (wHeads 1)  -- copy from tape 1
           else readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i =>
           if i = (1 : Fin 4) then Dir3.right       -- advance state tape
           else if i = (3 : Fin 4) then Dir3.right  -- advance scratch tape
           else idleDir (wHeads i),
         idleDir oHead)

    -- ── Phase 2: Scan sim tape for head markers ───────────────────────
    | .scan target pos =>
      if pos.val = 3 * target.val then
        -- At tape `target`'s head marker position.
        if wHeads 2 = Γ.one then
          -- Head marker found! Advance sim to sym_hi cell.
          (.readHi target,
           fun i => readBackWrite (wHeads i),
           readBackWrite oHead, idleDir iHead,
           fun i => if i = (2 : Fin 4) then Dir3.right else idleDir (wHeads i),
           idleDir oHead)
        else
          -- Head not here. Advance sim right, increment position.
          (.scan target
            ⟨(pos.val + 1) % (3 * (n + 2)), Nat.mod_lt _ (by omega)⟩,
           fun i => readBackWrite (wHeads i),
           readBackWrite oHead, idleDir iHead,
           fun i => if i = (2 : Fin 4) then Dir3.right else idleDir (wHeads i),
           idleDir oHead)
      else
        -- Not at target's marker position. Advance sim right.
        (.scan target
          ⟨(pos.val + 1) % (3 * (n + 2)), Nat.mod_lt _ (by omega)⟩,
         fun i => readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => if i = (2 : Fin 4) then Dir3.right else idleDir (wHeads i),
         idleDir oHead)

    -- ── Phase 2: Read sym_hi ──────────────────────────────────────────
    | .readHi target =>
      -- Read sim tape cell (sym_hi), remember it, advance sim to sym_lo.
      (.readLoWrite target (wHeads 2),
       fun i => readBackWrite (wHeads i),
       readBackWrite oHead, idleDir iHead,
       fun i => if i = (2 : Fin 4) then Dir3.right else idleDir (wHeads i),
       idleDir oHead)

    -- ── Phase 2: Read sym_lo, transcode, write first scratch bit ──────
    | .readLoWrite target simHi =>
      let (scrHi, scrLo) := transcodePair simHi (wHeads 2)
      -- Write first encoded bit to scratch, advance scratch right.
      (.writeLo target scrLo,
       fun i =>
         if i = (3 : Fin 4) then scrHi  -- write to scratch
         else readBackWrite (wHeads i),
       readBackWrite oHead, idleDir iHead,
       fun i => if i = (3 : Fin 4) then Dir3.right else idleDir (wHeads i),
       idleDir oHead)

    -- ── Phase 2: Write second scratch bit ─────────────────────────────
    | .writeLo target scrLo =>
      -- Write second encoded bit to scratch, advance scratch right.
      -- Then rewind sim tape.
      (.rewindSim target,
       fun i =>
         if i = (3 : Fin 4) then scrLo  -- write to scratch
         else readBackWrite (wHeads i),
       readBackWrite oHead, idleDir iHead,
       fun i => if i = (3 : Fin 4) then Dir3.right else idleDir (wHeads i),
       idleDir oHead)

    -- ── Phase 2: Rewind sim tape ──────────────────────────────────────
    | .rewindSim target =>
      if wHeads 2 = Γ.start then
        -- Hit ▷ at cell 0. Move right to cell 1.
        (.rewindSimR target,
         fun i => readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => if i = (2 : Fin 4) then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        -- Keep moving sim left.
        (.rewindSim target,
         fun i => readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i =>
           if i = (2 : Fin 4) then Dir3.left else idleDir (wHeads i),
         idleDir oHead)

    -- ── Phase 2: Sim at cell 1, proceed to next tape ─────────────────
    | .rewindSimR target =>
      if h : target.val = n + 1 then
        -- All tapes processed. Enter phase 3: rewind state tape.
        (.rewindState,
         fun i => readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => idleDir (wHeads i),
         idleDir oHead)
      else
        -- More tapes to process. Start scanning for next tape.
        (.scan ⟨target.val + 1, by omega⟩ ⟨0, by omega⟩,
         fun i => readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => idleDir (wHeads i),
         idleDir oHead)

    -- ── Phase 3: Rewind state tape ────────────────────────────────────
    | .rewindState =>
      if wHeads 1 = Γ.start then
        (.rewindStateR,
         fun i => readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => if i = (1 : Fin 4) then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.rewindState,
         fun i => readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i =>
           if i = (1 : Fin 4) then Dir3.left else idleDir (wHeads i),
         idleDir oHead)

    | .rewindStateR =>
      -- State tape now at cell 1. Rewind scratch tape.
      (.rewindScratch,
       fun i => readBackWrite (wHeads i),
       readBackWrite oHead, idleDir iHead,
       fun i => idleDir (wHeads i),
       idleDir oHead)

    -- ── Phase 3: Rewind scratch tape ──────────────────────────────────
    | .rewindScratch =>
      if wHeads 3 = Γ.start then
        (.rewindScratchR,
         fun i => readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => if i = (3 : Fin 4) then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.rewindScratch,
         fun i => readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i =>
           if i = (3 : Fin 4) then Dir3.left else idleDir (wHeads i),
         idleDir oHead)

    | .rewindScratchR =>
      -- Scratch tape now at cell 1. Done!
      (.done,
       fun i => readBackWrite (wHeads i),
       readBackWrite oHead, idleDir iHead,
       fun i => idleDir (wHeads i),
       idleDir oHead)

    -- ── Halt state ────────────────────────────────────────────────────
    | .done => allIdle .done iHead wHeads oHead

  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .copyState =>
      dsimp only []; split
      · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; dsimp only []
        split
        · subst_eqs; rfl
        · split
          · subst_eqs; rfl
          · exact idleDir_right_of_start hwi
    | .scan _ _ =>
      dsimp only []; split
      · split <;> (
          refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
          intro i hwi; dsimp only []; split
          · subst_eqs; rfl
          · exact idleDir_right_of_start hwi)
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; dsimp only []; split
        · subst_eqs; rfl
        · exact idleDir_right_of_start hwi
    | .readHi _ =>
      refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
      intro i hwi; dsimp only []; split
      · subst_eqs; rfl
      · exact idleDir_right_of_start hwi
    | .readLoWrite _ _ =>
      dsimp only []
      refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
      intro i hwi; split
      · subst_eqs; rfl
      · exact idleDir_right_of_start hwi
    | .writeLo _ _ =>
      refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
      intro i hwi; dsimp only []; split
      · subst_eqs; rfl
      · exact idleDir_right_of_start hwi
    | .rewindSim _ =>
      dsimp only []; split
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; dsimp only []; split
        · subst_eqs; rfl
        · exact idleDir_right_of_start hwi
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; dsimp only []; split
        · subst_eqs; simp_all
        · exact idleDir_right_of_start hwi
    | .rewindSimR _ =>
      dsimp only []; split <;>
        exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
    | .rewindState =>
      dsimp only []; split
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; dsimp only []; split
        · subst_eqs; rfl
        · exact idleDir_right_of_start hwi
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; dsimp only []; split
        · subst_eqs; simp_all
        · exact idleDir_right_of_start hwi
    | .rewindStateR =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
             idleDir_right_of_start⟩
    | .rewindScratch =>
      dsimp only []; split
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; dsimp only []; split
        · subst_eqs; rfl
        · exact idleDir_right_of_start hwi
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; dsimp only []; split
        · subst_eqs; simp_all
        · exact idleDir_right_of_start hwi
    | .rewindScratchR =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
             idleDir_right_of_start⟩
    | .done =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
             idleDir_right_of_start⟩

end TM
