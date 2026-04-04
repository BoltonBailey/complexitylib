import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.UTM.Defs
import Complexitylib.Models.TuringMachine.UTM.Helpers
import Complexitylib.Models.TuringMachine.UTM.SimConfig.Defs
import Complexitylib.Models.TuringMachine.Hoare.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

/-!
# UTM Apply Transition

Applies the decoded transition to the simulated state and tapes:
1. Overwrite the state tape with the new one-hot encoding from scratch
2. Write new symbols on the sim tape for each work/output tape
3. Move head markers on the sim tape for each simulated tape
4. Clear scratch tape and rewind all work tape heads to cell 1

## Architecture

**Phase 0** — Copy new state one-hot from scratch tape to state tape (k steps).

**Phase 1 (write symbols)** — For each work tape (0..n−1) then the output tape,
read 2 bits from scratch (the write-symbol encoding), scan the sim tape for
that tape's head marker, and overwrite the symbol cells at the head position.

**Phase 2 (move heads)** — For each simulated tape (input, work 0..n−1, output),
read 2 bits from scratch (the direction encoding), scan the sim tape for
the head marker, clear it, move by one super-cell width, and set the new marker.

**Phase 3** — Clear the scratch tape (left scan writing blanks) and rewind all
four work tape heads to cell 1.

## Main results

- `applyTransitionTM` — the machine definition (parametric in `k`)
- `applyTransitionTM_hoareTime` — HoareTime spec: advances SimInvariant by one step
-/

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- Decode / encode helpers
-- ════════════════════════════════════════════════════════════════════════

/-- Decode two scratch-tape cells (bool pair encoded as Γ) to a Γw. -/
def decodeΓw (hi lo : Γ) : Γw :=
  match hi, lo with | .zero, .zero => .zero | .zero, .one => .one | _, _ => .blank

/-- Decode two scratch-tape cells to a Dir3. -/
def decodeDir3 (hi lo : Γ) : Dir3 :=
  match hi, lo with | .zero, .zero => .left | .zero, .one => .right | _, _ => .stay

/-- High cell of the super-cell encoding of a Γw write symbol.
    Matches `SuperCell.symToCellPair (w.toΓ)` projected to the first component. -/
def symToSimHi (w : Γw) : Γw :=
  match w with | .zero => .zero | .one => .zero | .blank => .blank

/-- Low cell of the super-cell encoding. -/
def symToSimLo (w : Γw) : Γw :=
  match w with | .zero => .zero | .one => .one | .blank => .blank

-- ════════════════════════════════════════════════════════════════════════
-- State type
-- ════════════════════════════════════════════════════════════════════════

/-- States for the apply-transition machine.  See module docstring for phase descriptions. -/
inductive ApplyTransQ (n k : ℕ) where
  -- Phase 0
  | writeState (rem : Fin (k + 1))
  -- Phase 1: write new symbols to sim tape (n+1 operations)
  | rdWrHi (wrIdx : Fin (n + 1))
  | rdWrLo (wrIdx : Fin (n + 1)) (hi : Γ)
  | scanWr (wrIdx : Fin (n + 1)) (pos : Fin (3 * (n + 2))) (sHi sLo : Γw) (wrapped : Bool)
  | wrHi (wrIdx : Fin (n + 1)) (sHi sLo : Γw)
  | wrLo (wrIdx : Fin (n + 1)) (sLo : Γw)
  | rwWr (wrIdx : Fin (n + 1))
  | rwWrR (wrIdx : Fin (n + 1))
  -- Phase 2: move head markers on sim tape (n+2 operations)
  | rdMvHi (mvIdx : Fin (n + 2))
  | rdMvLo (mvIdx : Fin (n + 2)) (hi : Γ)
  | scanMv (mvIdx : Fin (n + 2)) (pos : Fin (3 * (n + 2)))
      (dir : Dir3) (wrapped : Bool)
  | clearMk (mvIdx : Fin (n + 2)) (dir : Dir3) (posZero : Bool)
  | mvStep (mvIdx : Fin (n + 2)) (goRight : Bool) (rem : Fin (3 * (n + 2) + 1))
  | setMk (mvIdx : Fin (n + 2))
  | rwMv (mvIdx : Fin (n + 2))
  | rwMvR (mvIdx : Fin (n + 2))
  -- Phase 3: cleanup
  | clrScr
  | rwTp (t : Fin 4)
  | rwTpR (t : Fin 4)
  | done
  deriving DecidableEq

private instance : Fintype (ApplyTransQ n k) where
  elems :=
    {.clrScr, .done} ∪
    (Finset.univ.image fun r : Fin (k + 1) => ApplyTransQ.writeState r) ∪
    (Finset.univ.image fun i : Fin (n + 1) => ApplyTransQ.rdWrHi i) ∪
    (Finset.univ.image fun p : Fin (n + 1) × Γ => ApplyTransQ.rdWrLo p.1 p.2) ∪
    (Finset.univ.image fun p : Fin (n + 1) × Fin (3 * (n + 2)) × Γw × Γw × Bool =>
      ApplyTransQ.scanWr p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ∪
    (Finset.univ.image fun p : Fin (n + 1) × Γw × Γw =>
      ApplyTransQ.wrHi p.1 p.2.1 p.2.2) ∪
    (Finset.univ.image fun p : Fin (n + 1) × Γw =>
      ApplyTransQ.wrLo p.1 p.2) ∪
    (Finset.univ.image fun i : Fin (n + 1) => ApplyTransQ.rwWr i) ∪
    (Finset.univ.image fun i : Fin (n + 1) => ApplyTransQ.rwWrR i) ∪
    (Finset.univ.image fun i : Fin (n + 2) => ApplyTransQ.rdMvHi i) ∪
    (Finset.univ.image fun p : Fin (n + 2) × Γ => ApplyTransQ.rdMvLo p.1 p.2) ∪
    (Finset.univ.image fun p : Fin (n + 2) × Fin (3 * (n + 2)) × Dir3 × Bool =>
      ApplyTransQ.scanMv p.1 p.2.1 p.2.2.1 p.2.2.2) ∪
    (Finset.univ.image fun p : Fin (n + 2) × Dir3 × Bool =>
      ApplyTransQ.clearMk p.1 p.2.1 p.2.2) ∪
    (Finset.univ.image fun p : Fin (n + 2) × Bool × Fin (3 * (n + 2) + 1) =>
      ApplyTransQ.mvStep p.1 p.2.1 p.2.2) ∪
    (Finset.univ.image fun i : Fin (n + 2) => ApplyTransQ.setMk i) ∪
    (Finset.univ.image fun i : Fin (n + 2) => ApplyTransQ.rwMv i) ∪
    (Finset.univ.image fun i : Fin (n + 2) => ApplyTransQ.rwMvR i) ∪
    (Finset.univ.image fun t : Fin 4 => ApplyTransQ.rwTp t) ∪
    (Finset.univ.image fun t : Fin 4 => ApplyTransQ.rwTpR t)
  complete x := by
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]
    cases x with
    | writeState r =>                                                     -- 17L R
      left; left; left; left; left; left; left; left; left
      left; left; left; left; left; left; left; left
      right; exact ⟨r, rfl⟩
    | rdWrHi i =>                                                         -- 16L R
      left; left; left; left; left; left; left; left; left
      left; left; left; left; left; left; left
      right; exact ⟨i, rfl⟩
    | rdWrLo i g =>                                                       -- 15L R
      left; left; left; left; left; left; left; left; left
      left; left; left; left; left; left
      right; exact ⟨i, g, rfl⟩
    | scanWr i p h l w =>                                                  -- 14L R
      left; left; left; left; left; left; left; left; left
      left; left; left; left; left
      right; exact ⟨i, p, h, l, w, rfl⟩
    | wrHi i h l =>                                                       -- 13L R
      left; left; left; left; left; left; left; left; left
      left; left; left; left
      right; exact ⟨i, h, l, rfl⟩
    | wrLo i l =>                                                         -- 12L R
      left; left; left; left; left; left; left; left; left
      left; left; left
      right; exact ⟨i, l, rfl⟩
    | rwWr i =>                                                           -- 11L R
      left; left; left; left; left; left; left; left; left
      left; left
      right; exact ⟨i, rfl⟩
    | rwWrR i =>                                                          -- 10L R
      left; left; left; left; left; left; left; left; left
      left
      right; exact ⟨i, rfl⟩
    | rdMvHi i =>                                                         --  9L R
      left; left; left; left; left; left; left; left; left
      right; exact ⟨i, rfl⟩
    | rdMvLo i g =>                                                       --  8L R
      left; left; left; left; left; left; left; left
      right; exact ⟨i, g, rfl⟩
    | scanMv i p d w =>                                                   --  7L R
      left; left; left; left; left; left; left
      right; exact ⟨i, p, d, w, rfl⟩
    | clearMk i d z =>                                                    --  6L R
      left; left; left; left; left; left
      right; exact ⟨i, d, z, rfl⟩
    | mvStep i g r =>                                                     --  5L R
      left; left; left; left; left
      right; exact ⟨i, g, r, rfl⟩
    | setMk i =>                                                          --  4L R
      left; left; left; left
      right; exact ⟨i, rfl⟩
    | rwMv i =>                                                           --  3L R
      left; left; left
      right; exact ⟨i, rfl⟩
    | rwMvR i =>                                                          --  2L R
      left; left
      right; exact ⟨i, rfl⟩
    | rwTp t =>                                                           --  1L R
      left; right; exact ⟨t, rfl⟩
    | rwTpR t =>                                                          --  0L R
      right; exact ⟨t, rfl⟩
    | clrScr =>                                                           -- 18L L rfl
      left; left; left; left; left; left; left; left; left
      left; left; left; left; left; left; left; left; left
      left; rfl
    | done =>                                                             -- 18L R rfl
      left; left; left; left; left; left; left; left; left
      left; left; left; left; left; left; left; left; left
      right; rfl

-- ════════════════════════════════════════════════════════════════════════
-- Machine definition
-- ════════════════════════════════════════════════════════════════════════

-- Abbreviation for the super-cell width (3 cells per simulated tape).
private abbrev cellWidth (n : ℕ) : ℕ := 3 * (n + 2)

/-- Apply the decoded transition to the UTM's work tapes.
    Reads transition output from scratch.  Updates state tape (new one-hot)
    and sim tape (new symbols + moved head markers).

    Parametric in `k` (number of states of the simulated TM). -/
noncomputable def applyTransitionTM (k : ℕ) : TM 4 where
  Q := ApplyTransQ n k
  qstart := .writeState ⟨k, by omega⟩
  qhalt := .done
  δ := fun state iH wH oH =>
    match state with
    -- ── Phase 0: overwrite state tape with new one-hot from scratch ─────
    | .writeState rem =>
      if rem.val = 0 then
        -- Done.  Both state + scratch heads now at cell k+1.
        (.rdWrHi ⟨0, by omega⟩,
         fun i => readBackWrite (wH i), readBackWrite oH,
         idleDir iH, fun i => idleDir (wH i), idleDir oH)
      else
        -- Copy scratch bit → state tape, advance both right.
        (.writeState ⟨rem.val - 1, by omega⟩,
         fun i => if i = utmStateTape then readBackWrite (wH utmScratchTape)
                  else if i = utmScratchTape then readBackWrite (wH utmScratchTape)
                  else readBackWrite (wH i),
         readBackWrite oH, idleDir iH,
         fun i => if i = utmStateTape then Dir3.right
                  else if i = utmScratchTape then Dir3.right
                  else idleDir (wH i),
         idleDir oH)

    -- ── Phase 1: read write-symbol hi bit from scratch ──────────────────
    | .rdWrHi wrIdx =>
      (.rdWrLo wrIdx (wH utmScratchTape),
       fun i => readBackWrite (wH i), readBackWrite oH,
       idleDir iH,
       fun i => if i = utmScratchTape then Dir3.right else idleDir (wH i),
       idleDir oH)

    -- ── Phase 1: read write-symbol lo bit, decode, start sim scan ───────
    | .rdWrLo wrIdx hi =>
      let lo := wH utmScratchTape
      let sym := decodeΓw hi lo
      (.scanWr wrIdx ⟨0, by omega⟩ (symToSimHi sym) (symToSimLo sym) false,
       fun i => readBackWrite (wH i), readBackWrite oH,
       idleDir iH,
       fun i => if i = utmScratchTape then Dir3.right else idleDir (wH i),
       idleDir oH)

    -- ── Phase 1: scan sim tape for head marker ──────────────────────────
    | .scanWr wrIdx pos sHi sLo wrapped =>
      -- tapeIdx on the sim tape: work tape wrIdx → tapeIdx wrIdx+1, output → n+1
      let newWrapped := wrapped || (pos.val + 1 == 3 * (n + 2))
      if pos.val = 3 * (wrIdx.val + 1) then
        if wH utmSimTape = Γ.one then
          if wrapped then
            -- Head marker found at position > 0.  Advance sim to sym_hi cell.
            (.wrHi wrIdx sHi sLo,
             fun i => readBackWrite (wH i), readBackWrite oH,
             idleDir iH,
             fun i => if i = utmSimTape then Dir3.right else idleDir (wH i),
             idleDir oH)
          else
            -- Head marker found at position 0.  Skip write (Tape.write is
            -- no-op at cell 0, so the symbol is always ▷ — no need to update).
            (.rwWr wrIdx,
             fun i => readBackWrite (wH i), readBackWrite oH,
             idleDir iH, fun i => idleDir (wH i), idleDir oH)
        else
          (.scanWr wrIdx ⟨(pos.val + 1) % (3 * (n + 2)), Nat.mod_lt _ (by omega)⟩
            sHi sLo newWrapped,
           fun i => readBackWrite (wH i), readBackWrite oH,
           idleDir iH,
           fun i => if i = utmSimTape then Dir3.right else idleDir (wH i),
           idleDir oH)
      else
        (.scanWr wrIdx ⟨(pos.val + 1) % (3 * (n + 2)), Nat.mod_lt _ (by omega)⟩
          sHi sLo newWrapped,
         fun i => readBackWrite (wH i), readBackWrite oH,
         idleDir iH,
         fun i => if i = utmSimTape then Dir3.right else idleDir (wH i),
         idleDir oH)

    -- ── Phase 1: write sym_hi to sim tape ───────────────────────────────
    | .wrHi wrIdx sHi sLo =>
      (.wrLo wrIdx sLo,
       fun i => if i = utmSimTape then sHi else readBackWrite (wH i),
       readBackWrite oH, idleDir iH,
       fun i => if i = utmSimTape then Dir3.right else idleDir (wH i),
       idleDir oH)

    -- ── Phase 1: write sym_lo to sim tape ───────────────────────────────
    | .wrLo wrIdx sLo =>
      (.rwWr wrIdx,
       fun i => if i = utmSimTape then sLo else readBackWrite (wH i),
       readBackWrite oH, idleDir iH,
       fun i => idleDir (wH i), idleDir oH)

    -- ── Phase 1: rewind sim tape after write ────────────────────────────
    | .rwWr wrIdx =>
      if wH utmSimTape = Γ.start then
        (.rwWrR wrIdx,
         fun i => readBackWrite (wH i), readBackWrite oH,
         idleDir iH,
         fun i => if i = utmSimTape then Dir3.right else idleDir (wH i),
         idleDir oH)
      else
        (.rwWr wrIdx,
         fun i => readBackWrite (wH i), readBackWrite oH,
         idleDir iH,
         fun i => if i = utmSimTape then Dir3.left else idleDir (wH i),
         idleDir oH)

    -- ── Phase 1: sim at cell 1, next tape or phase 2 ───────────────────
    | .rwWrR wrIdx =>
      if h : wrIdx.val + 1 < n + 1 then
        (.rdWrHi ⟨wrIdx.val + 1, h⟩,
         fun i => readBackWrite (wH i), readBackWrite oH,
         idleDir iH, fun i => idleDir (wH i), idleDir oH)
      else
        (.rdMvHi ⟨0, by omega⟩,
         fun i => readBackWrite (wH i), readBackWrite oH,
         idleDir iH, fun i => idleDir (wH i), idleDir oH)

    -- ── Phase 2: read direction hi bit from scratch ─────────────────────
    | .rdMvHi mvIdx =>
      (.rdMvLo mvIdx (wH utmScratchTape),
       fun i => readBackWrite (wH i), readBackWrite oH,
       idleDir iH,
       fun i => if i = utmScratchTape then Dir3.right else idleDir (wH i),
       idleDir oH)

    -- ── Phase 2: read direction lo bit, decode, start sim scan ──────────
    | .rdMvLo mvIdx hi =>
      let lo := wH utmScratchTape
      let dir := decodeDir3 hi lo
      (.scanMv mvIdx ⟨0, by omega⟩ dir false,
       fun i => readBackWrite (wH i), readBackWrite oH,
       idleDir iH,
       fun i => if i = utmScratchTape then Dir3.right else idleDir (wH i),
       idleDir oH)

    -- ── Phase 2: scan sim tape for head marker ──────────────────────────
    | .scanMv mvIdx pos dir wrapped =>
      let newWrapped := wrapped || (pos.val + 1 == 3 * (n + 2))
      if pos.val = 3 * mvIdx.val then
        if wH utmSimTape = Γ.one then
          -- Found head marker.  posZero iff we haven't wrapped yet.
          (.clearMk mvIdx dir (!wrapped),
           fun i => readBackWrite (wH i), readBackWrite oH,
           idleDir iH, fun i => idleDir (wH i), idleDir oH)
        else
          (.scanMv mvIdx ⟨(pos.val + 1) % (3 * (n + 2)), Nat.mod_lt _ (by omega)⟩
            dir newWrapped,
           fun i => readBackWrite (wH i), readBackWrite oH,
           idleDir iH,
           fun i => if i = utmSimTape then Dir3.right else idleDir (wH i),
           idleDir oH)
      else
        (.scanMv mvIdx ⟨(pos.val + 1) % (3 * (n + 2)), Nat.mod_lt _ (by omega)⟩
          dir newWrapped,
         fun i => readBackWrite (wH i), readBackWrite oH,
         idleDir iH,
         fun i => if i = utmSimTape then Dir3.right else idleDir (wH i),
         idleDir oH)

    -- ── Phase 2: decide whether to move the head marker ─────────────────
    | .clearMk mvIdx dir posZero =>
      if dir = Dir3.stay || (dir = Dir3.left && posZero) then
        -- No movement needed — head stays.  Go straight to rewind.
        (.rwMv mvIdx,
         fun i => readBackWrite (wH i), readBackWrite oH,
         idleDir iH, fun i => idleDir (wH i), idleDir oH)
      else
        -- Clear the old head marker, then start stepping.
        (.mvStep mvIdx (dir == Dir3.right) ⟨3 * (n + 2), by omega⟩,
         fun i => if i = utmSimTape then Γw.blank else readBackWrite (wH i),
         readBackWrite oH, idleDir iH,
         fun i => idleDir (wH i), idleDir oH)

    -- ── Phase 2: step toward new marker position ────────────────────────
    | .mvStep mvIdx goRight rem =>
      if rem.val = 0 then
        -- Arrived at target.
        (.setMk mvIdx,
         fun i => readBackWrite (wH i), readBackWrite oH,
         idleDir iH, fun i => idleDir (wH i), idleDir oH)
      else
        (.mvStep mvIdx goRight ⟨rem.val - 1, by omega⟩,
         fun i => readBackWrite (wH i), readBackWrite oH,
         idleDir iH,
         fun i => if i = utmSimTape then
                    (if goRight then Dir3.right
                     else if wH utmSimTape = Γ.start then Dir3.right
                     else Dir3.left)
                  else idleDir (wH i),
         idleDir oH)

    -- ── Phase 2: set new head marker ────────────────────────────────────
    | .setMk mvIdx =>
      (.rwMv mvIdx,
       fun i => if i = utmSimTape then Γw.one else readBackWrite (wH i),
       readBackWrite oH, idleDir iH,
       fun i => idleDir (wH i), idleDir oH)

    -- ── Phase 2: rewind sim tape ────────────────────────────────────────
    | .rwMv mvIdx =>
      if wH utmSimTape = Γ.start then
        (.rwMvR mvIdx,
         fun i => readBackWrite (wH i), readBackWrite oH,
         idleDir iH,
         fun i => if i = utmSimTape then Dir3.right else idleDir (wH i),
         idleDir oH)
      else
        (.rwMv mvIdx,
         fun i => readBackWrite (wH i), readBackWrite oH,
         idleDir iH,
         fun i => if i = utmSimTape then Dir3.left else idleDir (wH i),
         idleDir oH)

    -- ── Phase 2: sim at cell 1, next tape or phase 3 ───────────────────
    | .rwMvR mvIdx =>
      if h : mvIdx.val + 1 < n + 2 then
        (.rdMvHi ⟨mvIdx.val + 1, h⟩,
         fun i => readBackWrite (wH i), readBackWrite oH,
         idleDir iH, fun i => idleDir (wH i), idleDir oH)
      else
        (.clrScr,
         fun i => readBackWrite (wH i), readBackWrite oH,
         idleDir iH, fun i => idleDir (wH i), idleDir oH)

    -- ── Phase 3: clear scratch tape (move left writing blanks) ──────────
    | .clrScr =>
      if wH utmScratchTape = Γ.start then
        (.rwTp ⟨0, by omega⟩,
         fun i => readBackWrite (wH i), readBackWrite oH,
         idleDir iH,
         fun i => if i = utmScratchTape then Dir3.right else idleDir (wH i),
         idleDir oH)
      else
        (.clrScr,
         fun i => if i = utmScratchTape then Γw.blank else readBackWrite (wH i),
         readBackWrite oH, idleDir iH,
         fun i => if i = utmScratchTape then Dir3.left else idleDir (wH i),
         idleDir oH)

    -- ── Phase 3: rewind a specific work tape ────────────────────────────
    | .rwTp t =>
      if wH t = Γ.start then
        (.rwTpR t,
         fun i => readBackWrite (wH i), readBackWrite oH,
         idleDir iH,
         fun i => if i = t then Dir3.right else idleDir (wH i),
         idleDir oH)
      else
        (.rwTp t,
         fun i => readBackWrite (wH i), readBackWrite oH,
         idleDir iH,
         fun i => if i = t then Dir3.left else idleDir (wH i),
         idleDir oH)

    -- ── Phase 3: tape at cell 1, next tape or done ──────────────────────
    | .rwTpR t =>
      if h : t.val + 1 < 4 then
        (.rwTp ⟨t.val + 1, h⟩,
         fun i => readBackWrite (wH i), readBackWrite oH,
         idleDir iH, fun i => idleDir (wH i), idleDir oH)
      else
        (.done,
         fun i => readBackWrite (wH i), readBackWrite oH,
         idleDir iH, fun i => idleDir (wH i), idleDir oH)

    -- ── Halt ────────────────────────────────────────────────────────────
    | .done =>
      (.done,
       fun i => readBackWrite (wH i), readBackWrite oH,
       idleDir iH, fun i => idleDir (wH i), idleDir oH)

  δ_right_of_start := by
    intro state iH wH oH
    -- Common closers
    have hI := fun (h : iH = Γ.start) => idleDir_right_of_start h
    have hO := fun (h : oH = Γ.start) => idleDir_right_of_start h
    have hAll : ∀ i, wH i = Γ.start → idleDir (wH i) = Dir3.right :=
      fun i h => idleDir_right_of_start h
    -- Helper: one tape moves right, rest idle
    have hOneR : ∀ (t : Fin 4), ∀ i, wH i = Γ.start →
        (if i = t then Dir3.right else idleDir (wH i)) = Dir3.right :=
      fun _ i h => by split <;> [rfl; exact idleDir_right_of_start h]
    match state with
    | .writeState rem =>
      dsimp only []; split
      · exact ⟨hI, hAll, hO⟩
      · refine ⟨hI, ?_, hO⟩; intro i h; dsimp only []
        split <;> [rfl; split <;> [rfl; exact idleDir_right_of_start h]]
    | .rdWrHi _ | .rdWrLo _ _ | .rdMvHi _ | .rdMvLo _ _ =>
      dsimp only []; exact ⟨hI, hOneR utmScratchTape, hO⟩
    | .scanWr _ pos _ _ wrapped =>
      dsimp only []; split
      · split
        · split
          · exact ⟨hI, hOneR utmSimTape, hO⟩
          · exact ⟨hI, hAll, hO⟩
        · exact ⟨hI, hOneR utmSimTape, hO⟩
      · exact ⟨hI, hOneR utmSimTape, hO⟩
    | .wrHi _ _ _ =>
      exact ⟨hI, hOneR utmSimTape, hO⟩
    | .wrLo _ _ =>
      exact ⟨hI, hAll, hO⟩
    | .rwWr _ =>
      dsimp only []; split
      · exact ⟨hI, hOneR utmSimTape, hO⟩
      · next h => exact ⟨hI, fun i hi => by
          simp [idleDir, hi]; exact fun heq => h (heq ▸ hi), hO⟩
    | .rwMv _ =>
      dsimp only []; split
      · exact ⟨hI, hOneR utmSimTape, hO⟩
      · next h => exact ⟨hI, fun i hi => by
          simp [idleDir, hi]; exact fun heq => h (heq ▸ hi), hO⟩
    | .rwWrR _ | .rwMvR _ =>
      dsimp only []; split <;> exact ⟨hI, hAll, hO⟩
    | .scanMv _ pos _ _ =>
      dsimp only []; split
      · split
        · exact ⟨hI, hAll, hO⟩
        · exact ⟨hI, hOneR utmSimTape, hO⟩
      · exact ⟨hI, hOneR utmSimTape, hO⟩
    | .clearMk _ _ _ =>
      dsimp only []; split <;> exact ⟨hI, hAll, hO⟩
    | .mvStep _ goRight _ =>
      dsimp only []; split
      · exact ⟨hI, hAll, hO⟩
      · exact ⟨hI, fun i hi => by simp [idleDir, hi]; intro heq _; exact heq ▸ hi, hO⟩
    | .setMk _ =>
      exact ⟨hI, hAll, hO⟩
    | .clrScr =>
      dsimp only []; split
      · exact ⟨hI, hOneR utmScratchTape, hO⟩
      · next h => exact ⟨hI, fun i hi => by
          simp [idleDir, hi]; exact fun heq => h (heq ▸ hi), hO⟩
    | .rwTp t =>
      dsimp only []; split
      · exact ⟨hI, hOneR t, hO⟩
      · next h => exact ⟨hI, fun i hi => by
          simp [idleDir, hi]; exact fun heq => h (heq ▸ hi), hO⟩
    | .rwTpR _ =>
      dsimp only []; split <;> exact ⟨hI, hAll, hO⟩
    | .done =>
      exact ⟨hI, hAll, hO⟩

-- ════════════════════════════════════════════════════════════════════════
-- HoareTime specification
-- ════════════════════════════════════════════════════════════════════════

-- The HoareTime proof for `applyTransitionTM` lives in ApplyTransitionInternal.lean
-- as `TM.applyTransitionTM_hoareTime_proof`.  The circular import
-- (ApplyTransitionInternal imports ApplyTransition) prevents placing it here.
-- Downstream files should import ApplyTransitionInternal and use
-- `applyTransitionTM_hoareTime_proof` directly.

end TM
