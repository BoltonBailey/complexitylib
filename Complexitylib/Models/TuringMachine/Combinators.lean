import Complexitylib.Models.TuringMachine
import Mathlib.Data.Fintype.Sum

/-!
# TM Combinators

This file provides TM constructions for composing machines, used to prove
closure properties of complexity classes.

## Main definitions

- `TM.unionTM` — Given `tm₁ : TM n₁` deciding `L₁` and `tm₂ : TM n₂` deciding `L₂`,
  construct a `TM (n₁ + 1 + n₂)` that decides `L₁ ∪ L₂`.

## Design

The union machine has three phases:

1. **Phase 1**: Simulate `tm₁`, redirecting its output to work tape `n₁`
   (a "fake output" tape). The real output tape stays pristine.
2. **Transition**: Rewind the fake output to cell 1 and check the result.
   If `Γ.one` (tm₁ accepted), write `Γ.one` to the real output and halt.
   Otherwise rewind the input tape and reset Phase-2 tapes to cell 0.
3. **Phase 2**: Simulate `tm₂` using work tapes `n₁+1..n₁+n₂`
   and the real output tape.

### Work tape layout (0-indexed)

- `0 .. n₁-1` — Phase 1's work tapes (mirrors `tm₁.work`)
- `n₁` — Phase 1's redirected output (mirrors `tm₁.output`)
- `n₁+1 .. n₁+n₂` — Phase 2's work tapes (mirrors `tm₂.work`)

### State space

`Q₁ ⊕ Mid ⊕ Q₂` where `Mid` encodes the four transition states
between Phase 1 and Phase 2.
-/

variable {n₁ n₂ : ℕ}

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Helpers
-- ════════════════════════════════════════════════════════════════════════

/-- Direction for an idle tape: move right if reading `▷`, else stay.
    Satisfies `δ_right_of_start` for tapes not involved in the current phase. -/
def idleDir (head : Γ) : Dir3 :=
  if head = Γ.start then .right else .stay

/-- Direction for a tape we want to move left: move left unless reading `▷`,
    in which case move right to satisfy `δ_right_of_start`. During actual
    execution the tape won't be at cell 0, so this always moves left. -/
def moveLeftDir (head : Γ) : Dir3 :=
  if head = Γ.start then .right else .left

theorem idleDir_start : idleDir Γ.start = Dir3.right := rfl
private theorem moveLeftDir_start : moveLeftDir Γ.start = Dir3.right := rfl

theorem idleDir_right_of_start (h : head = Γ.start) : idleDir head = Dir3.right := by
  subst h; rfl

private theorem moveLeftDir_right_of_start (h : head = Γ.start) : moveLeftDir head = Dir3.right :=
  by subst h; rfl

/-- Write back the same symbol read from a tape, preserving cell contents.
    Maps `▷` to `□` since `Tape.write` at position 0 is a no-op anyway. -/
def readBackWrite (g : Γ) : Γw :=
  match g with
  | .zero => .zero
  | .one => .one
  | .blank => .blank
  | .start => .blank

/-- The "do nothing" transition output: all writes are `□`, all directions
    are `idleDir`. Used for states that only change the control state. -/
def allIdle {σ : Type} {k : ℕ}
    (newState : σ) (iHead : Γ) (wHeads : Fin k → Γ) (oHead : Γ) :
    σ × (Fin k → Γw) × Γw × Dir3 × (Fin k → Dir3) × Dir3 :=
  (newState, fun _ => .blank, .blank, idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)

/-- Proof that all-idle directions satisfy `δ_right_of_start`. -/
private def rightOfStart_allIdle (iHead : Γ) (wHeads : Fin k → Γ) (oHead : Γ) :
    (iHead = Γ.start → idleDir iHead = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → idleDir (wHeads i) = Dir3.right) ∧
    (oHead = Γ.start → idleDir oHead = Dir3.right) :=
  ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩

-- ════════════════════════════════════════════════════════════════════════
-- State type
-- ════════════════════════════════════════════════════════════════════════

/-- Intermediate states between Phase 1 and Phase 2 of the union machine. -/
inductive Mid where
  | rewindOut    -- rewind fake output (work tape n₁) to cell 0
  | checkResult  -- at fake output cell 1: read and decide accept/continue
  | rewindIn     -- rewind input tape to cell 0
  | setup2       -- move Phase-2 tapes from cell 1 to cell 0
  deriving DecidableEq

instance : Fintype Mid where
  elems := {.rewindOut, .checkResult, .rewindIn, .setup2}
  complete := fun x => by cases x <;> simp

/-- The state type for the union TM. -/
abbrev UnionQ (Q₁ Q₂ : Type) := Q₁ ⊕ Mid ⊕ Q₂

-- ════════════════════════════════════════════════════════════════════════
-- Index helpers for the n₁ + 1 + n₂ work tapes
-- ════════════════════════════════════════════════════════════════════════

/-- Index of the fake output tape (work tape `n₁`). -/
def fakeOutIdx : Fin (n₁ + 1 + n₂) := ⟨n₁, by omega⟩

/-- Read tm₁'s work tapes from the composite work tapes. -/
def phase1WorkReads (wHeads : Fin (n₁ + 1 + n₂) → Γ) (i : Fin n₁) : Γ :=
  wHeads ⟨i.val, by omega⟩

/-- Read tm₂'s work tapes from the composite work tapes. -/
def phase2WorkReads (wHeads : Fin (n₁ + 1 + n₂) → Γ) (j : Fin n₂) : Γ :=
  wHeads ⟨n₁ + 1 + j.val, by omega⟩

-- ════════════════════════════════════════════════════════════════════════
-- The union TM
-- ════════════════════════════════════════════════════════════════════════

/-- Construct a TM deciding `L₁ ∪ L₂` from TMs deciding `L₁` and `L₂`.

    The composite machine has `n₁ + 1 + n₂` work tapes:
    - `0 .. n₁-1` for `tm₁`'s work tapes
    - `n₁` for `tm₁`'s redirected output
    - `n₁+1 .. n₁+n₂` for `tm₂`'s work tapes -/
def unionTM (tm₁ : TM n₁) (tm₂ : TM n₂) : TM (n₁ + 1 + n₂) :=
  haveI : Fintype tm₁.Q := tm₁.finQ
  haveI : DecidableEq tm₁.Q := tm₁.decEq
  haveI : Fintype tm₂.Q := tm₂.finQ
  haveI : DecidableEq tm₂.Q := tm₂.decEq
  { Q := UnionQ tm₁.Q tm₂.Q,
    qstart := Sum.inl tm₁.qstart,
    qhalt := Sum.inr (Sum.inr tm₂.qhalt),
    δ := fun state iHead wHeads oHead =>
    match state with
    -- ══════════════════════════════════════════════════════════════════
    -- Phase 1: simulate tm₁ with output redirected to work tape n₁
    -- ══════════════════════════════════════════════════════════════════
    | Sum.inl q =>
      if q = tm₁.qhalt then
        -- Transition to rewind; preserve fake output value to avoid corrupting cell 1
        ( Sum.inr (Sum.inl .rewindOut),
          fun i => if i.val = n₁ then readBackWrite (wHeads fakeOutIdx) else .blank,
          .blank,
          idleDir iHead,
          fun i => idleDir (wHeads i),
          idleDir oHead )
      else
        let (q', wW, oW, iD, wD, oD) :=
          tm₁.δ q iHead (phase1WorkReads wHeads) (wHeads fakeOutIdx)
        ( Sum.inl q',
          fun i =>
            if h : i.val < n₁ then wW ⟨i.val, h⟩
            else if i.val = n₁ then oW
            else .blank,
          .blank, iD,
          fun i =>
            if h : i.val < n₁ then wD ⟨i.val, h⟩
            else if i.val = n₁ then oD
            else idleDir (wHeads i),
          idleDir oHead )
    -- ══════════════════════════════════════════════════════════════════
    -- Transition states between phases
    -- ══════════════════════════════════════════════════════════════════
    | Sum.inr (Sum.inl m) =>
      match m with
      | .rewindOut =>
        if wHeads fakeOutIdx = Γ.start then
          -- At cell 0 → move right to cell 1
          ( Sum.inr (Sum.inl .checkResult),
            fun _ => .blank, .blank, idleDir iHead,
            fun i => if i.val = n₁ then Dir3.right else idleDir (wHeads i),
            idleDir oHead )
        else
          -- Not at cell 0 → keep moving left; preserve fake output to avoid corrupting cell 1
          ( Sum.inr (Sum.inl .rewindOut),
            fun i => if i.val = n₁ then readBackWrite (wHeads fakeOutIdx) else .blank,
            .blank, idleDir iHead,
            fun i => if i.val = n₁ then Dir3.left else idleDir (wHeads i),
            idleDir oHead )
      | .checkResult =>
        if wHeads fakeOutIdx = Γ.one then
          -- tm₁ accepted → write Γ.one to real output (at cell 1), halt
          ( Sum.inr (Sum.inr tm₂.qhalt),
            fun _ => .blank, .one, idleDir iHead,
            fun i => idleDir (wHeads i),
            idleDir oHead )
        else
          -- tm₁ rejected → proceed to rewind input
          allIdle (Sum.inr (Sum.inl .rewindIn)) iHead wHeads oHead
      | .rewindIn =>
        if iHead = Γ.start then
          -- At cell 0 → forced right by δ_right_of_start, then setup2
          ( Sum.inr (Sum.inl .setup2),
            fun _ => .blank, .blank, Dir3.right,
            fun i => idleDir (wHeads i),
            idleDir oHead )
        else
          -- Not at cell 0 → keep moving left
          ( Sum.inr (Sum.inl .rewindIn),
            fun _ => .blank, .blank, Dir3.left,
            fun i => idleDir (wHeads i),
            idleDir oHead )
      | .setup2 =>
        -- Move input, Phase-2 work tapes, and real output from cell 1 to cell 0
        ( Sum.inr (Sum.inr tm₂.qstart),
          fun _ => .blank, .blank, moveLeftDir iHead,
          fun i => if i.val ≤ n₁ then idleDir (wHeads i) else moveLeftDir (wHeads i),
          moveLeftDir oHead )
    -- ══════════════════════════════════════════════════════════════════
    -- Phase 2: simulate tm₂ with the real output tape
    -- ══════════════════════════════════════════════════════════════════
    | Sum.inr (Sum.inr q) =>
      if q = tm₂.qhalt then
        -- Unreachable (step returns none), but δ is total
        allIdle (Sum.inr (Sum.inr tm₂.qhalt)) iHead wHeads oHead
      else
        let (q', wW, oW, iD, wD, oD) :=
          tm₂.δ q iHead (phase2WorkReads wHeads) oHead
        ( Sum.inr (Sum.inr q'),
          fun i =>
            if h : i.val ≤ n₁ then .blank
            else wW ⟨i.val - (n₁ + 1), by omega⟩,
          oW, iD,
          fun i =>
            if h : i.val ≤ n₁ then idleDir (wHeads i)
            else wD ⟨i.val - (n₁ + 1), by omega⟩,
          oD ),
    δ_right_of_start := by
      intro state iHead wHeads oHead
      match state with
      | Sum.inl q =>
        dsimp only []
        split
        · exact rightOfStart_allIdle iHead wHeads oHead
        · next hne =>
          have hδ := tm₁.δ_right_of_start q iHead (phase1WorkReads wHeads) (wHeads fakeOutIdx)
          simp only [phase1WorkReads, fakeOutIdx] at hδ
          refine ⟨hδ.1, ?_, idleDir_right_of_start⟩
          intro i hwi; simp only []
          split
          · next hi =>
            exact hδ.2.1 ⟨i.val, hi⟩ (by
              rwa [show wHeads ⟨↑i, by omega⟩ = wHeads i from by congr 1])
          · split
            · next hi hn =>
              exact hδ.2.2 (by
                rwa [show wHeads ⟨n₁, by omega⟩ = wHeads i from by congr 1; ext; simp [hn]])
            · exact idleDir_right_of_start hwi
      | Sum.inr (Sum.inl m) =>
        match m with
        | .rewindOut =>
          dsimp only [fakeOutIdx]
          split
          · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
            intro i hwi; simp only []; split
            · rfl
            · exact idleDir_right_of_start hwi
          · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
            intro i hwi; simp only []; split
            · next hn heq =>
              exfalso; apply hn
              rwa [show wHeads ⟨n₁, by omega⟩ = wHeads i from by congr 1; ext; simp [heq]]
            · exact idleDir_right_of_start hwi
        | .checkResult =>
          dsimp only [fakeOutIdx]
          split
          · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩
          · exact rightOfStart_allIdle iHead wHeads oHead
        | .rewindIn =>
          dsimp only []
          split
          · exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩
          · refine ⟨?_, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩
            intro hiHead; next hn => exact absurd hiHead hn
        | .setup2 =>
          refine ⟨moveLeftDir_right_of_start, ?_, moveLeftDir_right_of_start⟩
          intro i hwi; simp only []; split
          · exact idleDir_right_of_start hwi
          · exact moveLeftDir_right_of_start hwi
      | Sum.inr (Sum.inr q) =>
        dsimp only []
        split
        · exact rightOfStart_allIdle iHead wHeads oHead
        · next hne =>
          have hδ := tm₂.δ_right_of_start q iHead (phase2WorkReads wHeads) oHead
          simp only [phase2WorkReads] at hδ
          refine ⟨hδ.1, ?_, hδ.2.2⟩
          intro i hwi; simp only []; split
          · exact idleDir_right_of_start hwi
          · next hi =>
            exact hδ.2.1 ⟨i.val - (n₁ + 1), by omega⟩ (by
              rwa [show wHeads ⟨n₁ + 1 + (↑i - (n₁ + 1)), by omega⟩ = wHeads i from by
                congr 1; ext; simp; omega]) }

-- ════════════════════════════════════════════════════════════════════════
-- Complement TM
-- ════════════════════════════════════════════════════════════════════════

/-- Intermediate states for the complement machine's output-flipping phase. -/
inductive ComplementPhase where
  | rewind  -- rewind output head left to cell 0, then right to cell 1
  | flip    -- at cell 1: flip the output bit and halt
  | done    -- halt state
  deriving DecidableEq

instance : Fintype ComplementPhase where
  elems := {.rewind, .flip, .done}
  complete := fun x => by cases x <;> simp

/-- The state type for the complement TM. -/
abbrev ComplementQ (Q : Type) := Q ⊕ ComplementPhase

/-- Flip a readable symbol: `1 ↔ 0`, blanks stay blank. -/
def flipBit (g : Γ) : Γw :=
  match g with
  | .one => .zero
  | .zero => .one
  | .blank => .blank
  | .start => .blank

/-- Construct a TM deciding `Lᶜ` from a TM deciding `L`.

    The complement machine has the same number of work tapes as the original.
    It runs in three stages:

    1. **Simulate**: Run the original TM. When it halts, transition to `rewind`.
    2. **Rewind**: Move the output head left to `▷` (cell 0), then right to cell 1.
    3. **Flip**: Read output cell 1, write the flipped bit, and halt. -/
def complementTM (tm : TM n) : TM n :=
  haveI : Fintype tm.Q := tm.finQ
  haveI : DecidableEq tm.Q := tm.decEq
  { Q := ComplementQ tm.Q,
    qstart := Sum.inl tm.qstart,
    qhalt := Sum.inr .done,
    δ := fun state iHead wHeads oHead =>
    match state with
    -- ══════════════════════════════════════════════════════════════════
    -- Simulation phase: run original TM
    -- ══════════════════════════════════════════════════════════════════
    | Sum.inl q =>
      if q = tm.qhalt then
        -- Original TM halted → begin rewinding output
        -- Write back the current output symbol to preserve cell contents
        ( Sum.inr .rewind,
          fun _ => .blank,
          readBackWrite oHead,
          idleDir iHead,
          fun i => idleDir (wHeads i),
          idleDir oHead )
      else
        -- Not halted → run original δ, wrapping state in Sum.inl
        let (q', wW, oW, iD, wD, oD) := tm.δ q iHead wHeads oHead
        ( Sum.inl q', wW, oW, iD, wD, oD )
    -- ══════════════════════════════════════════════════════════════════
    -- Rewind phase: move output head left to ▷, then right to cell 1
    -- ══════════════════════════════════════════════════════════════════
    | Sum.inr .rewind =>
      if oHead = Γ.start then
        -- At cell 0 (▷) → move right to cell 1, enter flip state
        ( Sum.inr .flip,
          fun _ => .blank,
          .blank,
          idleDir iHead,
          fun i => idleDir (wHeads i),
          Dir3.right )
      else
        -- Not at cell 0 → keep moving left, preserve output cell contents
        ( Sum.inr .rewind,
          fun _ => .blank,
          readBackWrite oHead,
          idleDir iHead,
          fun i => idleDir (wHeads i),
          Dir3.left )
    -- ══════════════════════════════════════════════════════════════════
    -- Flip phase: at cell 1, flip the output bit and halt
    -- ══════════════════════════════════════════════════════════════════
    | Sum.inr .flip =>
      ( Sum.inr .done,
        fun _ => .blank,
        flipBit oHead,
        idleDir iHead,
        fun i => idleDir (wHeads i),
        idleDir oHead )
    -- ══════════════════════════════════════════════════════════════════
    -- Done (= qhalt): unreachable by step, but δ is total
    -- ══════════════════════════════════════════════════════════════════
    | Sum.inr .done =>
      allIdle (Sum.inr .done) iHead wHeads oHead,
    δ_right_of_start := by
      intro state iHead wHeads oHead
      match state with
      | Sum.inl q =>
        dsimp only []
        split
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
                 idleDir_right_of_start⟩
        · exact tm.δ_right_of_start q iHead wHeads oHead
      | Sum.inr .rewind =>
        dsimp only []
        split
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, fun _ => rfl⟩
        · refine ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, ?_⟩
          intro h; next hn => exact absurd h hn
      | Sum.inr .flip =>
        exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
      | Sum.inr .done =>
        exact rightOfStart_allIdle iHead wHeads oHead }

end TM
