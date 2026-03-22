import Complexitylib.Models.TuringMachine.UTM.Defs
import Complexitylib.Models.TuringMachine.Hoare.Defs
import Complexitylib.Models.TuringMachine.Combinators.SeqInternal

/-!
# Simulation Configuration

Defines the simulation invariant and tape predicates that relate the UTM's
work tapes to the simulated TM's configuration.

## Main definitions

- `SimInvariant` — the loop invariant: work tapes encode a simulated config
- `stateOnTapeAt` — one-hot state encoding on a tape
- `superCellsCorrect` — super-cell encoding of all simulated tapes
- `descOnTape` — description bits stored on a tape
- `scratchHasInputPattern` — scratch tape has serialized (state, symbols)
- `scratchHasTransOutput` — scratch tape has decoded transition output
- `WorkTapesWF` — all work tapes have cell 0 = ▷, cells ≥ 1 ≠ ▷

## Work Tape Layout (4 work tapes)

| Tape | Index | Contents |
|------|-------|----------|
| Description | `0` | Encoded TM description (read-only after init) |
| State | `1` | Current simulated state (one-hot: k cells) |
| Simulation | `2` | All simulated tapes interleaved as super-cells |
| Scratch | `3` | Temporary workspace |
-/

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Work tape indices
-- ════════════════════════════════════════════════════════════════════════

abbrev utmDescTape : Fin 4 := 0
abbrev utmStateTape : Fin 4 := 1
abbrev utmSimTape : Fin 4 := 2
abbrev utmScratchTape : Fin 4 := 3

-- ════════════════════════════════════════════════════════════════════════
-- Tape well-formedness
-- ════════════════════════════════════════════════════════════════════════

/-- All work tapes are well-formed: cell 0 = ▷, cells ≥ 1 ≠ ▷. -/
def WorkTapesWF (work : Fin 4 → Tape) : Prop :=
  (∀ i, (work i).cells 0 = Γ.start) ∧
  (∀ i j, j ≥ 1 → (work i).cells j ≠ Γ.start)

-- ════════════════════════════════════════════════════════════════════════
-- State encoding on tape
-- ════════════════════════════════════════════════════════════════════════

/-- Encode a state `q : Fin k` as a one-hot pattern on a tape.
    Cell 0 = ▷ (as always).
    Cell (j+1) = Γ.one if j = q.val, else Γ.zero, for 0 ≤ j < k.
    Cell (k+1) = Γ.blank (sentinel). -/
def stateOnTapeAt (k : ℕ) (q : Fin k) (t : Tape) : Prop :=
  t.cells 0 = Γ.start ∧
  (∀ j, j < k → t.cells (j + 1) = if j = q.val then Γ.one else Γ.zero) ∧
  t.cells (k + 1) = Γ.blank

-- ════════════════════════════════════════════════════════════════════════
-- Super-cell encoding of simulated tapes
-- ════════════════════════════════════════════════════════════════════════

/-- The simulation tape correctly encodes a single simulated tape at a given
    position. For position `pos` of simulated tape `tapeIdx`:
    - Head marker cell = Γ.one if the simulated head is at `pos`, Γ.blank otherwise
    - Symbol cells encode `tape.cells pos` via `symToCellPair`

    Design: head-absent = `Γ.blank` (not `Γ.zero`) so that uninitialized UTM sim
    tape cells automatically satisfy this predicate for blank-content positions
    where the head is elsewhere. -/
def simTapeCellCorrect (numTapes : ℕ) (tapeIdx : ℕ) (pos : ℕ)
    (simHead : ℕ) (simSym : Γ) (utmSim : Tape) : Prop :=
  let base := SuperCell.simTapeOffset numTapes pos tapeIdx
  let (hi, lo) := SuperCell.symToCellPair simSym
  utmSim.cells base = (if simHead = pos then Γ.one else Γ.blank) ∧
  utmSim.cells (base + 1) = hi ∧
  utmSim.cells (base + 2) = lo

/-- The simulation tape correctly encodes all simulated tapes at every position.
    The simulated machine has n work tapes, so n+2 total tapes (input + n work + output).
    Tape indices: 0 = input, 1..n = work, n+1 = output. -/
def superCellsCorrect {n : ℕ} {Q : Type} (simCfg : Cfg n Q) (utmSim : Tape) : Prop :=
  utmSim.cells 0 = Γ.start ∧
  -- Input tape encoding (tape index 0)
  (∀ pos, simTapeCellCorrect (n + 2) 0 pos simCfg.input.head
    (simCfg.input.cells pos) utmSim) ∧
  -- Work tape encodings (tape indices 1..n)
  (∀ (i : Fin n) pos, simTapeCellCorrect (n + 2) (i.val + 1) pos
    (simCfg.work i).head ((simCfg.work i).cells pos) utmSim) ∧
  -- Output tape encoding (tape index n+1)
  (∀ pos, simTapeCellCorrect (n + 2) (n + 1) pos simCfg.output.head
    (simCfg.output.cells pos) utmSim)

-- ════════════════════════════════════════════════════════════════════════
-- Description tape encoding
-- ════════════════════════════════════════════════════════════════════════

/-- A tape stores a list of bools at cells 1..len, with cell 0 = ▷ and
    a blank sentinel after. Used for both the description tape and scratch tape. -/
def tapeStoresBools (bits : List Bool) (t : Tape) : Prop :=
  t.cells 0 = Γ.start ∧
  (∀ (i : ℕ) (hi : i < bits.length),
    t.cells (i + 1) = Γ.ofBool (bits[i]'hi)) ∧
  t.cells (bits.length + 1) = Γ.blank

/-- The description tape correctly stores the encoded TM description. -/
abbrev descOnTape (desc : List Bool) (t : Tape) : Prop := tapeStoresBools desc t

-- ════════════════════════════════════════════════════════════════════════
-- Scratch tape predicates
-- ════════════════════════════════════════════════════════════════════════

/-- The scratch tape contains the serialized input pattern (state + current symbols)
    for lookup in the transition table.

    Format matches the input pattern prefix of a self-describing entry:
    q (one-hot, k bits) ++ iHead (2b) ++ wHeads (2n bits) ++ oHead (2b). -/
def scratchHasInputPattern (k n : ℕ) (q : Fin k)
    (iHead : Γ) (wHeads : Fin n → Γ) (oHead : Γ) (scratch : Tape) : Prop :=
  tapeStoresBools (TMEncoding.encodeInputPattern k n q iHead wHeads oHead) scratch ∧
  scratch.head = 1

/-- The scratch tape contains the decoded transition output after lookup.

    Format matches the output portion of a self-describing entry:
    q' (one-hot, k bits) ++ wWrites (2n bits) ++ oWrite (2b)
    ++ iDir (2b) ++ wDirs (2n bits) ++ oDir (2b). -/
def scratchHasTransOutput (k n : ℕ) (q' : Fin k)
    (wW : Fin n → Γw) (oW : Γw)
    (iD : Dir3) (wD : Fin n → Dir3) (oD : Dir3) (scratch : Tape) : Prop :=
  tapeStoresBools (TMEncoding.encodeTransOutput k n q' wW oW iD wD oD) scratch ∧
  scratch.head = 1

-- ════════════════════════════════════════════════════════════════════════
-- Simulation invariant
-- ════════════════════════════════════════════════════════════════════════

/-- The simulation invariant: the UTM's work tapes encode a simulated TM
    configuration. This is the loop invariant for `loopTM simStepTM checkHaltTM`.

    Existentially quantifies over the simulated config `simCfg`. The sub-machine
    specs are parametric in `simCfg` and instantiate the existential when composing.

    Components:
    - Description tape stores the encoded TM
    - State tape has one-hot encoding of current state
    - Simulation tape has super-cell encoding of all simulated tapes
    - All work tape heads at cell 1 (rewound)
    - All work tapes well-formed (cell 0 = ▷, cells ≥ 1 ≠ ▷) -/
noncomputable def SimInvariant {n : ℕ} (tm : TM n) (k : ℕ)
    (hk : k = @Fintype.card tm.Q tm.finQ) (desc : List Bool) : TapePred 4 :=
  fun _inp work _out =>
    ∃ (simCfg : Cfg n tm.Q),
      descOnTape desc (work utmDescTape) ∧
      stateOnTapeAt k (tm.stateEquivK hk simCfg.state) (work utmStateTape) ∧
      superCellsCorrect simCfg (work utmSimTape) ∧
      (∀ i, (work i).head ≥ 1) ∧
      WorkTapesWF work

-- ════════════════════════════════════════════════════════════════════════
-- seqTM transition preservation
-- ════════════════════════════════════════════════════════════════════════

/-- When a tape reads a non-▷ symbol, `idleDir` returns `.stay`. -/
private theorem idleDir_stay_of_ne {t : Tape} (h : t.read ≠ Γ.start) :
    idleDir t.read = Dir3.stay := by
  simp [idleDir, h]

/-- When a tape reads a non-▷ symbol, `readBackWrite` preserves it. -/
private theorem readBackWrite_toΓ_eq_read {t : Tape} (h : t.read ≠ Γ.start) :
    (readBackWrite t.read).toΓ = t.read := by
  cases hr : t.read <;> simp_all [readBackWrite, Γw.toΓ]

/-- `seqTransitionTape` is identity when the tape reads a non-▷ symbol
    and head ≥ 1. (Head stays, cell is written back with same value.) -/
theorem seqTransitionTape_id {t : Tape}
    (hread : t.read ≠ Γ.start) (hhead : t.head ≥ 1) :
    seqTransitionTape t = t := by
  simp only [seqTransitionTape, Tape.writeAndMove, idleDir_stay_of_ne hread,
    Tape.move, readBackWrite_toΓ_eq_read hread, Tape.write]
  split
  · omega
  · show { head := t.head, cells := Function.update t.cells t.head t.read } = t
    simp only [Tape.read, Function.update_eq_self]

/-- `seqTransitionInput` is identity when the tape reads a non-▷ symbol. -/
theorem seqTransitionInput_id {t : Tape}
    (hread : t.read ≠ Γ.start) :
    seqTransitionInput t = t := by
  simp only [seqTransitionInput, idleDir_stay_of_ne hread, Tape.move]

/-- When all work tapes are well-formed and heads ≥ 1, `seqTransitionTape` is
    identity on every work tape. This is the key lemma for `seqTM_hoareTime`'s
    `h_trans` obligation: the intermediate postcondition carries through unchanged. -/
theorem seqTransition_work_id {work : Fin 4 → Tape}
    (hwf : WorkTapesWF work)
    (hheads : ∀ i, (work i).head ≥ 1) :
    (fun i => seqTransitionTape (work i)) = work := by
  ext i
  apply seqTransitionTape_id
  · intro h
    have := hwf.2 i (work i).head (hheads i)
    rw [Tape.read] at h
    exact this h
  · exact hheads i

end TM
