import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.UTM.Defs
import Complexitylib.Models.TuringMachine.UTM.Helpers

/-!
# UTM Simulation Step

This file defines the simulation step machine `simStepTM` and the simulation
configuration relation `SimConfig`.

## Design

The UTM uses 4 work tapes:
- Work 0: Encoded TM description (read-only after init)
- Work 1: Current simulated state (binary)
- Work 2: Simulated tape contents (all tapes interleaved as super-cells)
- Work 3: Scratch space

The simulation step machine `simStepTM` performs one step of the simulated TM:
1. Read current state from work tape 1
2. Read current tape symbols from work tape 2 (at head-marked positions)
3. Look up the transition in the description on work tape 0
4. Write new state to work tape 1
5. Write new symbols and move heads on work tape 2

## Simulation Configuration

`SimConfig` relates the UTM's work tape contents to the simulated TM's
configuration. This is the key simulation invariant maintained by the loop.
-/

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Work tape indices for the UTM (4 work tapes)
-- ════════════════════════════════════════════════════════════════════════

/-- Index of the description tape. -/
def descTape : Fin 4 := 0

/-- Index of the state tape. -/
def stateTape : Fin 4 := 1

/-- Index of the simulation tape (interleaved simulated tapes). -/
def simTape : Fin 4 := 2

/-- Index of the scratch tape. -/
def scratchTape : Fin 4 := 3

-- ════════════════════════════════════════════════════════════════════════
-- Simulation configuration relation
-- ════════════════════════════════════════════════════════════════════════

/-- Encode a state `q : Fin k` as a one-hot pattern on a tape.
    Cell 1 through k encode the state: cell (q+1) = Γ.one, rest = Γ.zero.
    Cell 0 = ▷ as always. -/
def stateOnTape (k : ℕ) (q : Fin k) (t : Tape) : Prop :=
  t.cells 0 = Γ.start ∧
  (∀ i, 1 ≤ i → i ≤ k → t.cells i = if i = q.val + 1 then Γ.one else Γ.zero) ∧
  t.cells (k + 1) = Γ.blank

/-- Width of a super-cell: 3 bits per simulated tape (1 head marker + 2 symbol bits). -/
def superCellWidth (numTapes : ℕ) : ℕ := 3 * numTapes

/-- Encode a Γ symbol as two cells on the simulation tape. -/
def symToCells (g : Γ) : Γ × Γ :=
  match g with
  | .zero  => (.zero, .zero)
  | .one   => (.zero, .one)
  | .blank => (.one, .zero)
  | .start => (.one, .one)

/-- The simulation relation: UTM work tapes encode a simulated TM configuration.

    This is the key invariant for the UTM correctness proof. It relates:
    - Work tape 0 (description): contains the encoded TM description
    - Work tape 1 (state): encodes the current simulated state
    - Work tape 2 (simulation): encodes all simulated tape contents
    - The simulated TM's actual configuration

    For a normalized `TM n` with `k = Fintype.card Q` states:
    - State tape has one-hot encoding of current state
    - Simulation tape has super-cells encoding all n+2 tape contents
    - Head positions within super-cells are marked -/
structure SimConfig {n : ℕ} (tm : TM n) (k : ℕ)
    (e : tm.Q ≃ Fin k) (desc : List Bool) where
  /-- The simulated configuration. -/
  simCfg : Cfg n tm.Q
  /-- The UTM's work tapes. -/
  utmWork : Fin 4 → Tape
  /-- Work tape 0 has the description. -/
  descCorrect : ∀ (i : ℕ) (hi : i < desc.length),
    (utmWork descTape).cells (i + 1) = Γ.ofBool (desc[i]'hi)
  /-- Work tape 1 encodes the current state. -/
  stateCorrect : stateOnTape k (e simCfg.state) (utmWork stateTape)

-- ════════════════════════════════════════════════════════════════════════
-- Check halt machine
-- ════════════════════════════════════════════════════════════════════════

/-- States for the halt-check machine. -/
inductive CheckHaltPhase where
  | rewindState  -- rewind state tape to cell 1
  | scanState    -- scan state tape for the qhalt marker
  | found        -- found qhalt, write 1 to output
  | notFound     -- didn't find qhalt, write 0 to output
  | done         -- halt
  deriving DecidableEq

instance : Fintype CheckHaltPhase where
  elems := {.rewindState, .scanState, .found, .notFound, .done}
  complete := fun x => by cases x <;> simp

/-- Check if the simulated machine has halted by examining the state tape.

    In the one-hot encoding, the halt state `qhalt` is at position `qhalt.val + 1`.
    This machine reads a specific position on the state tape to check for Γ.one.

    For simplicity, this machine checks if the state tape has Γ.one at any position
    that corresponds to the halt state encoding. Since the state is one-hot,
    checking position `qhalt + 1` is sufficient.

    However, since the UTM doesn't know qhalt at definition time (it's part of
    the encoded description), this machine reads the halt state position from
    the description tape.

    For Phase 2, we define a simpler version that just reads output cell 1
    of the state comparison result (assuming a prior comparison step wrote it). -/
def checkOutputTM : TM 4 := writeTM .blank  -- placeholder: will be replaced

-- ════════════════════════════════════════════════════════════════════════
-- Simulation step: composed from helpers
-- ════════════════════════════════════════════════════════════════════════

/-- The simulation step machine performs one step of the simulated TM.

    This is defined as a sequential composition of sub-machines:
    1. Read current state and symbols from work tapes 1 and 2
    2. Look up the transition entry in the description (work tape 0)
    3. Update state on work tape 1
    4. Write new symbols and move heads on work tape 2

    For Phase 2, we define the type signature and structure.
    The full implementation requires the sub-machines for table lookup
    and tape manipulation, which will be completed in Phase 3. -/
noncomputable def simStepTM (_descLen : ℕ) : TM 4 :=
  -- Phase 1: Rewind state and description tapes to cell 1
  seqTM (rewindWorkTM stateTape)
    -- Phase 2: Rewind description tape
    (seqTM (rewindWorkTM descTape)
      -- Phase 3: Scan description tape (placeholder for lookup)
      (seqTM (scanRightTM descTape)
        -- Phase 4: Rewind scratch tape
        (rewindWorkTM scratchTape)))

end TM
