import Complexitylib.Models.TuringMachine.SingleTape.Internal
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

/-!
# Single-tape simulation — simulator state type

The state type `SimQ k Q` of `NTM.singleTapeSim` (for a source machine with
state type `Q` and `k` work tapes) and its `Fintype`/`DecidableEq` instances.
See `docs/A4-SingleTapeSimulation.md` §4–5 for the phase semantics.

The instances are **noncomputable** by design: `singleTapeSim` is a
`noncomputable def`, and synthesizing computable `DecidableEq` for the
function-typed phase data (`Fin k → Γ`, `Fin k → Γw × Dir3`) hits Lean's
product/`Pi` synthesis-size limit. `Finite` is a `Prop` and composes with no
such limit, so we route through it (`Fintype.ofFinite` / `Classical.decEq`).
-/

namespace NTM.SingleTape

/-- A sweep position: which tape's triple (`Fin k`) and which of its 3 cells
    (head-bit / sym-hi / sym-lo, as `Fin 3`). -/
abbrev SweepPos (k : ℕ) := Fin k × Fin 3

/-- GATHER-phase data: the simulated state `q`, the head symbols accumulated so
    far (`acc`), the input/output symbols read at macro-step start (kept for the
    `δ` computation and the `▷`-dodge), the current sweep position, a flag for
    whether the current tape's head marker was seen in this triple, and the
    pending high symbol cell read. -/
abbrev GatherData (k : ℕ) (Q : Type) := Q × (Fin k → Γ) × Γ × Γ × SweepPos k × Bool × Γ

/-- SCATTER-phase data: the next simulated state `q'`, the per-tape write+move
    action (combined as one `Pi` to keep instance synthesis light), the output
    write/dir, the input dir, the input/output symbols (for the `▷`-dodge at
    commit), and the current sweep position. -/
abbrev ScatterData (k : ℕ) (Q : Type) :=
  Q × (Fin k → Γw × Dir3) × (Γw × Dir3) × Dir3 × Γ × Γ × SweepPos k

/-- COMMIT-phase data: the next simulated state and the deferred input/output
    actions (output write+dir, input dir) with the symbols originally read. -/
abbrev CommitData (Q : Type) := Q × Γw × Dir3 × Dir3 × Γ × Γ

/-- The simulator's state type. Phases: `run` (between macro-steps, work head at
    cell 1), `gather`/`scatter` (the two work-tape sweeps), `commit` (apply the
    deferred input/output actions), and a dedicated `halt` (`Unit`). -/
abbrev SimQ (k : ℕ) (Q : Type) :=
  Q ⊕ GatherData k Q ⊕ ScatterData k Q ⊕ CommitData Q ⊕ Unit

namespace SimQ

variable {k : ℕ} {Q : Type}

/-- Between macro-steps, about to simulate an `N`-step from state `q`. -/
@[match_pattern] def run (q : Q) : SimQ k Q := Sum.inl q
/-- Sweeping right, gathering head symbols. -/
@[match_pattern] def gather (d : GatherData k Q) : SimQ k Q := Sum.inr (Sum.inl d)
/-- Sweeping, writing new symbols and moving head markers. -/
@[match_pattern] def scatter (d : ScatterData k Q) : SimQ k Q := Sum.inr (Sum.inr (Sum.inl d))
/-- Applying the deferred input/output actions. -/
@[match_pattern] def commit (d : CommitData Q) : SimQ k Q :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inl d)))
/-- The halt state. -/
@[match_pattern] def halt : SimQ k Q := Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))

end SimQ

/-- `Finite` composes freely (a `Prop`), so this synthesizes despite the
    function-typed phase data. -/
instance instFiniteSimQ (k : ℕ) (Q : Type) [Fintype Q] : Finite (SimQ k Q) := by
  infer_instance

/-- Noncomputable `Fintype` via `Finite` — sidesteps the product/`Pi`
    `DecidableEq` synthesis limit. -/
noncomputable instance instFintypeSimQ (k : ℕ) (Q : Type) [Fintype Q] :
    Fintype (SimQ k Q) := Fintype.ofFinite _

/-- Noncomputable decidable equality — only used inside proofs (`trace`/`step`
    reduce `c.state = qhalt` in `Prop`), never executed. -/
noncomputable instance instDecidableEqSimQ (k : ℕ) (Q : Type) :
    DecidableEq (SimQ k Q) := Classical.decEq _

end NTM.SingleTape
