import Complexitylib.Models.TuringMachine
import Complexitylib.Classes.Time
import Complexitylib.Classes.Space
import Complexitylib.Classes.Pairing
import Complexitylib.Asymptotics
import Mathlib.Data.Nat.Log

namespace Complexity

/-!
# Log-space transducer classes

This file defines the log-space complexity classes **L**, **NL**, **coNL**,
**FL**, and the search problem classes **FNL**, **TFNL**.

These classes require the machine to be a *transducer* (`IsTransducer`): the
output tape head never moves left, preventing it from being used as extra
workspace beyond the `O(log n)` space bound on work tapes.

The base parametric classes `DSPACE` and `NSPACE` (which do not require the
transducer property) are defined in `Space.lean`.
-/

open Complexity

/-- **L** (LOGSPACE) is the class of languages decidable by a deterministic
    log-space transducer: a DTM with `O(log n)` work tape space whose output
    tape head never moves left. The transducer constraint prevents the output
    tape from being used as extra workspace beyond the space bound. -/
def L : Set Language :=
  {L | ∃ (k : ℕ) (tm : TM k) (f : ℕ → ℕ),
    tm.IsTransducer ∧ tm.DecidesInSpace L f ∧ f =O (fun n => Nat.log 2 n)}

/-- **NL** is the class of languages decidable by a nondeterministic log-space
    transducer: an NTM with `O(log n)` work tape space whose output tape head
    never moves left. -/
def NL : Set Language :=
  {L | ∃ (k : ℕ) (tm : NTM k) (f : ℕ → ℕ),
    tm.IsTransducer ∧ tm.DecidesInSpace L f ∧ f =O (fun n => Nat.log 2 n)}

/-- **coNL** is the class of languages whose complements are in NL.
    By the Immerman-Szelepcsényi theorem coNL = NL, but this is nontrivial. -/
def coNL : Set Language := complClass NL

/-- **FL** is the class of functions computable by a deterministic log-space
    transducer: a DTM with `O(log n)` work tape space whose output tape head
    never moves left. -/
def FL : Set (List Bool → List Bool) :=
  {f | ∃ (k : ℕ) (tm : TM k) (S : ℕ → ℕ),
    tm.IsTransducer ∧ tm.ComputesInSpace f S ∧ S =O (fun n => Nat.log 2 n)}

/-- **FNL** is the class of search problems with log-space verifiable relations:
    binary relations that are polynomially balanced (witnesses have poly-bounded
    length) and whose pair language is decidable in L (deterministic log space).

    This parallels FNP, which uses P (deterministic poly time) for verification. -/
def FNL : Set (List Bool → List Bool → Prop) :=
  {R | PolyBalanced R ∧ pairLang R ∈ L}

/-- **TFNL** is the class of total FNL search problems: every instance has at
    least one witness. -/
def TFNL : Set (List Bool → List Bool → Prop) :=
  {R ∈ FNL | ∀ x, ∃ y, R x y}

end Complexity
