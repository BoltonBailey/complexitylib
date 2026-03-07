import Complexitylib.Models.TuringMachine
import Complexitylib.Asymptotics
import Complexitylib.Classes.Pairing
import Mathlib.Data.Nat.Log

/-!
# Space complexity classes

This file defines the space complexity classes `DSPACE`, `NSPACE`, **L**, **NL**,
**coNL**, **PSPACE**, **FL**, and the search problem classes **FNL**, **TFNL**.

## Space measurement

Space is measured on work tapes only. The input tape is read-only (structurally
in our model) and does not count. For function classes (FL), the output tape is
additionally constrained to rightward-only head movement, preventing its use as
extra workspace.
-/

open Complexity

/-- `DSPACE(S)` is the class of languages decidable by a deterministic TM using
    `O(S(n))` space on work tapes. -/
def DSPACE (S : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : TM k) (f : ℕ → ℕ),
    tm.DecidesInSpace L f ∧ f =O S}

/-- `NSPACE(S)` is the class of languages decidable by a nondeterministic TM
    using `O(S(n))` space on work tapes. -/
def NSPACE (S : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : NTM k) (f : ℕ → ℕ),
    tm.DecidesInSpace L f ∧ f =O S}

/-- **L** (LOGSPACE) is the class of languages decidable by a deterministic TM
    using logarithmic space on work tapes: `L = DSPACE(log n)`. -/
def L : Set Language :=
  DSPACE (fun n => Nat.log 2 n)

/-- Alias: `LOGSPACE` is another name for `L`. -/
abbrev LOGSPACE := L

/-- **NL** is the class of languages decidable by a nondeterministic TM using
    logarithmic space on work tapes: `NL = NSPACE(log n)`. -/
def NL : Set Language :=
  NSPACE (fun n => Nat.log 2 n)

/-- **coNL** is the class of languages whose complements are in NL.
    By the Immerman-Szelepcsényi theorem coNL = NL, but this is nontrivial. -/
def CoNL : Set Language :=
  {L | Lᶜ ∈ NL}

/-- **FL** is the class of functions computable by a deterministic log-space
    transducer: a DTM with `O(log n)` work tape space and a right-only output
    tape. -/
def FL : Set (List Bool → List Bool) :=
  {f | ∃ (k : ℕ) (tm : TM k) (S : ℕ → ℕ),
    tm.ComputesInSpace f S ∧ S =O (fun n => Nat.log 2 n)}

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

/-- **PSPACE** is the class of languages decidable by a deterministic TM using
    polynomial space on work tapes: `PSPACE = ⋃_k DSPACE(n^k)`. -/
def PSPACE : Set Language :=
  ⋃ k : ℕ, DSPACE (· ^ k)
