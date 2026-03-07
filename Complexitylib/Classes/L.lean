import Complexitylib.Models.TuringMachine
import Complexitylib.Classes.FNP
import Mathlib.Data.Nat.Log

/-!
# Logarithmic space complexity classes

This file defines the space complexity classes `DSPACE`, `NSPACE`, **L**, **NL**,
**coNL**, **FL**, and the search problem classes **FNL**, **coFNL**, **TFNL**
## Space measurement

Space is measured on work tapes only. The input tape is read-only (structurally
in our model) and does not count. For function classes (FL), the output tape is
additionally constrained to rightward-only head movement, preventing its use as
extra workspace.
-/

/-- A function `f : ℕ → ℕ` is logarithmically bounded if there exists a constant
    `c` such that `f(n) ≤ c * ⌊log₂(n + 1)⌋ + c` for all `n`. The `n + 1`
    avoids `log₂(0)`; the additive `c` handles small inputs. -/
def IsLogBounded (f : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, ∀ n, f n ≤ c * Nat.log 2 (n + 1) + c

/-- `DSPACE(S)` is the class of languages decidable by a deterministic TM using
    at most `S(n)` space on work tapes. -/
def DSPACE (S : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : TM k), tm.DecidesInSpace L S}

/-- `NSPACE(S)` is the class of languages decidable by a nondeterministic TM
    using at most `S(n)` space on work tapes. -/
def NSPACE (S : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : NTM k), tm.DecidesInSpace L S}

/-- **L** (LOGSPACE) is the class of languages decidable by a deterministic TM
    using logarithmic space on work tapes. -/
def L : Set Language :=
  {L | ∃ S, IsLogBounded S ∧ L ∈ DSPACE S}

/-- **NL** is the class of languages decidable by a nondeterministic TM using
    logarithmic space on work tapes. -/
def NL : Set Language :=
  {L | ∃ S, IsLogBounded S ∧ L ∈ NSPACE S}

/-- **coNL** is the class of languages whose complements are in NL.
    By the Immerman-Szelepcsényi theorem coNL = NL, but this is nontrivial. -/
def CoNL : Set Language :=
  {L | Lᶜ ∈ NL}

/-- **FL** is the class of functions computable by a deterministic log-space
    transducer: a DTM with logarithmically bounded work tape space and a
    right-only output tape. -/
def FL : Set (List Bool → List Bool) :=
  {f | ∃ S, IsLogBounded S ∧ ∃ (k : ℕ) (tm : TM k), tm.ComputesInSpace f S}

/-- **FNL** is the class of search problems defined by NL relations: binary
    relations that are polynomially balanced (witnesses have poly-bounded
    length) and decidable in L. -/
def FNL : Set (List Bool → List Bool → Prop) :=
  {R | (∃ p, IsPolyBounded p ∧ ∀ x y, R x y → y.length ≤ p x.length) ∧
       {z | ∃ x y, z = pair x y ∧ R x y} ∈ L}

/-- **coFNL** is the class of FNL search problems whose associated decision
    language `{x | ∃ y, R x y}` is in coNL. -/
def CoFNL : Set (List Bool → List Bool → Prop) :=
  {R ∈ FNL | {x | ∃ y, R x y} ∈ CoNL}

/-- **TFNL** is the class of total FNL search problems: every instance has at
    least one witness. -/
def TFNL : Set (List Bool → List Bool → Prop) :=
  {R ∈ FNL | ∀ x, ∃ y, R x y}
