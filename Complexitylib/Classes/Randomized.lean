import Complexitylib.Models.TuringMachine
import Complexitylib.Classes.Polynomial

/-!
# Randomized time complexity classes

This file defines the randomized complexity classes **BPP**, **RP**, **coRP**,
**ZPP**, and **PP**, along with the time-parameterized class `BPTIME`.

A PTM (probabilistic Turing machine) is an NTM where the two transition
functions are selected uniformly at random. Acceptance probability is defined
via `NTM.acceptProb`.

## Helper predicates

The acceptance-probability conditions shared across classes are factored into
`NTM.AcceptsWithProb` (lower-bounding acceptance on yes-instances) and
`NTM.RejectsWithProb` (upper-bounding acceptance on no-instances).
-/

namespace NTM

variable {n : ℕ}

/-- The PTM accepts every `x ∈ L` with probability at least `c` within
    `T(|x|)` steps. -/
def AcceptsWithProb (tm : NTM n) (L : Language) (T : ℕ → ℕ) (c : ℚ) : Prop :=
  ∀ x, x ∈ L → tm.acceptProb x (T x.length) ≥ c

/-- The PTM accepts every `x ∉ L` with probability at most `s` within
    `T(|x|)` steps. -/
def RejectsWithProb (tm : NTM n) (L : Language) (T : ℕ → ℕ) (s : ℚ) : Prop :=
  ∀ x, x ∉ L → tm.acceptProb x (T x.length) ≤ s

end NTM

/-- `BPTIME(T)` is the class of languages decidable by a PTM in time `T(n)`
    with two-sided bounded error (accept probability ≥ 2/3 on yes-instances,
    ≤ 1/3 on no-instances). -/
def BPTIME (T : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : NTM k),
    tm.AllPathsHaltIn T ∧
    tm.AcceptsWithProb L T (2 / 3) ∧
    tm.RejectsWithProb L T (1 / 3)}

/-- **BPP** is the class of languages decidable by a PTM in polynomial time
    with two-sided bounded error: yes-instances accepted with probability ≥ 2/3,
    no-instances accepted with probability ≤ 1/3. -/
def BPP : Set Language :=
  {L | ∃ (T : ℕ → ℕ), IsPolyBounded T ∧ L ∈ BPTIME T}

/-- `RTIME(T)` is the class of languages decidable by a PTM in time `T(n)`
    with one-sided error: yes-instances accepted with probability ≥ 1/2,
    no-instances never accepted (accept probability 0). -/
def RTIME (T : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : NTM k),
    tm.AllPathsHaltIn T ∧
    tm.AcceptsWithProb L T (1 / 2) ∧
    tm.RejectsWithProb L T 0}

/-- **RP** is the class of languages decidable by a PTM in polynomial time
    with one-sided error: yes-instances accepted with probability ≥ 1/2,
    no-instances never accepted. -/
def RP : Set Language :=
  {L | ∃ (T : ℕ → ℕ), IsPolyBounded T ∧ L ∈ RTIME T}

/-- **coRP** is the class of languages whose complements are in RP.
    Equivalently: yes-instances always accepted (probability 1), no-instances
    accepted with probability ≤ 1/2. -/
def CoRP : Set Language :=
  {L | Lᶜ ∈ RP}

/-- **ZPP** (zero-error probabilistic polynomial time) is RP ∩ coRP. A language
    is in ZPP iff it has a PTM with zero-error expected polynomial running
    time. -/
def ZPP : Set Language := RP ∩ CoRP

/-- **PP** (probabilistic polynomial time) is the class of languages decidable
    by a PTM in polynomial time with unbounded error: `x ∈ L` iff the PTM
    accepts with probability strictly greater than 1/2. -/
def PP : Set Language :=
  {L | ∃ (T : ℕ → ℕ), IsPolyBounded T ∧ ∃ (k : ℕ) (tm : NTM k),
    tm.AllPathsHaltIn T ∧
    (∀ x, x ∈ L → tm.acceptProb x (T x.length) > 1 / 2) ∧
    (∀ x, x ∉ L → tm.acceptProb x (T x.length) ≤ 1 / 2)}
