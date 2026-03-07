import Complexitylib.Models.TuringMachine
import Complexitylib.Classes.Polynomial

/-!
# BPP

This file defines **BPP**, the class of languages decidable by a probabilistic
Turing machine in polynomial time with bounded error.

A PTM is an NTM where the two transition functions are selected uniformly at
random. Acceptance probability is defined via `NTM.acceptProb`.
-/

/-- **BPP** is the class of languages decidable by a probabilistic TM in
    polynomial time with two-sided bounded error: all computation paths halt,
    yes-instances are accepted with probability ≥ 2/3, and no-instances are
    accepted with probability ≤ 1/3. -/
def BPP : Set Language :=
  {L | ∃ (T : ℕ → ℕ), IsPolyBounded T ∧ ∃ (k : ℕ) (tm : NTM k),
    tm.AllPathsHaltIn T ∧
    (∀ x, x ∈ L → tm.acceptProb x (T x.length) ≥ 2 / 3) ∧
    (∀ x, x ∉ L → tm.acceptProb x (T x.length) ≤ 1 / 3)}
