import Complexitylib.Models.TuringMachine
import Complexitylib.Classes.Polynomial
import Mathlib.Data.Nat.Log

/-!
# Simultaneous time-space complexity classes

This file defines the simultaneous time-space class `DTISP(T, S)` and **SC**
(Steve's Class), following Arora-Barak Chapter 4.

The key distinction from intersecting separate time and space classes is that
`DTISP` requires a *single* machine satisfying both bounds simultaneously.
-/

/-- A function `f : ℕ → ℕ` is polylogarithmically bounded if `f(n) ≤ p(log₂(n+1))`
    for some polynomial `p` with natural number coefficients. This captures
    the `polylog(n) = (log n)^{O(1)}` bound used in the definition of SC. -/
def IsPolyLogBounded (f : ℕ → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, f n ≤ p.eval (Nat.log 2 (n + 1))

/-- `DTISP(T, S)` is the class of languages decidable by a single deterministic
    TM running in time `T(n)` and space `S(n)` simultaneously
    (AB Definition 4.11). -/
def DTISP (T S : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : TM k), tm.DecidesInTimeSpace L T S}

/-- **SC** (Steve's Class, named after Stephen Cook) is the class of languages
    decidable in polynomial time and polylogarithmic space simultaneously:
    `SC = ∪_{T,S} DTISP(T, S)` over polynomially bounded `T` and
    polylogarithmically bounded `S`. -/
def SC : Set Language :=
  {L | ∃ T S, IsPolyBounded T ∧ IsPolyLogBounded S ∧ L ∈ DTISP T S}
