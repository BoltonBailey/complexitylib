import Mathlib.Data.Real.Basic

namespace Complexity

/-!
# Negligible functions

A function `f : ℕ → ℝ` is *negligible* if it vanishes faster than any inverse
polynomial. This is the standard notion used in cryptographic definitions.
-/

/-- A function `f : ℕ → ℝ` is negligible if for every `c`, `|f(n)| < 1/n^c`
    for all sufficiently large `n`. The threshold `N` is required to be positive,
    ensuring `n > 0` and `1/n^c` is well-defined. -/
def Negligible (f : ℕ → ℝ) : Prop :=
  ∀ c : ℕ, ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N, |f n| < 1 / (n : ℝ) ^ c

end Complexity
