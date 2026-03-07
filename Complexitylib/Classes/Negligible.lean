import Mathlib.Data.Real.Basic

/-!
# Negligible functions

A function `f : ℕ → ℝ` is *negligible* if it vanishes faster than any inverse
polynomial. This is the standard notion used in cryptographic definitions.
-/

/-- A function `f : ℕ → ℝ` is negligible if for every `c`, `|f(n)| · n^c < 1`
    for all sufficiently large `n`. -/
def Negligible (f : ℕ → ℝ) : Prop :=
  ∀ c : ℕ, ∃ N : ℕ, ∀ n ≥ N, |f n| * (n : ℝ) ^ c < 1
