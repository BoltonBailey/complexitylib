import Mathlib.Data.Real.Basic

/-!
# Negligible functions

A function `f : ℕ → ℝ` is *negligible* if it vanishes faster than any inverse
polynomial. This is used in cryptographic definitions throughout Arora-Barak
(Chapter 9 and beyond).
-/

/-- A function `f : ℕ → ℝ` is negligible if for every `c`, `|f(n)| · n^c < 1`
    for all sufficiently large `n` (Arora-Barak Section 9.1). -/
def Negligible (f : ℕ → ℝ) : Prop :=
  ∀ c : ℕ, ∃ N : ℕ, ∀ n ≥ N, |f n| * (n : ℝ) ^ c < 1
