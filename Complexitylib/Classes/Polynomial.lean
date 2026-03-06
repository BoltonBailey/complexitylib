import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Polynomial boundedness

A function `f : ℕ → ℕ` is *polynomially bounded* if there exists a polynomial `p`
with natural number coefficients such that `f(n) ≤ p(n)` for all `n`. This captures
the complexity-theoretic notion of "polynomial-time" bounds used throughout
Arora-Barak's *Computational Complexity: A Modern Approach*.
-/

/-- A function `f : ℕ → ℕ` is polynomially bounded if `f(n) ≤ p(n)` for some
    polynomial `p` with natural number coefficients. This is the standard
    complexity-theoretic notion used in definitions of P, NP, BPP, etc.
    (Arora-Barak, throughout Chapter 1 and beyond). -/
def IsPolyBounded (f : ℕ → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, f n ≤ p.eval n
