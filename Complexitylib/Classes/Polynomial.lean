import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Polynomial boundedness

A function `f : ℕ → ℕ` is *polynomially bounded* if there exists a polynomial `p`
with natural number coefficients such that `f(n) ≤ p(n)` for all `n`. Used in
`PolyBalanced` to express the "short witness" condition for NP, FNP, FNL, etc.
-/

/-- A function `f : ℕ → ℕ` is polynomially bounded if `f(n) ≤ p(n)` for some
    polynomial `p` with natural number coefficients. Used by `PolyBalanced`
    to bound witness length in search problem classes. -/
def IsPolyBounded (f : ℕ → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, f n ≤ p.eval n
