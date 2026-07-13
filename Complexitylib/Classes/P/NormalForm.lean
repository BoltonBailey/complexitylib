/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.P.Internal.NormalForm

/-!
# Polynomial-time function normal form

`FP` membership can be witnessed by a deterministic machine whose running-time
bound is the evaluation of a polynomial with natural coefficients. Unlike the
arbitrary asymptotic witness in the definition of `FP`, this normalized bound
is valid on every input length and is monotone.

## Main result

- `mem_FP_iff_computesInTime_polynomial` — polynomial-evaluation normal form for `FP`
-/

namespace Complexity

/-- A function belongs to `FP` exactly when some deterministic machine
computes it within the evaluation of a natural-coefficient polynomial. -/
theorem mem_FP_iff_computesInTime_polynomial {f : List Bool → List Bool} :
    f ∈ FP ↔ ∃ (k : ℕ) (tm : TM k) (p : Polynomial ℕ),
      tm.ComputesInTime f p.eval := by
  exact mem_FP_iff_computesInTime_polynomial_internal

end Complexity
