/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.P.Defs

/-!
# Polynomial-time function normal form — proof internals

The definition of `FP` permits an arbitrary time function with a Big-O power
bound. This module replaces that witness by the evaluation of one polynomial
over the naturals, giving an everywhere-valid and monotone time bound.

The public theorem is in `Complexitylib.Classes.P.NormalForm`.
-/

namespace Complexity

/-- Internal proof that `FP` membership is equivalent to computation within
the evaluation of a natural-coefficient polynomial. -/
theorem mem_FP_iff_computesInTime_polynomial_internal
    {f : List Bool → List Bool} :
    f ∈ FP ↔ ∃ (k : ℕ) (tm : TM k) (p : Polynomial ℕ),
      tm.ComputesInTime f p.eval := by
  constructor
  · rintro ⟨d, k, tm, T, hcomp, hbig⟩
    obtain ⟨p, hp⟩ := BigO.pow_polynomial_bound hbig
    exact ⟨k, tm, p, hcomp.mono hp⟩
  · rintro ⟨k, tm, p, hcomp⟩
    refine ⟨p.natDegree, k, tm, p.eval, hcomp, ?_⟩
    exact BigO.of_polynomial_bound p fun _ => le_rfl

end Complexity
