/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Hamming.Defs
public import Complexitylib.Metacomplexity.Hamming.Existence.Internal

/-!
# Existence of separated Boolean codes

A maximum-cardinality code of a prescribed minimum distance covers the Boolean
cube by balls of radius `minimumDistance - 1`. Counting that cover gives the
finite Gilbert--Varshamov inequality. This is an existence theorem only; it
does not supply an efficient encoder or decoder.
-/


public section

namespace Complexity

namespace BooleanHamming

/-- Some code of minimum distance `d` covers the cube by radius-`d-1` balls. -/
theorem exists_isSeparated_and_covering (length minimumDistance : ℕ) :
    ∃ code : Finset (Word length),
      IsSeparated code minimumDistance ∧
        ∀ word : Word length,
          ∃ center ∈ code,
            distance word center ≤ minimumDistance - 1 :=
  exists_isSeparated_and_covering_internal length minimumDistance

/-- Finite Gilbert--Varshamov bound for Boolean codes. -/
theorem gilbertVarshamov_bound (length minimumDistance : ℕ) :
    ∃ code : Finset (Word length),
      IsSeparated code minimumDistance ∧
        2 ^ length ≤ code.card * volume length (minimumDistance - 1) :=
  gilbertVarshamov_bound_internal length minimumDistance

end BooleanHamming

end Complexity
