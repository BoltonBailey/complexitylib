/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Oracle
public import Complexitylib.SAT.Headline

/-!
# SAT circuit oracles from `NP ⊆ P/poly`

This module extracts the exact polynomial-size SAT circuit family needed to
replace fixed-width SAT-oracle calls in a nonuniform computation. It does not
yet perform that adaptive circuit inlining step.
-/


public section

namespace Complexity

namespace SAT

/-- If every language in `NP` has polynomial-size circuits, then SAT has a
packaged polynomial-size circuit oracle. -/
theorem exists_polynomialCircuitOracle_of_NP_subset_PPoly
    (hNP : NP ⊆ PPoly) :
    Nonempty (PolynomialCircuitOracle language) :=
  mem_PPoly_iff_nonempty_polynomialCircuitOracle.mp (hNP language_mem_NP)

end SAT

end Complexity
