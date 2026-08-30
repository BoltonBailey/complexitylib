/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly
public import Complexitylib.Classes.PPoly.Oracle.Defs

/-!
# Polynomial-size circuit oracles

This module identifies `P/poly` membership with the existence of a packaged
polynomial-size circuit oracle and proves that the induced Boolean oracle has
the intended exact language semantics.
-/


public section

namespace Complexity

namespace PolynomialCircuitOracle

/-- Evaluating the packaged circuit family gives an exact oracle for its
language. -/
theorem oracle_decides {language : Language}
    (circuitOracle : PolynomialCircuitOracle language) :
    circuitOracle.oracle.Decides language :=
  circuitOracle.decides.evalList

end PolynomialCircuitOracle

/-- A language is in `P/poly` exactly when it has a packaged polynomial-size
circuit oracle. -/
theorem mem_PPoly_iff_nonempty_polynomialCircuitOracle
    {language : Language} :
    language ∈ PPoly ↔ Nonempty (PolynomialCircuitOracle language) := by
  rw [mem_PPoly_iff]
  constructor
  · rintro ⟨family, exponent, decides, size_bigO⟩
    exact ⟨⟨family, exponent, decides, size_bigO⟩⟩
  · rintro ⟨⟨family, exponent, decides, size_bigO⟩⟩
    exact ⟨family, exponent, decides, size_bigO⟩

end Complexity
