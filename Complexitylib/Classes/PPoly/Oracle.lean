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

/-- At every positive query width, the selected family member computes the
induced Boolean oracle on the serialized query. -/
theorem circuit_eval_eq_oracle {language : Language}
    (circuitOracle : PolynomialCircuitOracle language)
    {queryWidth : ℕ} [NeZero queryWidth] (query : BitString queryWidth) :
    (circuitOracle.family.circuit queryWidth).eval query 0 =
      circuitOracle.oracle query.toList := by
  rw [oracle, CircuitFamily.evalList_toList]
  obtain ⟨width, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne queryWidth)
  rfl

/-- At every positive width, the selected oracle circuit's size is the circuit
family's size at that width. -/
theorem circuit_size_eq_family_size {language : Language}
    (circuitOracle : PolynomialCircuitOracle language)
    (queryWidth : ℕ) [NeZero queryWidth] :
    (circuitOracle.family.circuit queryWidth).size =
      circuitOracle.family.size queryWidth := by
  obtain ⟨width, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne queryWidth)
  rfl

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
