/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.StatisticalTest.Oracle.Defs

/-!
# Finite statistical tests as Boolean oracles -- proof internals
-/


public section

namespace Complexity

theorem decodeFixedWidthBoolean?_ofFn_internal
    {length : ℕ} (bits : Fin length → Bool) :
    decodeFixedWidthBoolean? length (List.ofFn bits) = some bits := by
  simp [decodeFixedWidthBoolean?]

theorem finiteTestOracle_ofFn_internal
    {outputLength : ℕ} (test : Finset (Fin outputLength → Bool))
    (output : Fin outputLength → Bool) :
    finiteTestOracle test (List.ofFn output) = decide (output ∈ test) := by
  simp [finiteTestOracle, decodeFixedWidthBoolean?_ofFn_internal]

theorem finiteTestOracle_ofFn_eq_true_iff_internal
    {outputLength : ℕ} (test : Finset (Fin outputLength → Bool))
    (output : Fin outputLength → Bool) :
    finiteTestOracle test (List.ofFn output) = true ↔ output ∈ test := by
  simp [finiteTestOracle_ofFn_internal]

theorem finiteTestOracle_eq_false_of_length_ne_internal
    {outputLength : ℕ} (test : Finset (Fin outputLength → Bool))
    {query : List Bool} (hlength : query.length ≠ outputLength) :
    finiteTestOracle test query = false := by
  simp [finiteTestOracle, decodeFixedWidthBoolean?, hlength]

end Complexity
