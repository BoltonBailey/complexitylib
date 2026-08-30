/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.StatisticalTest.Oracle.Defs
public import Complexitylib.Metacomplexity.StatisticalTest.Oracle.Internal

/-!
# Finite statistical tests as Boolean oracles

The canonical oracle accepts exactly the fixed-length strings in a finite
statistical test and rejects every malformed-length query.
-/


public section

namespace Complexity

/-- Fixed-width decoding round-trips a canonical function encoding. -/
@[simp] theorem decodeFixedWidthBoolean?_ofFn
    {length : ℕ} (bits : Fin length → Bool) :
    decodeFixedWidthBoolean? length (List.ofFn bits) = some bits :=
  decodeFixedWidthBoolean?_ofFn_internal bits

/-- The finite-test oracle answers canonical fixed-length queries by test
membership. -/
@[simp] theorem finiteTestOracle_ofFn
    {outputLength : ℕ} (test : Finset (Fin outputLength → Bool))
    (output : Fin outputLength → Bool) :
    finiteTestOracle test (List.ofFn output) = decide (output ∈ test) :=
  finiteTestOracle_ofFn_internal test output

/-- The finite-test oracle returns true exactly on members of the test. -/
theorem finiteTestOracle_ofFn_eq_true_iff
    {outputLength : ℕ} (test : Finset (Fin outputLength → Bool))
    (output : Fin outputLength → Bool) :
    finiteTestOracle test (List.ofFn output) = true ↔ output ∈ test :=
  finiteTestOracle_ofFn_eq_true_iff_internal test output

/-- Every query of the wrong length is rejected. -/
theorem finiteTestOracle_eq_false_of_length_ne
    {outputLength : ℕ} (test : Finset (Fin outputLength → Bool))
    {query : List Bool} (hlength : query.length ≠ outputLength) :
    finiteTestOracle test query = false :=
  finiteTestOracle_eq_false_of_length_ne_internal test hlength

end Complexity
