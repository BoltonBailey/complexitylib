/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.StatisticalTest.Defs
public import Complexitylib.Models.TuringMachine.Oracle.Defs

/-!
# Finite statistical tests as Boolean oracles -- definitions

A fixed-length finite test is extended to all binary query strings by rejecting
malformed lengths. This supplies the canonical oracle used by reconstruction
decoders without placing the test's exponentially long truth table inside the
program description.
-/


@[expose] public section

namespace Complexity

/-- Decode a list only when it has exactly the advertised fixed length. -/
def decodeFixedWidthBoolean? (length : ℕ) (bits : List Bool) :
    Option (Fin length → Bool) :=
  if hlength : bits.length = length then
    some fun index => bits.get ⟨index.val, by rw [hlength]; exact index.isLt⟩
  else
    none

/-- Canonical total Boolean oracle associated to a finite fixed-length test.
Queries of the wrong length are rejected. -/
def finiteTestOracle {outputLength : ℕ}
    (test : Finset (Fin outputLength → Bool)) : BooleanOracle :=
  fun query =>
    match decodeFixedWidthBoolean? outputLength query with
    | some output => decide (output ∈ test)
    | none => false

end Complexity
