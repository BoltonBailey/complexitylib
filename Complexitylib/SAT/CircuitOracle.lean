/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Oracle
public import Complexitylib.Classes.PPoly.Oracle.Inlining
public import Complexitylib.SAT.Headline

/-!
# SAT circuit oracles from `NP ⊆ P/poly`

This module extracts the exact polynomial-size SAT circuit family needed to
replace SAT-oracle calls in a nonuniform computation. Fixed-round adaptive
programs may have a different positive query width at each round; the selected
family members inline every call into one ordinary circuit.
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

/-- Under `NP ⊆ PPoly`, every fixed-round adaptive SAT-oracle circuit program
has a polynomial circuit oracle whose width-selected family members inline to
an ordinary circuit with exactly the same output.

This theorem performs circuit-level oracle replacement. It does not assert
that an arbitrary oracle Turing machine has already been compiled into an
`AdaptiveOracleProgram`. -/
theorem exists_inlinedCircuitOracle_of_NP_subset_PPoly
    (hNP : NP ⊆ PPoly)
    {inputWidth outputWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (program : AdaptiveOracleProgram inputWidth outputWidth rounds) :
    ∃ circuitOracle : PolynomialCircuitOracle language,
      circuitOracle.oracle.Decides language ∧
        ∀ input,
          (program.inlineCircuitOracle circuitOracle).2.eval input =
            program.eval circuitOracle.oracle input := by
  obtain ⟨circuitOracle⟩ :=
    exists_polynomialCircuitOracle_of_NP_subset_PPoly hNP
  exact ⟨circuitOracle, circuitOracle.oracle_decides,
    program.inlineCircuitOracle_eval circuitOracle⟩

end SAT

end Complexity
