/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Succinct.NP.Defs
public import Complexitylib.Metacomplexity.MCSP.Succinct.NP.Internal

/-!
# SuccinctMCSP witness-class packaging

The complete normalized witness relation has an executable Boolean checker and
is already polynomially balanced. Consequently, a polynomial-time machine for
its paired language makes the relation an FNP relation; the repository's generic
guess-and-verify NTM construction then places `SuccinctMCSP` in `NP`.

Both machine-level premises remain explicit. This module does not identify
ordinary program execution with a proved polynomial-time Turing machine.
-/


public section

namespace Complexity

namespace SuccinctMCSP

/-- The complete Boolean checker decides the normalized raw witness relation. -/
@[simp] theorem verifyRawWitness_eq_true_iff (bits witness : List Bool) :
    verifyRawWitness bits witness = true ↔ RawWitnessRelation bits witness :=
  verifyRawWitness_eq_true_iff_internal bits witness

/-- A polynomial-time paired verifier turns the normalized raw relation into
an FNP relation. -/
theorem rawWitnessRelation_mem_FNP_of_pairLang_mem_P
    (hverifier : pairLang RawWitnessRelation ∈ P) :
    RawWitnessRelation ∈ FNP :=
  rawWitnessRelation_mem_FNP_of_pairLang_mem_P_internal hverifier

/-- Conditional NP packaging for SuccinctMCSP.

The premises isolate the two remaining machine-level obligations: the generic
FNP witness NTM construction and a `P` implementation of the paired executable
checker. -/
theorem mem_NP_of_pairLang_mem_P
    (hwitness : NP.WitnessNTMConstruction)
    (hverifier : pairLang RawWitnessRelation ∈ P) :
    Complexity.SuccinctMCSP ∈ NP :=
  mem_NP_of_pairLang_mem_P_internal hwitness hverifier

end SuccinctMCSP

end Complexity
