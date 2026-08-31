/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.SAT.CircuitSatisfiability.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.NP
import Complexitylib.SAT.CircuitSatisfiability.Internal

/-!
# Padded circuit satisfiability

The ruler in a query fixes the exact satisfying-assignment width. The resulting
language belongs to `NP`, using the verified serialized circuit evaluator as
its deterministic witness checker.
-/


public section

namespace Complexity

namespace CircuitSAT

/-- On a canonical query, witnesses have the ruler's exact width and make the
tagged circuit code evaluate to true. -/
theorem witness_pair_iff (code ruler witness : List Bool) :
    Witness (pair code ruler) witness ↔
      witness.length = ruler.length ∧
        CircuitCode.evalFamilyCode code witness = some true :=
  witness_pair_iff_internal code ruler witness

/-- A canonical padded circuit query is accepted exactly when it has a
satisfying assignment of the ruler's exact width. -/
theorem pair_mem_language_iff (code ruler : List Bool) :
    pair code ruler ∈ language ↔
      ∃ witness, witness.length = ruler.length ∧
        CircuitCode.evalFamilyCode code witness = some true :=
  pair_mem_language_iff_internal code ruler

/-- Every valid circuit-satisfiability witness is linearly bounded by its
query length. -/
theorem witness_length_le (query witness : List Bool)
    (h : Witness query witness) :
    witness.length ≤ query.length + 1 :=
  witness_length_le_internal query witness h

/-- The paired verifier language is polynomial-time decidable. -/
theorem pairLang_witness_mem_P : pairLang Witness ∈ P :=
  pairLang_witness_mem_P_internal

/-- Padded circuit satisfiability belongs to `NP`. -/
theorem language_mem_NP : language ∈ NP :=
  language_mem_NP_internal

/-- On a canonical extension query, witnesses have the ruler's exact width
and make the circuit accept when appended to the fixed public prefix. -/
theorem extensionWitness_pair_iff
    (code fixedPrefix ruler witness : List Bool) :
    ExtensionWitness (pair code (pair fixedPrefix ruler)) witness ↔
      witness.length = ruler.length ∧
        CircuitCode.evalFamilyCode code (fixedPrefix ++ witness) = some true :=
  extensionWitness_pair_iff_internal code fixedPrefix ruler witness

/-- A canonical extension query is accepted exactly when the circuit has an
accepting suffix of the ruler's exact width. -/
theorem pair_mem_extensionLanguage_iff
    (code fixedPrefix ruler : List Bool) :
    pair code (pair fixedPrefix ruler) ∈ extensionLanguage ↔
      ∃ witness, witness.length = ruler.length ∧
        CircuitCode.evalFamilyCode code (fixedPrefix ++ witness) = some true :=
  pair_mem_extensionLanguage_iff_internal code fixedPrefix ruler

/-- Every valid extension witness is linearly bounded by its query length. -/
theorem extensionWitness_length_le (query witness : List Bool)
    (h : ExtensionWitness query witness) :
    witness.length ≤ query.length + 1 :=
  extensionWitness_length_le_internal query witness h

/-- The paired extension verifier language is polynomial-time decidable. -/
theorem pairLang_extensionWitness_mem_P : pairLang ExtensionWitness ∈ P :=
  pairLang_extensionWitness_mem_P_internal

/-- Exact-width existential circuit extension belongs to `NP`. -/
theorem extensionLanguage_mem_NP : extensionLanguage ∈ NP :=
  extensionLanguage_mem_NP_internal

end CircuitSAT

end Complexity
