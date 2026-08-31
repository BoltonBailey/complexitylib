/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Machine.Defs
public import Complexitylib.Classes.Pairing
public import Complexitylib.Models.TuringMachine.Subroutines.PairValidate.Defs

/-!
# Padded circuit satisfiability -- definitions

A query is the canonical pair of a tagged circuit-family code and an arbitrary
`ruler` string. The ruler's contents are ignored; its length fixes the exact
assignment width. This prevents a serialized circuit from being interpreted at
a different input arity.
-/


@[expose] public section

namespace Complexity

namespace CircuitSAT

/-- A witness has exactly the width advertised by the query's ruler and makes
the query's tagged circuit code evaluate to true. The query uses canonical
pairing syntax; `pairLang Witness` separately validates its outer pair. -/
def Witness (query witness : List Bool) : Prop :=
  query ∈ validPairEncoding ∧
    witness.length = (pairSnd query).length ∧
    pair (pairFst query) witness ∈ CircuitCode.circuitEvalLanguage

/-- Tagged circuit codes having a satisfying assignment of the exact width
specified by their paired ruler string. -/
def language : Language :=
  {query | ∃ witness, Witness query witness}

end CircuitSAT

end Complexity
