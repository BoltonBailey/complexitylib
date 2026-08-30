/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Succinct.Defs

/-!
# Finite anti-checkers -- definitions

An anti-checker for a target function is a finite list of inputs that catches
every circuit up to a chosen size threshold: each such circuit disagrees with
the target on at least one listed input. Lists are the concrete multiset
representation used by the later generator. Repetitions and order are retained
syntactically but do not affect the semantic predicate.

This first layer is for positive arity, matching the hardness-magnification
application. SuccinctMCSP separately gives its zero-arity convention.
-/


@[expose] public section

namespace Complexity

namespace AntiChecker

/-- A circuit agrees with the target on every input in the finite list. -/
def AgreesOn {arity internalGates : ℕ} [NeZero arity]
    (circuit : Circuit Basis.andOr2 arity 1 internalGates)
    (target : BitString arity → Bool)
    (inputs : List (BitString arity)) : Prop :=
  ∀ input ∈ inputs, circuit.eval input 0 = target input

/-- A finite list is an anti-checker when it contains a counterexample to every
circuit within the threshold. -/
def IsFor {arity : ℕ} [NeZero arity]
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity)) : Prop :=
  ∀ (internalGates : ℕ)
      (circuit : Circuit Basis.andOr2 arity 1 internalGates),
    circuit.size ≤ threshold →
      ∃ input ∈ inputs, circuit.eval input 0 ≠ target input

end AntiChecker

end Complexity
