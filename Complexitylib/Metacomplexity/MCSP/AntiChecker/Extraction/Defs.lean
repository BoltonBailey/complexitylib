/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Defs

/-!
# Finite anti-checker extraction -- definitions

This layer tracks a finite set of machine-facing circuit descriptions that are
still consistent with all sampled target values. It is deliberately generic in
the initial code set: later enumeration or approximate-counting arguments can
supply the candidates and prove that they cover every small typed circuit.
-/


@[expose] public section

namespace Complexity

namespace AntiChecker

/-- One encoded circuit agrees with the target at one typed input. Malformed or
non-evaluating codes do not agree. -/
def CodeAgreesAt {arity : ℕ} (target : BitString arity → Bool)
    (code : List Bool) (input : BitString arity) : Prop :=
  CircuitCode.evalCode arity code input.toList = some (target input)

instance {arity : ℕ} (target : BitString arity → Bool)
    (code : List Bool) (input : BitString arity) :
    Decidable (CodeAgreesAt target code input) := by
  unfold CodeAgreesAt
  exact inferInstance

/-- A code is consistent with every target-labelled input in the list. -/
def ConsistentCode {arity : ℕ} (target : BitString arity → Bool)
    (inputs : List (BitString arity)) (code : List Bool) : Prop :=
  inputs.Forall (CodeAgreesAt target code)

instance {arity : ℕ} (target : BitString arity → Bool)
    (inputs : List (BitString arity)) (code : List Bool) :
    Decidable (ConsistentCode target inputs code) := by
  unfold ConsistentCode
  exact inferInstance

/-- Candidate circuit codes surviving every sampled target value. -/
def ConsistentCodes {arity : ℕ} (target : BitString arity → Bool)
    (inputs : List (BitString arity)) (codes : Finset (List Bool)) :
    Finset (List Bool) :=
  codes.filter (ConsistentCode target inputs)

/-- The finite code set contains the canonical encoding of every typed circuit
within the size threshold. -/
def CoversThreshold {arity : ℕ} [NeZero arity] (threshold : ℕ)
    (codes : Finset (List Bool)) : Prop :=
  ∀ (internalGates : ℕ)
      (circuit : Circuit Basis.andOr2 arity 1 internalGates),
    circuit.size ≤ threshold → CircuitCode.encodeCircuit circuit ∈ codes

/-- Every candidate code disagrees with the target on some input. -/
def AllFailSomewhere {arity : ℕ} (target : BitString arity → Bool)
    (codes : Finset (List Bool)) : Prop :=
  ∀ code ∈ codes, ∃ input, ¬ CodeAgreesAt target code input

end AntiChecker

end Complexity
