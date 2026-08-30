/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Promise.Defs
public import Complexitylib.Classes.PPoly.Defs
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Nonuniform circuit size for promise problems -- definitions

The completion-based lift `PromiseClass (SIZE s)` is the right extensional
meaning of a circuit family solving a promise problem: behavior outside the
promise is arbitrary. This module gives that class a direct name and separately
defines eventual size bounds, so finite exceptional lengths are never hidden in
an asymptotic hardness-magnification statement.
-/


@[expose] public section

namespace Complexity

namespace CircuitFamily

/-- A circuit family satisfies a size bound at every sufficiently large input
length. -/
def EventuallySizeBoundedBy {B : Basis}
    (family : CircuitFamily B) (bound : ℕ → ℕ) : Prop :=
  ∀ᶠ length in Filter.atTop, family.size length ≤ bound length

end CircuitFamily

/-- Promise problems solvable by `B`-circuits within a pointwise size bound. -/
def PromiseSIZEWithBasis (B : Basis) (bound : ℕ → ℕ) :
    Set PromiseProblem :=
  PromiseClass (SIZEWithBasis B bound)

/-- Promise problems solvable by the library's fan-in-two AND/OR circuits within
a pointwise size bound. -/
def PromiseSIZE (bound : ℕ → ℕ) : Set PromiseProblem :=
  PromiseSIZEWithBasis Basis.andOr2 bound

/-- Promise problems with a completion in `P/poly`. -/
def PromisePPoly : Set PromiseProblem :=
  PromiseClass PPoly

/-- Promise problems solved by `B`-circuit families meeting a size bound at all
sufficiently large lengths. -/
def PromiseEventuallySIZEWithBasis (B : Basis) (bound : ℕ → ℕ) :
    Set PromiseProblem :=
  {problem | ∃ family : CircuitFamily B,
    problem.SolvedBy family.evalList ∧
      family.EventuallySizeBoundedBy bound}

/-- Eventual-size promise circuits over the library's fan-in-two AND/OR basis. -/
def PromiseEventuallySIZE (bound : ℕ → ℕ) : Set PromiseProblem :=
  PromiseEventuallySIZEWithBasis Basis.andOr2 bound

end Complexity
