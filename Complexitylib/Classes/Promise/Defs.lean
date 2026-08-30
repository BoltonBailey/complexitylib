/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.NP

/-!
# Promise problems -- definitions

A promise problem has disjoint yes- and no-instance languages. Inputs outside
their union are unconstrained. This module keeps semantic solvers, explicit
side-preserving maps, and polynomial-time many-one reductions separate.

Ordinary languages embed as total promise problems with no-instances equal to
the complement. Gap problems should use `PromiseProblem` directly rather than
arbitrarily assigning the gap region to one side.
-/


@[expose] public section

namespace Complexity

/-- A decision promise consisting of disjoint yes- and no-instance languages. -/
structure PromiseProblem where
  /-- Inputs on which a solver must answer yes. -/
  yesInstances : Language
  /-- Inputs on which a solver must answer no. -/
  noInstances : Language
  /-- No input receives conflicting promised answers. -/
  disjoint : Disjoint yesInstances noInstances

namespace PromiseProblem

/-- The set of inputs on which the problem constrains a solver. -/
def promise (problem : PromiseProblem) : Language :=
  problem.yesInstances ∪ problem.noInstances

/-- A Boolean function solves a promise problem when it gives the required
answer on both promised sides. Its behavior outside the promise is arbitrary. -/
def SolvedBy (problem : PromiseProblem) (decide : List Bool → Bool) : Prop :=
  (∀ x ∈ problem.yesInstances, decide x = true) ∧
    ∀ x ∈ problem.noInstances, decide x = false

/-- An explicit map preserves both sides of a promise reduction. -/
def MapReducesVia (source target : PromiseProblem)
    (f : List Bool → List Bool) : Prop :=
  (∀ x ∈ source.yesInstances, f x ∈ target.yesInstances) ∧
    ∀ x ∈ source.noInstances, f x ∈ target.noInstances

/-- Polynomial-time many-one reduction between promise problems. -/
def MapReducesPoly (source target : PromiseProblem) : Prop :=
  ∃ f : List Bool → List Bool, f ∈ FP ∧ source.MapReducesVia target f

/-- Swap the promised yes and no sides. -/
def complement (problem : PromiseProblem) : PromiseProblem where
  yesInstances := problem.noInstances
  noInstances := problem.yesInstances
  disjoint := problem.disjoint.symm

/-- Regard an ordinary language as a total promise problem. -/
def ofLanguage (L : Language) : PromiseProblem where
  yesInstances := L
  noInstances := Lᶜ
  disjoint := disjoint_compl_right

end PromiseProblem

/-- Lift a language class to promise problems by total completions. A promise
problem belongs to `PromiseClass C` when some language in `C` contains every
yes-instance and no no-instance. Behavior outside the promise is unrestricted. -/
def PromiseClass (C : Set Language) : Set PromiseProblem :=
  {problem | ∃ completion : Language,
    completion ∈ C ∧
      problem.yesInstances ⊆ completion ∧
      Disjoint completion problem.noInstances}

/-- Promise problems admitting a deterministic polynomial-time completion. -/
def PromiseP : Set PromiseProblem :=
  PromiseClass P

/-- Promise problems admitting a nondeterministic polynomial-time completion. -/
def PromiseNP : Set PromiseProblem :=
  PromiseClass NP

/-- Promise problems admitting a coNP completion. -/
def PromiseCoNP : Set PromiseProblem :=
  PromiseClass coNP

/-- A promise problem is hard for a language class when every total language
in the class reduces to it by a side-preserving polynomial-time map. -/
def PromiseHardFor (C : Set Language) (target : PromiseProblem) : Prop :=
  ∀ L ∈ C, (PromiseProblem.ofLanguage L).MapReducesPoly target

/-- A promise problem is complete for a language class when it belongs to the
completion-based promise lift and is hard for every total language in the
class. -/
def PromiseCompleteFor (C : Set Language) (target : PromiseProblem) : Prop :=
  target ∈ PromiseClass C ∧ PromiseHardFor C target

/-- Polynomial-time side-preserving NP-hardness for a promise target. -/
def PromiseNPHard (target : PromiseProblem) : Prop :=
  PromiseHardFor NP target

/-- Completeness for `PromiseNP` under side-preserving polynomial reductions. -/
def PromiseNPComplete (target : PromiseProblem) : Prop :=
  PromiseCompleteFor NP target

end Complexity
