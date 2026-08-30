/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Promise.Defs
public import Complexitylib.Classes.Promise.Internal

/-!
# Promise problems

This module exposes disjoint yes/no promise problems, semantic Boolean solvers,
side-preserving maps, polynomial-time many-one reductions, complements, and the
total embedding of ordinary languages.
-/


public section

namespace Complexity

namespace PromiseProblem

/-- A promised yes-instance cannot also be a promised no-instance. -/
theorem not_mem_no_of_mem_yes (problem : PromiseProblem)
    {x : List Bool} (hyes : x ∈ problem.yesInstances) :
    x ∉ problem.noInstances :=
  not_mem_no_of_mem_yes_internal problem hyes

/-- A promised no-instance cannot also be a promised yes-instance. -/
theorem not_mem_yes_of_mem_no (problem : PromiseProblem)
    {x : List Bool} (hno : x ∈ problem.noInstances) :
    x ∉ problem.yesInstances :=
  not_mem_yes_of_mem_no_internal problem hno

/-- The promise is exactly the union of the two constrained sides. -/
theorem mem_promise_iff (problem : PromiseProblem) (x : List Bool) :
    x ∈ problem.promise ↔
      x ∈ problem.yesInstances ∨ x ∈ problem.noInstances :=
  mem_promise_iff_internal problem x

/-- Complementing a promise problem twice recovers it. -/
@[simp] theorem complement_complement (problem : PromiseProblem) :
    problem.complement.complement = problem :=
  complement_complement_internal problem

/-- Complementing a problem does not change its promised input set. -/
@[simp] theorem promise_complement (problem : PromiseProblem) :
    problem.complement.promise = problem.promise :=
  promise_complement_internal problem

/-- Solving the complemented promise is equivalent to complementing the
Boolean output of a solver for the original problem. -/
theorem solvedBy_complement_iff (problem : PromiseProblem)
    (decide : List Bool → Bool) :
    problem.complement.SolvedBy decide ↔
      problem.SolvedBy (fun x => !(decide x)) :=
  solvedBy_complement_iff_internal problem decide

/-- The ordinary-language embedding promises every input. -/
@[simp] theorem promise_ofLanguage (L : Language) :
    (ofLanguage L).promise = Set.univ :=
  promise_ofLanguage_internal L

/-- Solving an embedded ordinary language is exactly deciding it everywhere. -/
theorem solvedBy_ofLanguage_iff (L : Language)
    (decide : List Bool → Bool) :
    (ofLanguage L).SolvedBy decide ↔
      ∀ x, decide x = true ↔ x ∈ L :=
  solvedBy_ofLanguage_iff_internal L decide

/-- Identity preserves both sides of every promise problem. -/
theorem mapReducesVia_refl (problem : PromiseProblem) :
    problem.MapReducesVia problem id :=
  mapReducesVia_refl_internal problem

/-- Side-preserving maps compose. -/
theorem MapReducesVia.trans {first second third : PromiseProblem}
    {f g : List Bool → List Bool}
    (hfirst : first.MapReducesVia second f)
    (hsecond : second.MapReducesVia third g) :
    first.MapReducesVia third (g ∘ f) :=
  hfirst.trans_internal hsecond

/-- Polynomial-time promise reducibility is reflexive. -/
theorem mapReducesPoly_refl (problem : PromiseProblem) :
    problem.MapReducesPoly problem :=
  mapReducesPoly_refl_internal problem

/-- Polynomial-time promise reductions compose. -/
theorem MapReducesPoly.trans {first second third : PromiseProblem}
    (hfirst : first.MapReducesPoly second)
    (hsecond : second.MapReducesPoly third) :
    first.MapReducesPoly third :=
  hfirst.trans_internal hsecond

/-- On total embedded languages, preserving both promised sides is equivalent
to the usual membership equivalence. -/
theorem mapReducesVia_ofLanguage_iff (first second : Language)
    (f : List Bool → List Bool) :
    (ofLanguage first).MapReducesVia (ofLanguage second) f ↔
      ∀ x, x ∈ first ↔ f x ∈ second :=
  mapReducesVia_ofLanguage_iff_internal first second f

end PromiseProblem

end Complexity
