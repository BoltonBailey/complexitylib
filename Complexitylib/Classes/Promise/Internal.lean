/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Promise.Defs
import Complexitylib.Classes.P
import Complexitylib.Classes.NP.Closure
import Complexitylib.Classes.Containments

/-!
# Promise problems -- proof internals

Elementary set, solver, complement, and reduction laws supporting the public
promise-problem interface.
-/


public section

namespace Complexity

namespace PromiseProblem

theorem not_mem_no_of_mem_yes_internal (problem : PromiseProblem)
    {x : List Bool} (hyes : x ∈ problem.yesInstances) :
    x ∉ problem.noInstances := by
  exact Set.disjoint_left.mp problem.disjoint hyes

theorem not_mem_yes_of_mem_no_internal (problem : PromiseProblem)
    {x : List Bool} (hno : x ∈ problem.noInstances) :
    x ∉ problem.yesInstances := by
  exact Set.disjoint_left.mp problem.disjoint.symm hno

theorem mem_promise_iff_internal (problem : PromiseProblem) (x : List Bool) :
    x ∈ problem.promise ↔
      x ∈ problem.yesInstances ∨ x ∈ problem.noInstances := by
  rfl

theorem complement_complement_internal (problem : PromiseProblem) :
    problem.complement.complement = problem := by
  cases problem
  rfl

theorem promise_complement_internal (problem : PromiseProblem) :
    problem.complement.promise = problem.promise := by
  ext x
  simp only [promise, complement, Set.mem_union]
  exact or_comm

theorem solvedBy_complement_iff_internal (problem : PromiseProblem)
    (decide : List Bool → Bool) :
    problem.complement.SolvedBy decide ↔
      problem.SolvedBy (fun x => !(decide x)) := by
  constructor
  · rintro ⟨hyes, hno⟩
    constructor
    · intro x hx
      simpa using hno x hx
    · intro x hx
      simpa using hyes x hx
  · rintro ⟨hyes, hno⟩
    constructor
    · intro x hx
      have := hno x hx
      simpa using this
    · intro x hx
      have := hyes x hx
      simpa using this

theorem promise_ofLanguage_internal (L : Language) :
    (ofLanguage L).promise = Set.univ := by
  exact Set.union_compl_self L

theorem solvedBy_ofLanguage_iff_internal (L : Language)
    (decide : List Bool → Bool) :
    (ofLanguage L).SolvedBy decide ↔
      ∀ x, decide x = true ↔ x ∈ L := by
  constructor
  · rintro ⟨hyes, hno⟩ x
    constructor
    · intro hdecide
      by_contra hx
      have hfalse := hno x hx
      simp [hdecide] at hfalse
    · exact hyes x
  · intro hdecide
    constructor
    · intro x hx
      exact (hdecide x).mpr hx
    · intro x hx
      cases h : decide x
      · rfl
      · exact (hx ((hdecide x).mp h)).elim

theorem mapReducesVia_refl_internal (problem : PromiseProblem) :
    problem.MapReducesVia problem id := by
  exact ⟨fun _x hx => hx, fun _x hx => hx⟩

theorem MapReducesVia.trans_internal {first second third : PromiseProblem}
    {f g : List Bool → List Bool}
    (hfirst : first.MapReducesVia second f)
    (hsecond : second.MapReducesVia third g) :
    first.MapReducesVia third (g ∘ f) := by
  constructor
  · intro x hx
    exact hsecond.1 (f x) (hfirst.1 x hx)
  · intro x hx
    exact hsecond.2 (f x) (hfirst.2 x hx)

theorem mapReducesPoly_refl_internal (problem : PromiseProblem) :
    problem.MapReducesPoly problem :=
  ⟨id, id_mem_FP, mapReducesVia_refl_internal problem⟩

theorem MapReducesPoly.trans_internal {first second third : PromiseProblem}
    (hfirst : first.MapReducesPoly second)
    (hsecond : second.MapReducesPoly third) :
    first.MapReducesPoly third := by
  obtain ⟨f, hf, hfred⟩ := hfirst
  obtain ⟨g, hg, hgred⟩ := hsecond
  exact ⟨g ∘ f, mem_FP_comp hf hg, hfred.trans_internal hgred⟩

theorem mapReducesVia_ofLanguage_iff_internal (first second : Language)
    (f : List Bool → List Bool) :
    (ofLanguage first).MapReducesVia (ofLanguage second) f ↔
      ∀ x, x ∈ first ↔ f x ∈ second := by
  constructor
  · rintro ⟨hyes, hno⟩ x
    constructor
    · exact hyes x
    · intro hx
      by_contra hfirst
      exact hno x hfirst hx
  · intro hiff
    constructor
    · intro x hx
      exact (hiff x).mp hx
    · intro x hx hsecond
      exact hx ((hiff x).mpr hsecond)

theorem MapReducesPoly.mem_promiseClass_internal
    {C : Set Language} {source target : PromiseProblem}
    (hpreimage : ∀ {f : List Bool → List Bool} {L : Language},
      f ∈ FP → L ∈ C → f ⁻¹' L ∈ C)
    (hred : source.MapReducesPoly target)
    (htarget : target ∈ PromiseClass C) :
    source ∈ PromiseClass C := by
  obtain ⟨f, hf, hmap⟩ := hred
  obtain ⟨completion, hcompletion, hyes, hno⟩ := htarget
  refine ⟨f ⁻¹' completion, hpreimage hf hcompletion, ?_, ?_⟩
  · intro x hx
    exact hyes (hmap.1 x hx)
  · apply Set.disjoint_left.mpr
    intro x hxCompletion hxNo
    exact Set.disjoint_left.mp hno hxCompletion (hmap.2 x hxNo)

theorem MapReducesPoly.mem_PromiseP_internal
    {source target : PromiseProblem}
    (hred : source.MapReducesPoly target) (htarget : target ∈ PromiseP) :
    source ∈ PromiseP :=
  hred.mem_promiseClass_internal
    (fun hf hL => mem_P_preimage hf hL) htarget

theorem MapReducesPoly.mem_PromiseNP_internal
    {source target : PromiseProblem}
    (hred : source.MapReducesPoly target) (htarget : target ∈ PromiseNP) :
    source ∈ PromiseNP :=
  hred.mem_promiseClass_internal
    (fun hf hL => mem_NP_preimage hf hL) htarget

end PromiseProblem

theorem promiseClass_mono_internal {C D : Set Language} (hsubset : C ⊆ D) :
    PromiseClass C ⊆ PromiseClass D := by
  rintro problem ⟨completion, hcompletion, hyes, hno⟩
  exact ⟨completion, hsubset hcompletion, hyes, hno⟩

theorem ofLanguage_mem_promiseClass_iff_internal
    (C : Set Language) (L : Language) :
    PromiseProblem.ofLanguage L ∈ PromiseClass C ↔ L ∈ C := by
  constructor
  · rintro ⟨completion, hcompletion, hyes, hno⟩
    have heq : completion = L := by
      apply Set.Subset.antisymm
      · intro x hx
        by_contra hxL
        exact Set.disjoint_left.mp hno hx hxL
      · exact hyes
    rwa [heq] at hcompletion
  · intro hL
    exact ⟨L, hL, fun _ hx => hx, disjoint_compl_right⟩

theorem PromiseP_subset_PromiseNP_internal : PromiseP ⊆ PromiseNP :=
  promiseClass_mono_internal P_subset_NP

theorem PromiseP_complement_internal {problem : PromiseProblem}
    (hproblem : problem ∈ PromiseP) :
    problem.complement ∈ PromiseP := by
  obtain ⟨completion, hcompletion, hyes, hno⟩ := hproblem
  refine ⟨completionᶜ, P_compl hcompletion, ?_, ?_⟩
  · intro x hxNo hxCompletion
    exact Set.disjoint_left.mp hno hxCompletion hxNo
  · apply Set.disjoint_left.mpr
    intro x hxComplement hxYes
    exact hxComplement (hyes hxYes)

end Complexity
