/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Promise.CircuitSize.Defs
public import Complexitylib.Circuits.BasisHom.Defs
import Complexitylib.Circuits.BasisHom
import Complexitylib.Classes.Promise
import Complexitylib.Classes.PPoly

/-!
# Nonuniform circuit size for promise problems -- proof internals
-/


public section

namespace Complexity

theorem mem_PromiseSIZEWithBasis_iff_internal
    (problem : PromiseProblem) (B : Basis) (bound : ℕ → ℕ) :
    problem ∈ PromiseSIZEWithBasis B bound ↔
      ∃ family : CircuitFamily B,
        problem.SolvedBy family.evalList ∧ family.SizeBoundedBy bound := by
  constructor
  · rintro ⟨completion, ⟨family, hdecides, hbound⟩, hyes, hno⟩
    refine ⟨family, ?_, hbound⟩
    constructor
    · intro x hx
      exact (hdecides.evalList x).mpr (hyes hx)
    · intro x hx
      cases heval : family.evalList x with
      | false => rfl
      | true =>
          have hxCompletion := (hdecides.evalList x).mp heval
          exact (Set.disjoint_left.mp hno hxCompletion hx).elim
  · rintro ⟨family, hsolve, hbound⟩
    refine ⟨family.language, ⟨family, rfl, hbound⟩, ?_, ?_⟩
    · intro x hx
      exact CircuitFamily.mem_language.mpr (hsolve.1 x hx)
    · apply Set.disjoint_left.mpr
      intro x hxCompletion hxNo
      have htrue := CircuitFamily.mem_language.mp hxCompletion
      have hfalse := hsolve.2 x hxNo
      simp [htrue] at hfalse

theorem mem_PromiseSIZE_iff_internal
    (problem : PromiseProblem) (bound : ℕ → ℕ) :
    problem ∈ PromiseSIZE bound ↔
      ∃ family : CircuitFamily Basis.andOr2,
        problem.SolvedBy family.evalList ∧ family.SizeBoundedBy bound := by
  exact mem_PromiseSIZEWithBasis_iff_internal
    problem Basis.andOr2 bound

theorem mem_PromisePPoly_iff_internal (problem : PromiseProblem) :
    problem ∈ PromisePPoly ↔
      ∃ family : CircuitFamily Basis.andOr2,
        problem.SolvedBy family.evalList ∧ family.PolynomialSize := by
  constructor
  · rintro ⟨completion, hcompletion, hyes, hno⟩
    simp only [PPoly, Set.mem_iUnion] at hcompletion
    obtain ⟨p, hcompletion⟩ := hcompletion
    have hproblem : problem ∈ PromiseSIZE (fun n => p.eval n) :=
      ⟨completion, hcompletion, hyes, hno⟩
    obtain ⟨family, hsolve, hbound⟩ :=
      (mem_PromiseSIZE_iff_internal problem (fun n => p.eval n)).mp hproblem
    exact ⟨family, hsolve, p, hbound⟩
  · rintro ⟨family, hsolve, p, hbound⟩
    obtain ⟨completion, hcompletion, hyes, hno⟩ :=
      (mem_PromiseSIZE_iff_internal problem (fun n => p.eval n)).mpr
        ⟨family, hsolve, hbound⟩
    refine ⟨completion, ?_, hyes, hno⟩
    simp only [PPoly, Set.mem_iUnion]
    exact ⟨p, hcompletion⟩

namespace CircuitFamily

theorem SizeBoundedBy.eventuallySizeBoundedBy_internal
    {B : Basis} {family : CircuitFamily B} {bound : ℕ → ℕ}
    (hbound : family.SizeBoundedBy bound) :
    family.EventuallySizeBoundedBy bound := by
  exact Filter.Eventually.of_forall hbound

theorem EventuallySizeBoundedBy.mono_internal
    {B : Basis} {family : CircuitFamily B} {first second : ℕ → ℕ}
    (hbound : family.EventuallySizeBoundedBy first)
    (hle : ∀ n, first n ≤ second n) :
    family.EventuallySizeBoundedBy second := by
  exact hbound.mono fun n hn => hn.trans (hle n)

theorem EventuallySizeBoundedBy.trans_eventually_internal
    {B : Basis} {family : CircuitFamily B} {first second : ℕ → ℕ}
    (hbound : family.EventuallySizeBoundedBy first)
    (hle : ∀ᶠ n in Filter.atTop, first n ≤ second n) :
    family.EventuallySizeBoundedBy second := by
  exact (hbound.and hle).mono fun _ hn => hn.1.trans hn.2

theorem EventuallySizeBoundedBy.polynomialSize_internal
    {B : Basis} {family : CircuitFamily B} {p : Polynomial ℕ}
    (hbound : family.EventuallySizeBoundedBy fun n => p.eval n) :
    family.PolynomialSize := by
  rw [EventuallySizeBoundedBy, Filter.eventually_atTop] at hbound
  obtain ⟨cutoff, hbound⟩ := hbound
  let exceptionSum := ∑ n ∈ Finset.range cutoff, family.size n
  refine ⟨p + Polynomial.C exceptionSum, ?_⟩
  intro n
  simp only [Polynomial.eval_add, Polynomial.eval_C]
  by_cases hn : n < cutoff
  · have hterm : family.size n ≤ exceptionSum := by
      dsimp only [exceptionSum]
      exact Finset.single_le_sum (fun i _ => Nat.zero_le (family.size i))
        (Finset.mem_range.mpr hn)
    exact hterm.trans (Nat.le_add_left exceptionSum (p.eval n))
  · have hlarge : cutoff ≤ n := Nat.le_of_not_gt hn
    exact (hbound n hlarge).trans (Nat.le_add_right (p.eval n) exceptionSum)

end CircuitFamily

theorem PromiseSIZEWithBasis_subset_PromiseEventuallySIZEWithBasis_internal
    (B : Basis) (bound : ℕ → ℕ) :
    PromiseSIZEWithBasis B bound ⊆
      PromiseEventuallySIZEWithBasis B bound := by
  intro problem hproblem
  obtain ⟨family, hsolve, hbound⟩ :=
    (mem_PromiseSIZEWithBasis_iff_internal problem B bound).mp hproblem
  exact ⟨family, hsolve, hbound.eventuallySizeBoundedBy_internal⟩

theorem PromiseSIZE_subset_PromiseEventuallySIZE_internal
    (bound : ℕ → ℕ) :
    PromiseSIZE bound ⊆ PromiseEventuallySIZE bound := by
  exact PromiseSIZEWithBasis_subset_PromiseEventuallySIZEWithBasis_internal
    Basis.andOr2 bound

theorem PromiseSIZEWithBasis_mono_internal
    (B : Basis) {first second : ℕ → ℕ}
    (hle : ∀ n, first n ≤ second n) :
    PromiseSIZEWithBasis B first ⊆ PromiseSIZEWithBasis B second := by
  intro problem hproblem
  obtain ⟨family, hsolve, hbound⟩ :=
    (mem_PromiseSIZEWithBasis_iff_internal problem B first).mp hproblem
  apply (mem_PromiseSIZEWithBasis_iff_internal problem B second).mpr
  exact ⟨family, hsolve, fun n => (hbound n).trans (hle n)⟩

theorem PromiseEventuallySIZEWithBasis_mono_internal
    (B : Basis) {first second : ℕ → ℕ}
    (hle : ∀ n, first n ≤ second n) :
    PromiseEventuallySIZEWithBasis B first ⊆
      PromiseEventuallySIZEWithBasis B second := by
  rintro problem ⟨family, hsolve, hbound⟩
  exact ⟨family, hsolve, hbound.mono_internal hle⟩

theorem PromiseSIZEWithBasis_mapBasis_subset_internal
    {source target : Basis} (hom : Basis.Hom source target)
    (bound : ℕ → ℕ) :
    PromiseSIZEWithBasis source bound ⊆
      PromiseSIZEWithBasis target bound := by
  intro problem hproblem
  obtain ⟨family, hsolve, hbound⟩ :=
    (mem_PromiseSIZEWithBasis_iff_internal
      problem source bound).mp hproblem
  apply (mem_PromiseSIZEWithBasis_iff_internal
    problem target bound).mpr
  have heval : (family.mapBasis hom).evalList = family.evalList := by
    funext input
    unfold CircuitFamily.evalList
    rw [CircuitFamily.function_mapBasis hom family]
  refine ⟨family.mapBasis hom, ?_, ?_⟩
  · simpa only [heval] using hsolve
  · intro length
    rw [show (family.mapBasis hom).size length = family.size length by
      exact congrFun (CircuitFamily.size_mapBasis hom family) length]
    exact hbound length

theorem PromiseEventuallySIZEWithBasis_mapBasis_subset_internal
    {source target : Basis} (hom : Basis.Hom source target)
    (bound : ℕ → ℕ) :
    PromiseEventuallySIZEWithBasis source bound ⊆
      PromiseEventuallySIZEWithBasis target bound := by
  rintro problem ⟨family, hsolve, hbound⟩
  have heval : (family.mapBasis hom).evalList = family.evalList := by
    funext input
    unfold CircuitFamily.evalList
    rw [CircuitFamily.function_mapBasis hom family]
  refine ⟨family.mapBasis hom, ?_, ?_⟩
  · simpa only [heval] using hsolve
  · filter_upwards [hbound] with length hlength
    rw [show (family.mapBasis hom).size length = family.size length by
      exact congrFun (CircuitFamily.size_mapBasis hom family) length]
    exact hlength

theorem PromiseSIZEWithBasis_eq_of_homs_internal
    {first second : Basis}
    (forward : Basis.Hom first second)
    (reverse : Basis.Hom second first) (bound : ℕ → ℕ) :
    PromiseSIZEWithBasis first bound =
      PromiseSIZEWithBasis second bound := by
  apply Set.Subset.antisymm
  · exact PromiseSIZEWithBasis_mapBasis_subset_internal forward bound
  · exact PromiseSIZEWithBasis_mapBasis_subset_internal reverse bound

theorem PromiseEventuallySIZEWithBasis_eq_of_homs_internal
    {first second : Basis}
    (forward : Basis.Hom first second)
    (reverse : Basis.Hom second first) (bound : ℕ → ℕ) :
    PromiseEventuallySIZEWithBasis first bound =
      PromiseEventuallySIZEWithBasis second bound := by
  apply Set.Subset.antisymm
  · exact PromiseEventuallySIZEWithBasis_mapBasis_subset_internal
      forward bound
  · exact PromiseEventuallySIZEWithBasis_mapBasis_subset_internal
      reverse bound

theorem PromiseEventuallySIZE_polynomial_subset_PromisePPoly_internal
    (p : Polynomial ℕ) :
    PromiseEventuallySIZE (fun n => p.eval n) ⊆ PromisePPoly := by
  rintro problem ⟨family, hsolve, hbound⟩
  apply (mem_PromisePPoly_iff_internal problem).mpr
  exact ⟨family, hsolve, hbound.polynomialSize_internal⟩

end Complexity
