/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Promise.CircuitSize.Defs
public import Complexitylib.Classes.Promise.CircuitSize.Internal
public import Complexitylib.Classes.Promise
public import Complexitylib.Classes.PPoly
public import Complexitylib.Circuits.BasisHom

/-!
# Nonuniform circuit size for promise problems

This module proves that completion-based promise `SIZE` is exactly explicit
circuit-family solvability on the promised sides. It also distinguishes
pointwise from eventual size bounds and proves that finitely many exceptional
lengths do not affect polynomial-size promise circuits.
-/


public section

namespace Complexity

/-- Completion-based promise `SIZE` is equivalent to one explicit circuit
family that solves both promised sides and meets the pointwise bound. -/
theorem mem_PromiseSIZEWithBasis_iff
    (problem : PromiseProblem) (B : Basis) (bound : ℕ → ℕ) :
    problem ∈ PromiseSIZEWithBasis B bound ↔
      ∃ family : CircuitFamily B,
        problem.SolvedBy family.evalList ∧ family.SizeBoundedBy bound :=
  mem_PromiseSIZEWithBasis_iff_internal problem B bound

/-- Specialized explicit-solver characterization over `Basis.andOr2`. -/
theorem mem_PromiseSIZE_iff
    (problem : PromiseProblem) (bound : ℕ → ℕ) :
    problem ∈ PromiseSIZE bound ↔
      ∃ family : CircuitFamily Basis.andOr2,
        problem.SolvedBy family.evalList ∧ family.SizeBoundedBy bound :=
  mem_PromiseSIZE_iff_internal problem bound

/-- A promise has a `P/poly` completion exactly when one polynomial-size circuit
family solves both promised sides. -/
theorem mem_PromisePPoly_iff (problem : PromiseProblem) :
    problem ∈ PromisePPoly ↔
      ∃ family : CircuitFamily Basis.andOr2,
        problem.SolvedBy family.evalList ∧ family.PolynomialSize :=
  mem_PromisePPoly_iff_internal problem

namespace CircuitFamily

/-- A pointwise size bound is also an eventual size bound. -/
theorem SizeBoundedBy.eventuallySizeBoundedBy
    {B : Basis} {family : CircuitFamily B} {bound : ℕ → ℕ}
    (hbound : family.SizeBoundedBy bound) :
    family.EventuallySizeBoundedBy bound :=
  hbound.eventuallySizeBoundedBy_internal

/-- An eventual size bound is monotone under pointwise enlargement. -/
theorem EventuallySizeBoundedBy.mono
    {B : Basis} {family : CircuitFamily B} {first second : ℕ → ℕ}
    (hbound : family.EventuallySizeBoundedBy first)
    (hle : ∀ n, first n ≤ second n) :
    family.EventuallySizeBoundedBy second :=
  hbound.mono_internal hle

/-- An eventual size bound composes with an eventually valid comparison. -/
theorem EventuallySizeBoundedBy.trans_eventually
    {B : Basis} {family : CircuitFamily B} {first second : ℕ → ℕ}
    (hbound : family.EventuallySizeBoundedBy first)
    (hle : ∀ᶠ n in Filter.atTop, first n ≤ second n) :
    family.EventuallySizeBoundedBy second :=
  hbound.trans_eventually_internal hle

/-- A polynomial bound outside a finite prefix can be enlarged by a constant
polynomial to cover every length. -/
theorem EventuallySizeBoundedBy.polynomialSize
    {B : Basis} {family : CircuitFamily B} {p : Polynomial ℕ}
    (hbound : family.EventuallySizeBoundedBy fun n => p.eval n) :
    family.PolynomialSize :=
  hbound.polynomialSize_internal

end CircuitFamily

/-- Pointwise promise size is contained in eventual promise size over any
basis. -/
theorem PromiseSIZEWithBasis_subset_PromiseEventuallySIZEWithBasis
    (B : Basis) (bound : ℕ → ℕ) :
    PromiseSIZEWithBasis B bound ⊆
      PromiseEventuallySIZEWithBasis B bound :=
  PromiseSIZEWithBasis_subset_PromiseEventuallySIZEWithBasis_internal B bound

/-- Pointwise promise size is contained in eventual promise size. -/
theorem PromiseSIZE_subset_PromiseEventuallySIZE (bound : ℕ → ℕ) :
    PromiseSIZE bound ⊆ PromiseEventuallySIZE bound :=
  PromiseSIZE_subset_PromiseEventuallySIZE_internal bound

/-- Pointwise promise `SIZE` is monotone in its bound. -/
theorem PromiseSIZEWithBasis_mono
    (B : Basis) {first second : ℕ → ℕ}
    (hle : ∀ n, first n ≤ second n) :
    PromiseSIZEWithBasis B first ⊆ PromiseSIZEWithBasis B second :=
  PromiseSIZEWithBasis_mono_internal B hle

/-- Eventual promise `SIZE` is monotone in its bound. -/
theorem PromiseEventuallySIZEWithBasis_mono
    (B : Basis) {first second : ℕ → ℕ}
    (hle : ∀ n, first n ≤ second n) :
    PromiseEventuallySIZEWithBasis B first ⊆
      PromiseEventuallySIZEWithBasis B second :=
  PromiseEventuallySIZEWithBasis_mono_internal B hle

/-- Exact semantics-preserving basis relabeling preserves pointwise promise
circuit size with no overhead. -/
theorem PromiseSIZEWithBasis_mapBasis_subset
    {source target : Basis} (hom : Basis.Hom source target)
    (bound : ℕ → ℕ) :
    PromiseSIZEWithBasis source bound ⊆
      PromiseSIZEWithBasis target bound :=
  PromiseSIZEWithBasis_mapBasis_subset_internal hom bound

/-- Exact semantics-preserving basis relabeling preserves eventual promise
circuit size with no overhead. -/
theorem PromiseEventuallySIZEWithBasis_mapBasis_subset
    {source target : Basis} (hom : Basis.Hom source target)
    (bound : ℕ → ℕ) :
    PromiseEventuallySIZEWithBasis source bound ⊆
      PromiseEventuallySIZEWithBasis target bound :=
  PromiseEventuallySIZEWithBasis_mapBasis_subset_internal hom bound

/-- Bases admitting exact semantics-preserving relabelings in both directions
give the same pointwise promise-size class at every bound. -/
theorem PromiseSIZEWithBasis_eq_of_homs
    {first second : Basis}
    (forward : Basis.Hom first second)
    (reverse : Basis.Hom second first) (bound : ℕ → ℕ) :
    PromiseSIZEWithBasis first bound =
      PromiseSIZEWithBasis second bound :=
  PromiseSIZEWithBasis_eq_of_homs_internal forward reverse bound

/-- Bases admitting exact semantics-preserving relabelings in both directions
give the same eventual promise-size class at every bound. -/
theorem PromiseEventuallySIZEWithBasis_eq_of_homs
    {first second : Basis}
    (forward : Basis.Hom first second)
    (reverse : Basis.Hom second first) (bound : ℕ → ℕ) :
    PromiseEventuallySIZEWithBasis first bound =
      PromiseEventuallySIZEWithBasis second bound :=
  PromiseEventuallySIZEWithBasis_eq_of_homs_internal
    forward reverse bound

/-- Finitely many exceptional lengths do not prevent a polynomially bounded
promise solver from giving a `P/poly` completion. -/
theorem PromiseEventuallySIZE_polynomial_subset_PromisePPoly
    (p : Polynomial ℕ) :
    PromiseEventuallySIZE (fun n => p.eval n) ⊆ PromisePPoly :=
  PromiseEventuallySIZE_polynomial_subset_PromisePPoly_internal p

/-- The promise-size lift agrees with ordinary `SIZE` on total languages. -/
theorem ofLanguage_mem_PromiseSIZE_iff (L : Language) (bound : ℕ → ℕ) :
    PromiseProblem.ofLanguage L ∈ PromiseSIZE bound ↔ L ∈ SIZE bound := by
  exact PromiseProblem.ofLanguage_mem_promiseClass_iff (SIZE bound) L

/-- The promise-`P/poly` lift agrees with ordinary `P/poly` on total languages. -/
theorem ofLanguage_mem_PromisePPoly_iff (L : Language) :
    PromiseProblem.ofLanguage L ∈ PromisePPoly ↔ L ∈ PPoly := by
  exact PromiseProblem.ofLanguage_mem_promiseClass_iff PPoly L

end Complexity
