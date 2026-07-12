/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.DescriptiveComplexity.Query
import Complexitylib.DescriptiveComplexity.FirstOrder

/-!
# First-order definable queries

A Boolean query is **first-order definable** when some FO sentence defines it. The
central fact of descriptive complexity — that a logic can only define
"legitimate" (order-independent) queries — is recorded here for first-order logic:
every FO-definable query is order-independent (`FODefinable.orderIndependent`, a
packaging of Immerman Proposition 1.16). Since FO has `¬`, `∧`, `∨`, the
FO-definable queries are closed under complement, intersection, and union.

This is the template for the logic/complexity correspondences on track L6: a class
of logics defines a class of queries, and expressibility questions become lower
bounds.

## Main definitions and results

- `DescriptiveComplexity.FODefinable` — first-order definability of a query.
- `DescriptiveComplexity.FODefinable.orderIndependent` — FO-definable ⟹
  order-independent.
- `FODefinable.complement`, `.inter`, `.union` — Boolean closure.
-/

open scoped Complexity.DescriptiveComplexity

namespace Complexity

namespace DescriptiveComplexity

variable {V : Vocabulary}

/-- A Boolean query is **first-order definable** if some FO sentence defines it. -/
def FODefinable (Q : BooleanQuery V) : Prop :=
  ∃ φ : Sentence V, ∀ A : FinStruct V, Q A ↔ (A ⊨ φ)

/-- **FO-definable queries are order-independent** (Immerman Proposition 1.16,
    packaged): a query defined by an FO sentence cannot distinguish isomorphic
    structures. -/
theorem FODefinable.orderIndependent {Q : BooleanQuery V} (hQ : FODefinable Q) :
    Q.IsOrderIndependent := by
  obtain ⟨φ, hφ⟩ := hQ
  intro A B hiso
  rw [hφ A, hφ B]
  exact Sentence.orderIndependent φ hiso

/-- FO-definable queries are closed under complement (via `¬`). -/
theorem FODefinable.complement {Q : BooleanQuery V} (hQ : FODefinable Q) :
    FODefinable Q.complement := by
  obtain ⟨φ, hφ⟩ := hQ
  exact ⟨φ.neg, fun A => by
    simp only [BooleanQuery.complement, hφ A, Sentence.Models, Formula.Sat]⟩

/-- FO-definable queries are closed under intersection (via `∧`). -/
theorem FODefinable.inter {Q₁ Q₂ : BooleanQuery V}
    (h₁ : FODefinable Q₁) (h₂ : FODefinable Q₂) : FODefinable (Q₁.inter Q₂) := by
  obtain ⟨φ, hφ⟩ := h₁
  obtain ⟨ψ, hψ⟩ := h₂
  exact ⟨φ.conj ψ, fun A => by
    simp only [BooleanQuery.inter, hφ A, hψ A, Sentence.Models, Formula.Sat]⟩

/-- FO-definable queries are closed under union (via `∨`). -/
theorem FODefinable.union {Q₁ Q₂ : BooleanQuery V}
    (h₁ : FODefinable Q₁) (h₂ : FODefinable Q₂) : FODefinable (Q₁.union Q₂) := by
  obtain ⟨φ, hφ⟩ := h₁
  obtain ⟨ψ, hψ⟩ := h₂
  exact ⟨φ.disj ψ, fun A => by
    simp only [BooleanQuery.union, hφ A, hψ A, Sentence.Models, Formula.Sat]⟩

end DescriptiveComplexity

end Complexity
