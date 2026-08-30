/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith

/-!
# Plurality over a finite set

The pigeonhole fact behind every "decode a cloud by majority vote" step: among
the `Fintype.card α` possible labels, some label is worn by at least a
`1 / Fintype.card α` fraction of a finite set.

Dinur's degree reduction uses this to decode the blown-up assignment — a vertex
is given the label that the most half-edges of its cloud claim — and the bound
below is exactly what makes the *disagreeing* part of a cloud small enough for
the cloud expander to charge it.

## Main results

- `Complexity.exists_plurality` — some label captures at least `1 / card α` of
  the set
-/

@[expose] public section

namespace Complexity

/-- **Plurality.** Some label is taken by at least a `1 / Fintype.card α`
fraction of `S`. -/
theorem exists_plurality {β α : Type} [DecidableEq α] [Fintype α] [Nonempty α]
    (S : Finset β) (A : β → α) :
    ∃ a : α, S.card ≤ Fintype.card α * (S.filter fun p => A p = a).card := by
  by_contra hcon
  push Not at hcon
  have hsum : ∑ a : α, (S.filter fun p => A p = a).card = S.card :=
    (Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (A x))).symm
  have hle : ∀ a : α, Fintype.card α * (S.filter fun p => A p = a).card + 1 ≤ S.card :=
    fun a => hcon a
  have h1 : Fintype.card α * S.card + Fintype.card α ≤ Fintype.card α * S.card := by
    calc Fintype.card α * S.card + Fintype.card α
        = ∑ a : α, (Fintype.card α * (S.filter fun p => A p = a).card + 1) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
          simp
      _ ≤ ∑ _a : α, S.card := Finset.sum_le_sum fun a _ => hle a
      _ = Fintype.card α * S.card := by simp [mul_comm]
  have hpos : 0 < Fintype.card α := Fintype.card_pos
  linarith

end Complexity
