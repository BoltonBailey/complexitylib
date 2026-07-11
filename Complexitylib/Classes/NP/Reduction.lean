/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.NP
import Complexitylib.Classes.P.Defs

/-!
# Polynomial-time many-one reductions and NP-completeness

This file defines **polynomial-time many-one (Karp) reductions** `L ≤ₚ L'` and
the derived notions **`NPHard`** and **`NPComplete`**, following Arora–Barak
(Definitions 2.7, 2.8).

A reduction `L ≤ₚ L'` is a polynomial-time computable function `f` (i.e. `f ∈ FP`)
such that `x ∈ L ↔ f x ∈ L'`. A language is NP-hard when every language in `NP`
reduces to it, and NP-complete when it is additionally a member of `NP`.

The headline application is `SAT.NPComplete_language` (Cook–Levin), in
`Complexitylib/SAT/CookLevin.lean`.
-/

namespace Complexity


/-- **Polynomial-time many-one reduction.** `MapReducesPoly L L'` (written
    `L ≤ₚ L'`) holds when there is a polynomial-time computable function `f`
    (`f ∈ FP`) with `x ∈ L ↔ f x ∈ L'` for every input `x`. -/
def MapReducesPoly (L L' : Language) : Prop :=
  ∃ f : List Bool → List Bool, f ∈ FP ∧ ∀ x, x ∈ L ↔ f x ∈ L'

@[inherit_doc] infix:50 " ≤ₚ " => MapReducesPoly

/-- **NP-hardness.** `L` is NP-hard when every language in `NP` reduces to `L`
    in polynomial time. -/
def NPHard (L : Language) : Prop := ∀ L' ∈ NP, L' ≤ₚ L

/-- **NP-completeness.** `L` is NP-complete when it is in `NP` and NP-hard. -/
def NPComplete (L : Language) : Prop := L ∈ NP ∧ NPHard L

end Complexity
