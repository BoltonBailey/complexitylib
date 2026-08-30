/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.Cobham.Internal.FPBridge
public import Complexitylib.Classes.P.Cobham.Internal.PolyLen

/-!
# Rulers of polynomial length

A *ruler* is a string of zeros whose only content is its length. `polyRuler q`
has length `q.eval |x|` and is polynomial-time in `x`; `wideRuler m R` is `m`
copies of a ruler. Rulers drive the bounded loops of `Cobham.iterate_mem_FP`:
the loop runs once per ruler symbol.

## Main definitions

- `polyRuler`, `polyRulerFn_mem_FP` — a ruler of polynomial length, in `FP`
- `wideRuler`, `wideRulerFn_mem_FP` — a constant number of copies
- `blockRuler_eq_polyRuler` — the block ruler of a polynomial window
-/

@[expose] public section

namespace Complexity
open Cobham

/-- A ruler whose length is a polynomial in the input length. -/
def polyRuler (q : Polynomial ℕ) (x : List Bool) : List Bool :=
  List.replicate (q.eval x.length) false

@[simp] theorem polyRuler_length (q : Polynomial ℕ) (x : List Bool) :
    (polyRuler q x).length = q.eval x.length := by
  rw [polyRuler, List.length_replicate]

theorem polyRulerFn_mem_FP (q : Polynomial ℕ) {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => polyRuler q (a z)) ∈ FP := by
  have h : Cobham fun v : Fin 1 → List Bool =>
      List.replicate (Cobham.polyLen q (v 0)).length false :=
    Cobham.zeroBlockFn (Cobham.polyLen_mem q (Cobham.proj 0))
  refine unFn_mem_FP (g := polyRuler q) ?_ ha
  refine h.of_eq fun v => ?_
  rw [polyRuler, Cobham.polyLen_length]

/-- The block ruler of a polynomial window. -/
theorem blockRuler_eq_polyRuler (q : Polynomial ℕ) (x : List Bool) :
    blockRuler (q.eval x.length) = polyRuler (2 * q + 2) x := by
  rw [blockRuler, polyRuler, blockWidth]
  congr 1
  simp [Polynomial.eval_add, Polynomial.eval_mul]
  omega

/-- A code's width, as a ruler: `m` copies of the block ruler. -/
def wideRuler (m : ℕ) (R : List Bool) : List Bool := (List.replicate m R).flatten

@[simp] theorem wideRuler_length (m : ℕ) (R : List Bool) :
    (wideRuler m R).length = m * R.length := by
  rw [wideRuler, List.length_flatten]
  simp [List.sum_replicate]

/-- Every constant number of copies of a polynomial-time value is
polynomial-time. -/
theorem wideRulerFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) (m : ℕ) :
    (fun z => wideRuler m (a z)) ∈ FP := by
  induction m with
  | zero => exact mem_FP_of_eq (constFn_mem_FP []) (fun _ => rfl)
  | succ m ih =>
      refine mem_FP_of_eq (Cobham.appendFn_mem_FP ha ih) fun z => ?_
      simp only [wideRuler, List.replicate_succ, List.flatten_cons]

end Complexity
