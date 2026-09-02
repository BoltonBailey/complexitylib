/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.TQBFFlat
public import Complexitylib.Classes.Containments.Internal.ConfigCount
public import Complexitylib.Classes.Containments.Internal.NLSearchAssemble

/-!
# The flat layout's sizes are polynomials in the input length

⚠️ Unreviewed by Bolton

Every number the flat Savitch formula depends on — the horizon `T`, the block width, the number
of levels, the total number of variables — is `q.eval x.length` for an explicit
`q : Polynomial ℕ` built from the machine and a polynomial space bound. That is what lets an
`FP` emitter compute them: `polyRuler q` writes any of them down in unary.

## Main results

- `horizonP`, `widthP`, `levelsP`, `nvarP` and their `eval` lemmas
- `flatLayoutOf` — the `FlatLayout` of an input, with `W`, `Ws`, `n` read off those polynomials
-/

@[expose] public section

namespace Complexity

open Polynomial CircuitUnrolling

variable {k : ℕ} (tm : NTM k) (sp : Polynomial ℕ)

/-- The horizon: input length plus space bound plus two. -/
noncomputable def horizonP : Polynomial ℕ := X + sp + C 2

@[simp] theorem horizonP_eval (n : ℕ) :
    (horizonP sp).eval n = n + sp.eval n + 2 := by
  simp [horizonP]

/-- The width of one configuration block. -/
noncomputable def widthP : Polynomial ℕ :=
  C (Fintype.card tm.Q) + C (k + 2) * (horizonP sp + C 1) + C (4 * (k + 2)) * (horizonP sp + C 2)

@[simp] theorem widthP_eval (n : ℕ) :
    (widthP tm sp).eval n = configWidth tm ((horizonP sp).eval n) := by
  simp only [widthP, configWidth, eval_add, eval_mul, eval_C]

/-- The number of Savitch levels: the exponent of the code-count bound. -/
noncomputable def levelsP : Polynomial ℕ :=
  C (Fintype.card tm.Q) + (X + sp + C 2) + C (3 * k) * (sp + C 1) + C 3 * (sp + C 2)

@[simp] theorem levelsP_eval (n : ℕ) :
    (levelsP tm sp).eval n = codeBound tm.Q k n (sp.eval n) := by
  simp only [levelsP, codeBound, eval_add, eval_mul, eval_C, eval_X]

/-- The total number of variables of the flat formula. -/
noncomputable def nvarP : Polynomial ℕ :=
  C 2 * widthP tm sp + C 1 + (C 7 * widthP tm sp + C 1) * levelsP tm sp + C 2

/-- The flat layout of an input: blocks as wide as a configuration, a two-bit scratch, and one
level per unit of the code-count exponent. -/
noncomputable def flatLayoutOf (x : List Bool) : FlatLayout where
  W := configWidth tm ((horizonP sp).eval x.length)
  Ws := 2
  n := (levelsP tm sp).eval x.length

@[simp] theorem flatLayoutOf_W (x : List Bool) :
    (flatLayoutOf tm sp x).W = (widthP tm sp).eval x.length :=
  (widthP_eval tm sp _).symm

@[simp] theorem flatLayoutOf_Ws (x : List Bool) : (flatLayoutOf tm sp x).Ws = 2 := rfl

@[simp] theorem flatLayoutOf_n (x : List Bool) :
    (flatLayoutOf tm sp x).n = (levelsP tm sp).eval x.length := rfl

@[simp] theorem nvarP_eval (x : List Bool) :
    (nvarP tm sp).eval x.length = (flatLayoutOf tm sp x).nvar := by
  rw [FlatLayout.nvar, FlatLayout.scr, FlatLayout.levelSize]
  simp only [nvarP, flatLayoutOf_W, flatLayoutOf_Ws, flatLayoutOf_n, eval_add, eval_mul,
    eval_C]

/-- The layout's sizes, in unary, are `FP` functions of the input. -/
theorem nvarRuler_mem_FP : (fun x => polyRuler (nvarP tm sp) x) ∈ FP :=
  polyRulerFn_mem_FP _ id_mem_FP

theorem widthRuler_mem_FP : (fun x => polyRuler (widthP tm sp) x) ∈ FP :=
  polyRulerFn_mem_FP _ id_mem_FP

theorem levelsRuler_mem_FP : (fun x => polyRuler (levelsP tm sp) x) ∈ FP :=
  polyRulerFn_mem_FP _ id_mem_FP

end Complexity
