/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.TQBFEmitWire
public import Complexitylib.Classes.Containments.Internal.TQBFReach

/-!
# The flat Savitch instance is emittable

⚠️ Unreviewed by Bolton

The prefix and the matrix of the flat quantified Boolean formula are both `FP` functions of the
input, and both compute the intended object. Pairing them gives the whole instance.

## Main results

- `flatInstance_mem_FP` — the encoded instance is an `FP` function of the input
-/

@[expose] public section

namespace Complexity

open Polynomial QBF CircuitUnrolling Shen

variable {k : ℕ} (tm : NTM k) (sp : Polynomial ℕ)

/-- The flat layout is the layout the hardness construction uses. -/
theorem flatLayoutOf_eq (x : List Bool) :
    flatLayoutOf tm sp x
      = { W := configWidth tm (x.length + sp.eval x.length + 2), Ws := 2,
          n := codeBound tm.Q k x.length (sp.eval x.length) } := by
  simp only [flatLayoutOf, horizonP_eval, levelsP_eval]

/-- The block width of the flat layout, spelled out. -/
theorem flatLayoutOf_W_eq (x : List Bool) :
    (flatLayoutOf tm sp x).W = configWidth tm (x.length + sp.eval x.length + 2) := by
  rw [flatLayoutOf_W_configWidth, horizonP_eval]

/-- The level count of the flat layout, spelled out. -/
theorem flatLayoutOf_n_eq (x : List Bool) :
    (flatLayoutOf tm sp x).n = codeBound tm.Q k x.length (sp.eval x.length) := by
  rw [flatLayoutOf_n, levelsP_eval]

/-- The horizon of the flat layout. -/
theorem horizonP_eval_layout (x : List Bool) :
    (horizonP sp).eval x.length = x.length + sp.eval x.length + 2 := horizonP_eval sp _

/-- The matrix of the flat formula, as a function of the input. -/
noncomputable def flatMatrixOf (x : List Bool) : List (List CLit) :=
  (flatLayoutOf tm sp x).fullClauses
    (cfgValidC tm ((horizonP sp).eval x.length) x (sp.eval x.length))
    (cfgBaseC tm ((horizonP sp).eval x.length))
    (cfgAccC tm ((horizonP sp).eval x.length))
    (encodeBlock tm ((horizonP sp).eval x.length) (tm.initCfg x))

/-- **The matrix is emittable.** -/
theorem flatMatrix_mem_FP :
    (fun x => DataEncode.bitstringEncode (flatMatrixOf tm sp x)) ∈ FP := by
  refine mem_FP_of_eq (matrixEmit_mem_FP tm sp) fun x => ?_
  rw [flatMatrixOf]
  exact matrixEmit_value tm ((horizonP sp).eval x.length) sp x _ rfl
    (Fintype.card_pos_iff.mpr ⟨tm.qstart⟩) (flatLayoutOf_W_configWidth tm sp x)
    (fun r hr => rfl)

/-- **The whole instance is emittable.** -/
theorem flatInstance_mem_FP :
    (fun x => DataEncode.bitstringEncode
      (((flatLayoutOf tm sp x).fullPrefix, flatMatrixOf tm sp x)
        : Prefix × List (List CLit))) ∈ FP :=
  pair_emit_mem_FP _ _
    (by
      refine mem_FP_of_eq (prefixEnc_mem_FP tm sp) fun x => ?_
      rw [FlatLayout.fullPrefix_eq])
    (flatMatrix_mem_FP tm sp)

end Complexity
