/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Hamming.Code.Repetition.Defs
import Complexitylib.Metacomplexity.Hamming.Code.Internal
import Complexitylib.Metacomplexity.Hamming.Internal

/-!
# Boolean repetition codes -- proof internals
-/


public section

namespace Complexity

namespace BooleanCode

theorem repetitionEncode_apply_internal {messageLength copies : ℕ}
    (message : BooleanHamming.Word messageLength)
    (coordinate : Fin (messageLength * copies)) :
    repetitionEncode messageLength copies message coordinate =
      message (finProdFinEquiv.symm coordinate).1 := by
  simp [repetitionEncode, blocksEquiv_symm_apply]

theorem repetitionEncode_injective_internal {messageLength copies : ℕ}
    (hcopies : 0 < copies) :
    Function.Injective (repetitionEncode messageLength copies) := by
  intro left right hencode
  funext input
  let copy : Fin copies := ⟨0, hcopies⟩
  have hcoordinate := congrFun hencode (finProdFinEquiv (input, copy))
  simpa [repetitionEncode_apply_internal] using hcoordinate

theorem distance_repetitionEncode_internal {messageLength copies : ℕ}
    (left right : BooleanHamming.Word messageLength) :
    BooleanHamming.distance
      (repetitionEncode messageLength copies left)
      (repetitionEncode messageLength copies right) =
        BooleanHamming.distance left right * copies := by
  unfold BooleanHamming.distance
  calc
    (BooleanHamming.disagreement
        (repetitionEncode messageLength copies left)
        (repetitionEncode messageLength copies right)).card =
        ((BooleanHamming.disagreement left right).product
          (Finset.univ : Finset (Fin copies))).card := by
      apply Finset.card_bij'
          (fun coordinate _ => finProdFinEquiv.symm coordinate)
          (fun pair _ => finProdFinEquiv pair)
      · intro coordinate hcoordinate
        apply Finset.mem_product.mpr
        constructor
        · apply (BooleanHamming.mem_disagreement_internal left right _).mpr
          have hne := (BooleanHamming.mem_disagreement_internal
            (repetitionEncode messageLength copies left)
            (repetitionEncode messageLength copies right) coordinate).mp
              hcoordinate
          simpa [repetitionEncode_apply_internal] using hne
        · simp
      · intro pair hpair
        apply (BooleanHamming.mem_disagreement_internal
          (repetitionEncode messageLength copies left)
          (repetitionEncode messageLength copies right) _).mpr
        have hne := (BooleanHamming.mem_disagreement_internal left right pair.1).mp
          (Finset.mem_product.mp hpair).1
        simpa [repetitionEncode_apply_internal] using hne
      · intro coordinate _
        exact Equiv.apply_symm_apply finProdFinEquiv coordinate
      · intro pair _
        exact Equiv.symm_apply_apply finProdFinEquiv pair
    _ = (BooleanHamming.disagreement left right).card * copies := by
      simp

theorem repetitionEncode_isLinear_internal {messageLength copies : ℕ} :
    repetitionEncode messageLength copies (zeroWord messageLength) =
        zeroWord (messageLength * copies) ∧
      ∀ left right,
        repetitionEncode messageLength copies (xorWords left right) =
          xorWords (repetitionEncode messageLength copies left)
            (repetitionEncode messageLength copies right) := by
  constructor
  · funext coordinate
    simp [repetitionEncode_apply_internal, zeroWord]
  · intro left right
    funext coordinate
    simp [repetitionEncode_apply_internal, xorWords]

end BooleanCode

end Complexity
