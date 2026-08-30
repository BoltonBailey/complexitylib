/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.InputProjection.Defs

/-!
# Primary-input projection circuits -- proof internals
-/


public section

namespace Complexity

namespace Circuit

theorem eval_projectInputs_internal {N M : ℕ} [NeZero N] [NeZero M]
    (mapInput : Fin M → Fin N) (input : BitString N) :
    (projectInputs mapInput).eval input = input ∘ mapInput := by
  funext output
  unfold Circuit.eval projectInputs inputProjectionOutputGate Gate.eval
  change AndOrOp.eval .and 2 _ = _
  rw [AndOrOp.eval_two_and]
  dsimp only
  simp only [Bool.false_xor]
  rw [Circuit.wireValue_of_lt _ _ _ (by simp)]
  simp

end Circuit

end Complexity
