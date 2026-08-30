/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.InputSources.Defs

/-!
# Constant and primary-input source circuits -- proof internals
-/


public section

namespace Complexity

namespace Circuit

theorem eval_inputSources_internal {inputWidth outputWidth : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (sources : Fin outputWidth → InputSource inputWidth)
    (input : BitString inputWidth) :
    (inputSources sources).eval input =
      fun output => (sources output).eval input := by
  funext output
  unfold Circuit.eval
  change (inputSourceOutputGate (sources output)).eval
      ((inputSources sources).wireValue input) =
    (sources output).eval input
  cases hsource : sources output with
  | constant value =>
      cases value with
      | false =>
          unfold inputSourceOutputGate InputSource.eval Gate.eval
          change AndOrOp.eval .and 2 _ = false
          rw [AndOrOp.eval_two_and]
          dsimp only
          rw [Circuit.wireValue_of_lt _ _ _ (by
            have hinput : 0 < inputWidth :=
              Nat.pos_of_ne_zero (NeZero.ne inputWidth)
            simp
            omega)]
          simp
      | true =>
          unfold inputSourceOutputGate InputSource.eval Gate.eval
          change AndOrOp.eval .or 2 _ = true
          rw [AndOrOp.eval_two_or]
          dsimp only
          rw [Circuit.wireValue_of_lt _ _ _ (by
            have hinput : 0 < inputWidth :=
              Nat.pos_of_ne_zero (NeZero.ne inputWidth)
            simp
            omega)]
          simp
  | input coordinate =>
      unfold inputSourceOutputGate InputSource.eval Gate.eval
      change AndOrOp.eval .and 2 _ = input coordinate
      rw [AndOrOp.eval_two_and]
      dsimp only
      simp only [Bool.false_xor]
      rw [Circuit.wireValue_of_lt _ _ _ (by simp)]
      simp

end Circuit

end Complexity
