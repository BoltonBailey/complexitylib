/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.FormulaEncoding.ForwardNavigation.Defs
import Complexitylib.Circuits.FormulaEncoding.ForwardNavigation.Internal

/-!
# Forward navigation in postfix formula codes

This module exposes the streaming invariant that locates a binary postfix
formula's child boundary in one left-to-right pass.
-/

namespace Complexity

namespace FormulaCode

/-- Scanning one canonical formula raises the postfix stack height by one and
has the closed numeric effect recorded by `afterFormula`. -/
theorem forwardScan_tokens
    (formula : BoolFormula) (state : ForwardScanState) :
    forwardScan (tokens formula) state = state.afterFormula formula :=
  forwardScan_tokens_internal formula state

/-- In the rootless body of a canonical binary formula, the last height-one
boundary is exactly the end of the left child, both in tokens and encoded
bits. -/
theorem forwardScan_binary_body
    (left right : BoolFormula) :
    forwardScan (tokens left ++ tokens right) ForwardScanState.initial =
      { stackHeight := 2
        tokenCount := left.size + right.size
        bitOffset := tokensCodeLength (tokens left) +
          tokensCodeLength (tokens right)
        lastOneCount := left.size
        lastOneBitOffset := tokensCodeLength (tokens left) } :=
  forwardScan_binary_body_internal left right

end FormulaCode

end Complexity
