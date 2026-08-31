/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.InputPairing.Defs
public import Complexitylib.Circuits.InputPairing.Internal

/-!
# Self-delimiting input-pair circuits

This module exposes a zero-internal-gate circuit for the canonical pairing
codec used by serialized machines and circuit evaluators.
-/


public section

namespace Complexity

namespace Circuit

/-- Pair-source circuits serialize exactly the semantic values of their left
and right source tuples. -/
theorem eval_pairInputSources
    {inputWidth leftWidth rightWidth : ℕ}
    [NeZero inputWidth]
    (left : Fin leftWidth → InputSource inputWidth)
    (right : Fin rightWidth → InputSource inputWidth)
    (input : BitString inputWidth) :
    BitString.toList ((pairInputSources left right).eval input) =
      pair (BitString.toList (fun i => (left i).eval input))
        (BitString.toList (fun i => (right i).eval input)) :=
  eval_pairInputSources_internal left right input

/-- Pair-source circuits pay exactly one counted output gate per serialized
query bit. -/
@[simp] theorem size_pairInputSources
    {inputWidth leftWidth rightWidth : ℕ}
    [NeZero inputWidth]
    (left : Fin leftWidth → InputSource inputWidth)
    (right : Fin rightWidth → InputSource inputWidth) :
    (pairInputSources left right).size =
      pairSourceWidth leftWidth rightWidth :=
  size_pairInputSources_internal left right

end Circuit

end Complexity
