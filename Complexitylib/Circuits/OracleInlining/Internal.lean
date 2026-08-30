/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.OracleInlining.Defs
public import Complexitylib.Circuits.Composition
public import Complexitylib.Circuits.InputProjection

/-!
# Circuit-level oracle inlining -- proof internals
-/


public section

namespace Complexity

namespace Circuit

/-- Internal exact evaluation law for one inlined oracle answer. -/
theorem eval_appendOracleAnswer_internal
    {inputWidth historyWidth queryWidth historyGates queryGates oracleGates : ℕ}
    [NeZero inputWidth] [NeZero historyWidth] [NeZero queryWidth]
    (history : Circuit Basis.andOr2 inputWidth historyWidth historyGates)
    (query : Circuit Basis.andOr2 historyWidth queryWidth queryGates)
    (oracle : Circuit Basis.andOr2 queryWidth 1 oracleGates)
    (input : BitString inputWidth) :
    (appendOracleAnswer history query oracle).eval input =
      Fin.append (history.eval input)
        (oracle.eval (query.eval (history.eval input))) := by
  simp [appendOracleAnswer, Function.comp_def]

end Circuit

end Complexity
