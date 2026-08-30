/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.OracleInlining.Defs
import Complexitylib.Circuits.OracleInlining.Internal

/-!
# Circuit-level oracle inlining

This module exposes the exact semantics and gate accounting for extending an
adaptive history by one answer from a fixed-width oracle circuit.
-/


public section

namespace Complexity

namespace Circuit

/-- One inlining step retains the existing history and appends the oracle
circuit's answer to the query computed from that history. -/
@[simp] theorem eval_appendOracleAnswer
    {inputWidth historyWidth queryWidth historyGates queryGates oracleGates : ℕ}
    [NeZero inputWidth] [NeZero historyWidth] [NeZero queryWidth]
    (history : Circuit Basis.andOr2 inputWidth historyWidth historyGates)
    (query : Circuit Basis.andOr2 historyWidth queryWidth queryGates)
    (oracle : Circuit Basis.andOr2 queryWidth 1 oracleGates)
    (input : BitString inputWidth) :
    (appendOracleAnswer history query oracle).eval input =
      Fin.append (history.eval input)
        (oracle.eval (query.eval (history.eval input))) :=
  eval_appendOracleAnswer_internal history query oracle input

/-- One inlining step has the source history size, the query and oracle sizes,
and one additional `historyWidth`-gate copy of the retained history. -/
@[simp] theorem size_appendOracleAnswer
    {inputWidth historyWidth queryWidth historyGates queryGates oracleGates : ℕ}
    [NeZero inputWidth] [NeZero historyWidth] [NeZero queryWidth]
    (history : Circuit Basis.andOr2 inputWidth historyWidth historyGates)
    (query : Circuit Basis.andOr2 historyWidth queryWidth queryGates)
    (oracle : Circuit Basis.andOr2 queryWidth 1 oracleGates) :
    (appendOracleAnswer history query oracle).size =
      history.size + historyWidth + query.size + oracle.size := by
  rw [appendOracleAnswer, Circuit.size_compose, Circuit.size_parallel,
    Circuit.size_projectInputs, Circuit.size_compose]
  omega

end Circuit

end Complexity
