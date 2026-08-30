/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Composition.Defs
public import Complexitylib.Circuits.InputProjection.Defs

/-!
# Circuit-level oracle inlining -- definitions

An adaptive oracle computation carries its original input followed by the
answers to earlier queries. One inlining step computes the next fixed-width
query from that history, feeds it to a single-output oracle circuit, and
appends the answer while preserving the existing history outputs.
-/


@[expose] public section

namespace Complexity

namespace Circuit

/-- Extend a circuit producing a `historyWidth`-bit history by one inlined
oracle answer.

The query circuit reads the current history, and the oracle circuit reads the
query. The outer identity projection retains the history alongside the new
answer before the whole extension is composed with `history`. -/
def appendOracleAnswer
    {inputWidth historyWidth queryWidth historyGates queryGates oracleGates : ℕ}
    [NeZero inputWidth] [NeZero historyWidth] [NeZero queryWidth]
    (history : Circuit Basis.andOr2 inputWidth historyWidth historyGates)
    (query : Circuit Basis.andOr2 historyWidth queryWidth queryGates)
    (oracle : Circuit Basis.andOr2 queryWidth 1 oracleGates) :
    Circuit Basis.andOr2 inputWidth (historyWidth + 1)
      (historyGates + historyWidth +
        (0 + (queryGates + queryWidth + oracleGates))) :=
  ((projectInputs fun input : Fin historyWidth => input).parallel
    (oracle.compose query)).compose history

end Circuit

end Complexity
