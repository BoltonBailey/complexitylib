/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.BitString
public import Complexitylib.Circuits.OracleInlining.Defs
public import Complexitylib.Models.TuringMachine.Oracle.Defs

/-!
# Fixed-round adaptive oracle circuit programs -- definitions

A program makes a fixed number of adaptive Boolean-oracle calls. Before round
`i`, its history consists of the original input followed by the `i` previous
answer bits. A query circuit maps that history to a positive-width query, and a
final circuit maps the complete history to the program output.

Query widths may vary by round. A variable-call computation can use dummy
queries after it has logically terminated, while retaining a fixed circuit
shape at each outer input length.
-/


@[expose] public section

namespace Complexity

private instance neZero_add_right (left right : ℕ) [NeZero left] :
    NeZero (left + right) :=
  ⟨by have := NeZero.ne left; omega⟩

/-- A fixed-round adaptive oracle computation whose query generators and final
output map are fan-in-two AND/OR circuits. -/
structure AdaptiveOracleProgram (inputWidth outputWidth rounds : ℕ)
    [NeZero inputWidth] [NeZero outputWidth] where
  /-- Width of the query issued in each round. -/
  queryWidth : Fin rounds → ℕ
  /-- Every query has positive width, as required by the circuit model. -/
  [queryWidth_neZero : ∀ round, NeZero (queryWidth round)]
  /-- Internal-gate count of each query circuit. -/
  queryGates : Fin rounds → ℕ
  /-- Query circuit for each round, reading the input and previous answers. -/
  query : ∀ round, Circuit Basis.andOr2
    (inputWidth + round.val) (queryWidth round) (queryGates round)
  /-- Internal-gate count of the final output circuit. -/
  finalGates : ℕ
  /-- Final output circuit, reading the input and every oracle answer. -/
  final : Circuit Basis.andOr2
    (inputWidth + rounds) outputWidth finalGates

attribute [instance] AdaptiveOracleProgram.queryWidth_neZero

namespace AdaptiveOracleProgram

/-- Semantic history after `completed` oracle calls. It consists of the
original input followed in order by the answers to the first `completed`
queries. -/
def history {inputWidth outputWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (program : AdaptiveOracleProgram inputWidth outputWidth rounds)
    (oracle : BooleanOracle) (input : BitString inputWidth) :
    (completed : ℕ) → completed ≤ rounds → BitString (inputWidth + completed)
  | 0, _ => input
  | completed + 1, hcompleted =>
      let prior := program.history oracle input completed
        (Nat.le_trans (Nat.le_succ completed) hcompleted)
      let round : Fin rounds := ⟨completed, Nat.lt_of_succ_le hcompleted⟩
      let query := (program.query round).eval prior
      fun index =>
        Fin.append prior (fun _ : Fin 1 => oracle query.toList)
          (Fin.cast (by omega) index)

/-- Output of the adaptive program relative to a Boolean oracle. -/
def eval {inputWidth outputWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (program : AdaptiveOracleProgram inputWidth outputWidth rounds)
    (oracle : BooleanOracle) (input : BitString inputWidth) :
    BitString outputWidth :=
  program.final.eval (program.history oracle input rounds le_rfl)

/-- One single-output oracle circuit for each query round of `program`. The
query width fixes which circuit may be used at that round. -/
structure OracleCircuitImplementation {inputWidth outputWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (program : AdaptiveOracleProgram inputWidth outputWidth rounds) where
  /-- Internal-gate count of the oracle circuit used in each round. -/
  internalGates : Fin rounds → ℕ
  /-- Oracle circuit at the query width of each round. -/
  circuit : ∀ round, Circuit Basis.andOr2
    (program.queryWidth round) 1 (internalGates round)

namespace OracleCircuitImplementation

/-- The selected oracle circuits implement `oracle` when every round circuit
returns the oracle's answer on every fixed-width query. -/
def Implements {inputWidth outputWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    {program : AdaptiveOracleProgram inputWidth outputWidth rounds}
    (implementation : OracleCircuitImplementation program)
    (oracle : BooleanOracle) : Prop :=
  ∀ round query,
    (implementation.circuit round).eval query 0 = oracle query.toList

end OracleCircuitImplementation

/-- Exact size of the circuit producing a prefix of the inlined adaptive
history. This recurrence mirrors `inlineHistory`: the base identity costs one
output gate per original input, and each round pays to retain the old history
and to evaluate its query and oracle circuits. -/
def inlineHistorySize {inputWidth outputWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (program : AdaptiveOracleProgram inputWidth outputWidth rounds)
    (implementation : OracleCircuitImplementation program) :
    (completed : ℕ) → completed ≤ rounds → ℕ
  | 0, _ => inputWidth
  | completed + 1, hcompleted =>
      let hprior := Nat.le_trans (Nat.le_succ completed) hcompleted
      let round : Fin rounds := ⟨completed, Nat.lt_of_succ_le hcompleted⟩
      program.inlineHistorySize implementation completed hprior +
        (inputWidth + completed) + (program.query round).size +
          (implementation.circuit round).size

/-- Compile the first `completed` adaptive calls into one circuit producing
the original input followed by their answer bits. -/
def inlineHistory {inputWidth outputWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (program : AdaptiveOracleProgram inputWidth outputWidth rounds)
    (implementation : OracleCircuitImplementation program) :
    (completed : ℕ) → completed ≤ rounds →
      Σ internalGates,
        Circuit Basis.andOr2 inputWidth (inputWidth + completed) internalGates
  | 0, _ =>
      ⟨0, Circuit.projectInputs (fun input : Fin inputWidth => input)⟩
  | completed + 1, hcompleted =>
      let hprior := Nat.le_trans (Nat.le_succ completed) hcompleted
      letI : NeZero (inputWidth + completed) :=
        ⟨by have := NeZero.ne inputWidth; omega⟩
      let prior := program.inlineHistory implementation completed hprior
      let round : Fin rounds := ⟨completed, Nat.lt_of_succ_le hcompleted⟩
      ⟨_, Circuit.appendOracleAnswer prior.2 (program.query round)
        (implementation.circuit round)⟩

/-- Compile every adaptive call and then the final output circuit into one
ordinary oracle-free circuit. -/
def inline {inputWidth outputWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (program : AdaptiveOracleProgram inputWidth outputWidth rounds)
    (implementation : OracleCircuitImplementation program) :
    Σ internalGates,
      Circuit Basis.andOr2 inputWidth outputWidth internalGates :=
  let history := program.inlineHistory implementation rounds le_rfl
  ⟨_, program.final.compose history.2⟩

end AdaptiveOracleProgram

end Complexity
