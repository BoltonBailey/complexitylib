/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AndOrNot.Defs

/-!
# Constant and primary-input source circuits -- definitions

An input source is either a Boolean constant or one selected primary input.
A source tuple materializes any positive collection of such values using only
counted output gates and no internal gates.
-/


@[expose] public section

namespace Complexity

namespace Circuit

/-- One output source: a Boolean constant or a selected primary input. -/
inductive InputSource (inputWidth : ℕ) where
  | constant (value : Bool)
  | input (coordinate : Fin inputWidth)

namespace InputSource

/-- Semantic value of one source under a primary-input assignment. -/
def eval {inputWidth : ℕ} (source : InputSource inputWidth)
    (input : BitString inputWidth) : Bool :=
  match source with
  | .constant value => value
  | .input coordinate => input coordinate

end InputSource

/-- Output gate materializing one source. -/
def inputSourceOutputGate {inputWidth : ℕ} [NeZero inputWidth]
    (source : InputSource inputWidth) : Gate Basis.andOr2 (inputWidth + 0) :=
  match source with
  | .constant value =>
      { op := if value then .or else .and
        fanIn := 2
        arityOk := rfl
        inputs := fun _ => ⟨0, by have := NeZero.ne inputWidth; omega⟩
        negated := fun input => input.val ≠ 0 }
  | .input coordinate =>
      { op := .and
        fanIn := 2
        arityOk := rfl
        inputs := fun _ => ⟨coordinate.val, by omega⟩
        negated := fun _ => false }

/-- Materialize a tuple of constants and selected primary inputs. -/
def inputSources {inputWidth outputWidth : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (sources : Fin outputWidth → InputSource inputWidth) :
    Circuit Basis.andOr2 inputWidth outputWidth 0 where
  gates := Fin.elim0
  outputs output := inputSourceOutputGate (sources output)
  acyclic index := Fin.elim0 index

end Circuit

end Complexity
