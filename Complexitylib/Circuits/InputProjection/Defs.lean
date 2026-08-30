/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AndOrNot.Defs

/-!
# Primary-input projection circuits -- definitions

An input projection copies selected primary inputs to a positive output tuple.
Each output uses one duplicated-input AND gate, and no internal gates are needed.
-/


@[expose] public section

namespace Complexity

namespace Circuit

/-- Duplicated-input output gate that copies one selected primary input. -/
def inputProjectionOutputGate {N M : ℕ} (mapInput : Fin M → Fin N)
    (output : Fin M) : Gate Basis.andOr2 (N + 0) where
  op := .and
  fanIn := 2
  arityOk := rfl
  inputs := fun _ => ⟨(mapInput output).val, by omega⟩
  negated := fun _ => false

/-- Circuit whose output tuple is the selected tuple of primary inputs. -/
def projectInputs {N M : ℕ} [NeZero N] [NeZero M]
    (mapInput : Fin M → Fin N) : Circuit Basis.andOr2 N M 0 where
  gates := Fin.elim0
  outputs output := inputProjectionOutputGate mapInput output
  acyclic index := Fin.elim0 index

end Circuit

end Complexity
