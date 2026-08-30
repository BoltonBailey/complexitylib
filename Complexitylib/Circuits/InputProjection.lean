/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.InputProjection.Defs
public import Complexitylib.Circuits.InputProjection.Internal

/-!
# Primary-input projection circuits

This module exposes zero-internal-gate circuits that copy, permute, or duplicate
primary inputs into an arbitrary positive output tuple.
-/


public section

namespace Complexity

namespace Circuit

/-- Input projection evaluates by precomposing the input with the projection map. -/
@[simp] theorem eval_projectInputs {N M : ℕ} [NeZero N] [NeZero M]
    (mapInput : Fin M → Fin N) (input : BitString N) :
    (projectInputs mapInput).eval input = input ∘ mapInput :=
  eval_projectInputs_internal mapInput input

/-- An `M`-output input projection has exactly `M` counted output gates. -/
@[simp] theorem size_projectInputs {N M : ℕ} [NeZero N] [NeZero M]
    (mapInput : Fin M → Fin N) :
    (projectInputs mapInput).size = M := by
  simp only [Circuit.size, Nat.zero_add]

end Circuit

end Complexity
