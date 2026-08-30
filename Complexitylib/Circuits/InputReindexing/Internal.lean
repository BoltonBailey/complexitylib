/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.InputReindexing.Defs
import Complexitylib.Circuits.Composition.Internal

/-!
# Circuit input reindexing -- proof internals
-/


public section

namespace Complexity

namespace Circuit

theorem reindexInputWire_input_internal {N N' G : ℕ}
    (mapInput : Fin N → Fin N') (input : Fin N) :
    reindexInputWire (G := G) mapInput (Fin.castAdd G input) =
      Fin.castAdd G (mapInput input) := by
  simp [reindexInputWire]

theorem reindexInputWire_gate_internal {N N' G : ℕ}
    (mapInput : Fin N → Fin N') (gate : Fin G) :
    reindexInputWire mapInput (Fin.natAdd N gate) =
      Fin.natAdd N' gate := by
  simp [reindexInputWire]

theorem wireValue_reindexInputs_internal {B : Basis} {N N' M G : ℕ}
    [NeZero N] [NeZero N'] [NeZero M]
    (circuit : Circuit B N M G) (mapInput : Fin N → Fin N')
    (input : BitString N') (wire : Fin (N + G)) :
    (circuit.reindexInputs mapInput).wireValue input
        (reindexInputWire mapInput wire) =
      circuit.wireValue (input ∘ mapInput) wire := by
  induction hwire : wire.val using Nat.strong_induction_on generalizing wire with
  | h wireValue ih =>
      refine Fin.addCases (motive := fun wire : Fin (N + G) =>
        wire.val = wireValue →
          (circuit.reindexInputs mapInput).wireValue input
              (reindexInputWire mapInput wire) =
            circuit.wireValue (input ∘ mapInput) wire) ?_ ?_ wire hwire
      · intro sourceInput _
        rw [reindexInputWire_input_internal]
        rw [Circuit.wireValue_of_lt _ _ _ (by simp)]
        rw [Circuit.wireValue_of_lt _ _ _ (by simp)]
        simp [Function.comp_apply]
      · intro gate hgateValue
        rw [reindexInputWire_gate_internal]
        rw [Circuit.wireValue_of_not_lt _ _ _ (by simp)]
        rw [Circuit.wireValue_of_not_lt _ _ _ (by simp)]
        simp only [Fin.val_natAdd, Nat.add_sub_cancel_left]
        change ((circuit.gates gate).rewire (reindexInputWire mapInput)).eval
            ((circuit.reindexInputs mapInput).wireValue input) =
          (circuit.gates gate).eval (circuit.wireValue (input ∘ mapInput))
        rw [Gate.eval_rewire_internal]
        unfold Gate.eval
        congr 1
        funext argument
        congr 1
        let source := (circuit.gates gate).inputs argument
        apply ih source.val (by
          have hsource := circuit.acyclic gate argument
          dsimp only [source]
          simp only [Fin.val_natAdd] at hgateValue
          omega) source rfl

theorem eval_reindexInputs_internal {B : Basis} {N N' M G : ℕ}
    [NeZero N] [NeZero N'] [NeZero M]
    (circuit : Circuit B N M G) (mapInput : Fin N → Fin N')
    (input : BitString N') :
    (circuit.reindexInputs mapInput).eval input =
      circuit.eval (input ∘ mapInput) := by
  funext output
  unfold Circuit.eval
  change ((circuit.outputs output).rewire (reindexInputWire mapInput)).eval
      ((circuit.reindexInputs mapInput).wireValue input) =
    (circuit.outputs output).eval (circuit.wireValue (input ∘ mapInput))
  rw [Gate.eval_rewire_internal]
  unfold Gate.eval
  congr 1
  funext argument
  congr 1
  exact wireValue_reindexInputs_internal circuit mapInput input
    ((circuit.outputs output).inputs argument)

end Circuit

end Complexity
