/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Composition.Defs

/-!
# Circuit input reindexing -- definitions

This layer transports a circuit along an arbitrary map from its original
primary inputs into a new positive input tuple. Internal gates keep their
order and every source internal wire retains its gate index.
-/


@[expose] public section

namespace Complexity

namespace Circuit

/-- Map an input-or-gate wire into a new primary-input namespace while
preserving the internal-gate index. -/
def reindexInputWire {N N' G : ℕ} (mapInput : Fin N → Fin N') :
    Fin (N + G) → Fin (N' + G) :=
  Fin.addCases (fun input => Fin.castAdd G (mapInput input))
    (fun gate => Fin.natAdd N' gate)

/-- Reindex a circuit's primary inputs without changing its gates, outputs, or
resource counts. -/
def reindexInputs {B : Basis} {N N' M G : ℕ} [NeZero N] [NeZero N']
    [NeZero M] (circuit : Circuit B N M G) (mapInput : Fin N → Fin N') :
    Circuit B N' M G where
  gates gate := (circuit.gates gate).rewire (reindexInputWire mapInput)
  outputs output :=
    (circuit.outputs output).rewire (reindexInputWire mapInput)
  acyclic gate argument := by
    let source := (circuit.gates gate).inputs argument
    have hsource : source.val < N + gate.val := circuit.acyclic gate argument
    change (reindexInputWire mapInput source).val < N' + gate.val
    refine Fin.addCases (motive := fun wire : Fin (N + G) =>
      wire.val < N + gate.val →
        (reindexInputWire mapInput wire).val < N' + gate.val) ?_ ?_ source hsource
    · intro input _
      simp [reindexInputWire]
      omega
    · intro prior hprior
      simp only [Fin.val_natAdd] at hprior
      simp [reindexInputWire]
      omega

end Circuit

end Complexity
