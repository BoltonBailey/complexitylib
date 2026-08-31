/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Padded.Defs
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Padded.Internal

/-!
# Padded fixed-width raw-circuit semantics

Valid fixed-width descriptions remain topologically ordered when all canonical
inactive slots are retained. This is the semantic target of the bounded
sequential encoded evaluator.
-/


public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace Description

/-- Every slot of a valid description, active or canonically padded, points to
a primary input or an earlier slot. -/
theorem slot_wellFormedAt_of_wellFormed
    {inputWidth gateBound : Nat}
    {description : Description inputWidth gateBound}
    (hdescription : description.WellFormed) (slot : Fin gateBound) :
    (description.slots slot).WellFormedAt (inputWidth + slot.val) :=
  slot_wellFormedAt_of_wellFormed_internal hdescription slot

/-- The padded raw circuit has exactly the fixed gate bound as its length. -/
@[simp] theorem length_toPaddedRawCircuit
    {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) :
    description.toPaddedRawCircuit.length = gateBound :=
  length_toPaddedRawCircuit_internal description

/-- A valid description's complete padded raw circuit is topologically
ordered. -/
theorem topologicallyWellFormed_toPaddedRawCircuit
    {inputWidth gateBound : Nat}
    {description : Description inputWidth gateBound}
    (hdescription : description.WellFormed) :
    description.toPaddedRawCircuit.TopologicallyWellFormed inputWidth :=
  topologicallyWellFormed_toPaddedRawCircuit_internal hdescription

end Description

end FixedWidth

end CircuitCode

end Complexity
