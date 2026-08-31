/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Step.Internal

/-!
# Sequential fixed-width step semantics

The laid-out formula for one gate agrees with that description slot's raw-gate
semantics whenever the assignment contains the encoded description prefix and
the declared source formulas realize the available wire values.
-/


public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace Description

namespace EvaluationLayout

/-- The code prefix of an assignment decodes each gate formula's slot exactly. -/
theorem decodedSlot_eq_of_code
    {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound)
    (slot : Fin gateBound) (assignment : Nat → Bool)
    (hcode : ∀ coordinate,
      assignment coordinate.val = Description.encode description coordinate) :
    GateFormula.decodedSlot inputWidth gateBound slot assignment =
      description.slots slot :=
  decodedSlot_eq_of_code_internal description slot assignment hcode

/-- A sequentially laid-out gate formula realizes the corresponding raw gate
on any supplied family of available wire values. -/
theorem eval_stepFormula
    {inputWidth gateBound : Nat}
    {description : Description inputWidth gateBound}
    (hdescription : description.WellFormed) (slot : Fin gateBound)
    (wireValue : Fin (inputWidth + slot.val) → Bool)
    (assignment : Nat → Bool)
    (hcode : ∀ coordinate,
      assignment coordinate.val = Description.encode description coordinate)
    (hsources : ∀ source,
      (sourceFormula inputWidth gateBound slot source).eval assignment =
        wireValue source) :
    (stepFormula inputWidth gateBound slot).eval assignment =
      (description.slots slot).toRawGate.eval
        (wireValue ⟨(description.slots slot).input0Value,
          (slot_wellFormedAt_of_wellFormed hdescription slot).1⟩)
        (wireValue ⟨(description.slots slot).input1Value,
          (slot_wellFormedAt_of_wellFormed hdescription slot).2⟩) :=
  eval_stepFormula_internal hdescription slot wireValue assignment
    hcode hsources

end EvaluationLayout

end Description

end FixedWidth

end CircuitCode

end Complexity
