/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Layout
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Padded
import Complexitylib.Circuits.Encoding.FixedWidth.Codec
import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Gate

/-!
# Sequential fixed-width step semantics -- proof internals
-/


public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace Description

namespace EvaluationLayout

theorem decodedSlot_eq_of_code_internal
    {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound)
    (slot : Fin gateBound) (assignment : Nat → Bool)
    (hcode : ∀ coordinate,
      assignment coordinate.val = Description.encode description coordinate) :
    GateFormula.decodedSlot inputWidth gateBound slot assignment =
      description.slots slot := by
  have hprefix :
      GateFormula.codeOfAssignment inputWidth gateBound assignment =
        Description.encode description := by
    funext coordinate
    exact hcode coordinate
  unfold GateFormula.decodedSlot
  rw [hprefix, Description.slotBits_encode, GateSlot.decode_encode]

theorem eval_stepFormula_internal
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
          (slot_wellFormedAt_of_wellFormed hdescription slot).2⟩) := by
  have hdecoded := decodedSlot_eq_of_code_internal
    description slot assignment hcode
  have hslot :
      (GateFormula.decodedSlot inputWidth gateBound slot assignment).WellFormedAt
        (inputWidth + slot.val) := by
    rw [hdecoded]
    exact slot_wellFormedAt_of_wellFormed hdescription slot
  unfold stepFormula
  rw [GateFormula.eval_gate slot _ assignment hslot,
    hsources, hsources]
  simp only [hdecoded]

end EvaluationLayout

end Description

end FixedWidth

end CircuitCode

end Complexity
