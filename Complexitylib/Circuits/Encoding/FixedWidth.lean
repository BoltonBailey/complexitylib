/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Defs
import Complexitylib.Circuits.Encoding.FixedWidth.Internal

/-!
# Fixed-width binary circuit descriptions

Bounded descriptions use one fixed-width gate array. Reference words have a
positive ceiling-logarithmic width, active gates are topologically ordered,
and inactive slots are canonically zero. This gives the approximate-counting
relation a finite, parser-free syntax while retaining `RawCircuit` semantics.
-/


public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

/-- Reference words always have positive width. -/
theorem one_le_referenceWidth (inputWidth gateBound : Nat) :
    1 ≤ referenceWidth inputWidth gateBound :=
  one_le_referenceWidth_internal inputWidth gateBound

/-- Gate-count words always have positive width. -/
theorem one_le_gateCountWidth (gateBound : Nat) :
    1 ≤ gateCountWidth gateBound :=
  one_le_gateCountWidth_internal gateBound

/-- The reference width represents every primary or bounded gate wire. -/
theorem inputWidth_add_gateBound_le_two_pow_referenceWidth
    (inputWidth gateBound : Nat) :
    inputWidth + gateBound ≤ 2 ^ referenceWidth inputWidth gateBound :=
  inputWidth_add_gateBound_le_two_pow_referenceWidth_internal
    inputWidth gateBound

/-- Every allowed positive gate count fits in the count word. -/
theorem gateBound_lt_two_pow_gateCountWidth (gateBound : Nat) :
    gateBound < 2 ^ gateCountWidth gateBound :=
  gateBound_lt_two_pow_gateCountWidth_internal gateBound

/-- A gate slot has exactly as many values as its advertised bit width. -/
theorem card_gateSlot (width : Nat) :
    Fintype.card (GateSlot width) = 2 ^ (3 + 2 * width) :=
  card_gateSlot_internal width

/-- Exact number of bounded descriptions before imposing validity. -/
theorem card_description (inputWidth gateBound : Nat) :
    Fintype.card (Description inputWidth gateBound) =
      (gateBound + 1) *
        2 ^ (gateBound * gateSlotWidth inputWidth gateBound) :=
  card_description_internal inputWidth gateBound

namespace Description

/-- The active count is within the fixed gate array. -/
theorem gateCountNat_le_gateBound {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) :
    description.gateCountNat ≤ gateBound :=
  gateCountNat_le_gateBound_internal description

/-- Converting active slots to raw syntax preserves the exact gate count. -/
@[simp] theorem length_toRawCircuit {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) :
    description.toRawCircuit.length = description.gateCountNat :=
  length_toRawCircuit_internal description

/-- Fixed-slot and raw-list topological validity agree exactly. -/
theorem topologicallyWellFormed_toRawCircuit_iff
    {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) :
    description.toRawCircuit.TopologicallyWellFormed inputWidth ↔
      description.TopologicallyWellFormed :=
  topologicallyWellFormed_toRawCircuit_iff_internal description

/-- A valid fixed-width description produces a valid raw circuit. -/
theorem wellFormed_toRawCircuit {inputWidth gateBound : Nat}
    {description : Description inputWidth gateBound}
    (hdescription : description.WellFormed) :
    description.toRawCircuit.WellFormed inputWidth :=
  wellFormed_toRawCircuit_internal hdescription

end Description

end FixedWidth

end CircuitCode

end Complexity
