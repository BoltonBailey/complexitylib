/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonProbeQuery.Defs
import Complexitylib.Circuits.BarringtonProbeQuery.Internal
import Complexitylib.Circuits.BarringtonTokenQuery

/-!
# Direct Barrington queries through canonical formula-code probes

This module replaces the complete encoded formula list by a numeric bit
oracle. With fuel covering the header and every token field, the first/last
occupied addresses and every fixed-address instruction agree exactly with the
reference Barrington compiler.

## Main results

- `barringtonProbeFirstOccupiedSlot?_eq` gives the structural first address.
- `barringtonProbeLastOccupiedSlot?_eq` gives the structural last address.
- `barringtonCompileProbeSlot?_eq_instruction?` gives the exact instruction at
  every fixed address.
-/

namespace Complexity

/-- Probe traversal over canonical formula bits computes the structural first
occupied Barrington address. -/
theorem barringtonProbeFirstOccupiedSlot?_eq (fuel : ℕ)
    (formula : BoolFormula) (bitFuel : ℕ)
    (hheader : formula.size + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ FormulaCode.tokens formula,
      token.codeLength ≤ bitFuel) :
    barringtonProbeFirstOccupiedSlot? fuel
        (FormulaCode.BitOracle.ofList (FormulaCode.encode formula))
        bitFuel ⟨0, formula.size⟩ =
      barringtonFirstOccupiedSlot? fuel formula := by
  calc
    _ = barringtonTokensFirstOccupiedSlot? fuel
        (FormulaCode.tokens formula) := by
      simpa [FormulaCode.encode, FormulaCode.encodeTokenStream] using
        (barringtonProbeOccupiedSlots_correct_context_internal fuel [] []
          formula bitFuel (by simpa using hheader)
            (by simpa using hbound)).1
    _ = _ := barringtonTokensFirstOccupiedSlot?_eq fuel formula

/-- Probe traversal over canonical formula bits computes the structural last
occupied Barrington address. -/
theorem barringtonProbeLastOccupiedSlot?_eq (fuel : ℕ)
    (formula : BoolFormula) (bitFuel : ℕ)
    (hheader : formula.size + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ FormulaCode.tokens formula,
      token.codeLength ≤ bitFuel) :
    barringtonProbeLastOccupiedSlot? fuel
        (FormulaCode.BitOracle.ofList (FormulaCode.encode formula))
        bitFuel ⟨0, formula.size⟩ =
      barringtonLastOccupiedSlot? fuel formula := by
  calc
    _ = barringtonTokensLastOccupiedSlot? fuel
        (FormulaCode.tokens formula) := by
      simpa [FormulaCode.encode, FormulaCode.encodeTokenStream] using
        (barringtonProbeOccupiedSlots_correct_context_internal fuel [] []
          formula bitFuel (by simpa using hheader)
            (by simpa using hbound)).2
    _ = _ := barringtonTokensLastOccupiedSlot?_eq fuel formula

/-- Every direct query through canonical formula-code probes agrees with the
selected instruction of the list-valued fixed Barrington schedule. -/
theorem barringtonCompileProbeSlot?_eq_instruction? (fuel : ℕ)
    (formula : BoolFormula) (bitFuel : ℕ)
    (target : Equiv.Perm (Fin 5)) (slot : ℕ)
    (hheader : formula.size + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ FormulaCode.tokens formula,
      token.codeLength ≤ bitFuel) :
    barringtonCompileProbeSlot? fuel
        (FormulaCode.BitOracle.ofList (FormulaCode.encode formula))
        bitFuel ⟨0, formula.size⟩ target slot =
      BPSlots.instruction?
        (barringtonCompileSlots fuel formula target) slot := by
  calc
    _ = barringtonCompileTokensSlot? fuel (FormulaCode.tokens formula)
        target slot := by
      simpa [FormulaCode.encode, FormulaCode.encodeTokenStream] using
        barringtonCompileProbeSlot?_correct_context_internal fuel [] []
          formula bitFuel target slot (by simpa using hheader)
            (by simpa using hbound)
    _ = _ :=
      barringtonCompileTokensSlot?_eq_instruction? fuel formula target slot

end Complexity
