/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonProbeQuery.Defs
import Complexitylib.Circuits.BarringtonTokenQuery.Internal
import Complexitylib.Circuits.FormulaEncoding.ProbeNavigation.Internal

/-!
# Direct Barrington queries through a formula-code oracle -- proof internals
-/

namespace Complexity

namespace FormulaCode

namespace BitOracle

theorem segmentRootToken?_ofList_encodeTokenStream_context_internal
    (before after : List Token) (formula : BoolFormula) (bitFuel : ℕ)
    (hheader : (before ++ tokens formula ++ after).length + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ before ++ tokens formula ++ after,
      token.codeLength ≤ bitFuel) :
    segmentRootToken?
        (ofList (encodeTokenStream (before ++ tokens formula ++ after)))
        bitFuel ⟨before.length, formula.size⟩ =
      (tokens formula).getLast? := by
  have hpositive : 0 < formula.size := by
    cases formula <;> simp [BoolFormula.size]
  rw [segmentRootToken?]
  rw [show formula.size = (formula.size - 1) + 1 by omega]
  simp only [TokenSegment.root?, Option.bind_eq_bind, Option.bind_some]
  have hglobal : before.length + (formula.size - 1) <
      (before ++ tokens formula ++ after).length := by
    simp
    omega
  rw [tokenValueAt?_ofList_encodeTokenStream_internal _ bitFuel _ hheader
    hglobal hbound]
  rw [← List.getElem?_eq_getElem hglobal]
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_append_right (by omega)]
  rw [show before.length + (formula.size - 1) - before.length =
    formula.size - 1 by omega]
  rw [List.getLast?_eq_getElem?]
  simp

end BitOracle

end FormulaCode

theorem barringtonProbeOccupiedSlots_correct_context_internal (fuel : ℕ)
    (before after : List FormulaCode.Token) (formula : BoolFormula)
    (bitFuel : ℕ)
    (hheader :
      (before ++ FormulaCode.tokens formula ++ after).length + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ before ++ FormulaCode.tokens formula ++ after,
      token.codeLength ≤ bitFuel) :
    barringtonProbeFirstOccupiedSlot? fuel
        (FormulaCode.BitOracle.ofList
          (FormulaCode.encodeTokenStream
            (before ++ FormulaCode.tokens formula ++ after)))
        bitFuel ⟨before.length, formula.size⟩ =
          barringtonTokensFirstOccupiedSlot? fuel
            (FormulaCode.tokens formula) ∧
      barringtonProbeLastOccupiedSlot? fuel
        (FormulaCode.BitOracle.ofList
          (FormulaCode.encodeTokenStream
            (before ++ FormulaCode.tokens formula ++ after)))
        bitFuel ⟨before.length, formula.size⟩ =
          barringtonTokensLastOccupiedSlot? fuel
            (FormulaCode.tokens formula) := by
  induction fuel generalizing before after formula with
  | zero =>
      have hroot :=
        FormulaCode.BitOracle.segmentRootToken?_ofList_encodeTokenStream_context_internal
          before after formula bitFuel hheader hbound
      cases formula <;>
        simp [FormulaCode.tokens, BoolFormula.size,
          List.append_assoc] at hroot <;>
        simp [barringtonProbeFirstOccupiedSlot?,
          barringtonProbeLastOccupiedSlot?,
          barringtonTokensFirstOccupiedSlot?,
          barringtonTokensLastOccupiedSlot?, FormulaCode.tokens,
          BoolFormula.size, List.append_assoc, hroot]
  | succ fuel ih =>
      have hroot :=
        FormulaCode.BitOracle.segmentRootToken?_ofList_encodeTokenStream_context_internal
          before after formula bitFuel hheader hbound
      cases formula with
      | var index =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          simp [barringtonProbeFirstOccupiedSlot?,
            barringtonProbeLastOccupiedSlot?,
            barringtonTokensFirstOccupiedSlot?,
            barringtonTokensLastOccupiedSlot?, FormulaCode.tokens,
            BoolFormula.size, hroot]
      | tru =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          simp [barringtonProbeFirstOccupiedSlot?,
            barringtonProbeLastOccupiedSlot?,
            barringtonTokensFirstOccupiedSlot?,
            barringtonTokensLastOccupiedSlot?, FormulaCode.tokens,
            BoolFormula.size, hroot]
      | fls =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          simp [barringtonProbeFirstOccupiedSlot?,
            barringtonProbeLastOccupiedSlot?,
            barringtonTokensFirstOccupiedSlot?,
            barringtonTokensLastOccupiedSlot?, FormulaCode.tokens,
            BoolFormula.size, hroot]
      | neg formula =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          have hchild := ih before (FormulaCode.Token.neg :: after) formula
            (by simpa [FormulaCode.tokens, List.append_assoc] using hheader)
            (by simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hchild' :
              barringtonProbeFirstOccupiedSlot? fuel
                  (FormulaCode.BitOracle.ofList
                    (FormulaCode.encodeTokenStream
                      (before ++ FormulaCode.tokens (.neg formula) ++ after)))
                  bitFuel ⟨before.length, formula.size⟩ =
                    barringtonTokensFirstOccupiedSlot? fuel
                      (FormulaCode.tokens formula) ∧
                barringtonProbeLastOccupiedSlot? fuel
                  (FormulaCode.BitOracle.ofList
                    (FormulaCode.encodeTokenStream
                      (before ++ FormulaCode.tokens (.neg formula) ++ after)))
                  bitFuel ⟨before.length, formula.size⟩ =
                    barringtonTokensLastOccupiedSlot? fuel
                      (FormulaCode.tokens formula) := by
            simpa [FormulaCode.tokens, List.append_assoc] using hchild
          simp [FormulaCode.tokens, List.append_assoc] at hchild'
          simp [barringtonProbeFirstOccupiedSlot?,
            barringtonProbeLastOccupiedSlot?,
            barringtonTokensFirstOccupiedSlot?,
            barringtonTokensLastOccupiedSlot?, FormulaCode.tokens,
            BoolFormula.size, List.append_assoc,
            FormulaCode.TokenSegment.dropRoot?, hroot,
            hchild'.1, hchild'.2]
      | conj left right =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          have hchildren :=
            FormulaCode.BitOracle.encodedBinaryChildren?_ofList_encodeTokenStream_internal
              before after left right FormulaCode.Token.conj bitFuel
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hheader)
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hchildren' :
              FormulaCode.BitOracle.encodedBinaryChildren?
                (FormulaCode.BitOracle.ofList
                  (FormulaCode.encodeTokenStream
                    (before ++ FormulaCode.tokens (.conj left right) ++
                      after)))
                bitFuel ⟨before.length, left.size + right.size + 1⟩ =
                some (⟨before.length, left.size⟩,
                  ⟨before.length + left.size, right.size⟩) := by
            simpa [FormulaCode.tokens, List.append_assoc] using hchildren
          simp [FormulaCode.tokens, List.append_assoc] at hchildren'
          have hleft := ih before
            (FormulaCode.tokens right ++ FormulaCode.Token.conj :: after)
            left
            (by simpa [FormulaCode.tokens, List.append_assoc] using hheader)
            (by simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hright := ih (before ++ FormulaCode.tokens left)
            (FormulaCode.Token.conj :: after) right
            (by simpa [FormulaCode.tokens, List.append_assoc] using hheader)
            (by simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hleft' := hleft
          have hright' := hright
          simp [List.append_assoc] at hleft' hright'
          simp [barringtonProbeFirstOccupiedSlot?,
            barringtonProbeLastOccupiedSlot?,
            barringtonTokensFirstOccupiedSlot?,
            barringtonTokensLastOccupiedSlot?, FormulaCode.tokens,
            BoolFormula.size, List.append_assoc,
            FormulaCode.postfixBinaryChildren?_tokens_assoc_internal,
            hroot, hchildren', hleft'.1, hright'.1]
          exact ⟨rfl, rfl⟩
      | disj left right =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          have hchildren :=
            FormulaCode.BitOracle.encodedBinaryChildren?_ofList_encodeTokenStream_internal
              before after left right FormulaCode.Token.disj bitFuel
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hheader)
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hchildren' :
              FormulaCode.BitOracle.encodedBinaryChildren?
                (FormulaCode.BitOracle.ofList
                  (FormulaCode.encodeTokenStream
                    (before ++ FormulaCode.tokens (.disj left right) ++
                      after)))
                bitFuel ⟨before.length, left.size + right.size + 1⟩ =
                some (⟨before.length, left.size⟩,
                  ⟨before.length + left.size, right.size⟩) := by
            simpa [FormulaCode.tokens, List.append_assoc] using hchildren
          simp [FormulaCode.tokens, List.append_assoc] at hchildren'
          have hleft := ih before
            (FormulaCode.tokens right ++ FormulaCode.Token.disj :: after)
            left
            (by simpa [FormulaCode.tokens, List.append_assoc] using hheader)
            (by simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hright := ih (before ++ FormulaCode.tokens left)
            (FormulaCode.Token.disj :: after) right
            (by simpa [FormulaCode.tokens, List.append_assoc] using hheader)
            (by simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hleft' := hleft
          have hright' := hright
          simp [List.append_assoc] at hleft' hright'
          simp [barringtonProbeFirstOccupiedSlot?,
            barringtonProbeLastOccupiedSlot?,
            barringtonTokensFirstOccupiedSlot?,
            barringtonTokensLastOccupiedSlot?, FormulaCode.tokens,
            BoolFormula.size, List.append_assoc,
            FormulaCode.postfixBinaryChildren?_tokens_assoc_internal,
            hroot, hchildren', hleft'.1, hright'.1]

theorem barringtonCompileProbeSlot?_correct_context_internal (fuel : ℕ)
    (before after : List FormulaCode.Token) (formula : BoolFormula)
    (bitFuel : ℕ) (target : Equiv.Perm (Fin 5)) (slot : ℕ)
    (hheader :
      (before ++ FormulaCode.tokens formula ++ after).length + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ before ++ FormulaCode.tokens formula ++ after,
      token.codeLength ≤ bitFuel) :
    barringtonCompileProbeSlot? fuel
        (FormulaCode.BitOracle.ofList
          (FormulaCode.encodeTokenStream
            (before ++ FormulaCode.tokens formula ++ after)))
        bitFuel ⟨before.length, formula.size⟩ target slot =
      barringtonCompileTokensSlot? fuel
        (FormulaCode.tokens formula) target slot := by
  induction fuel generalizing before after formula target slot with
  | zero =>
      have hroot :=
        FormulaCode.BitOracle.segmentRootToken?_ofList_encodeTokenStream_context_internal
          before after formula bitFuel hheader hbound
      cases formula <;>
        simp [FormulaCode.tokens, BoolFormula.size,
          List.append_assoc] at hroot ⊢ <;>
        simp [barringtonCompileProbeSlot?,
          barringtonCompileTokensSlot?, hroot]
  | succ fuel ih =>
      have hroot :=
        FormulaCode.BitOracle.segmentRootToken?_ofList_encodeTokenStream_context_internal
          before after formula bitFuel hheader hbound
      cases formula with
      | var index =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot ⊢
          simp [barringtonCompileProbeSlot?,
            barringtonCompileTokensSlot?, hroot]
      | tru =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot ⊢
          simp [barringtonCompileProbeSlot?,
            barringtonCompileTokensSlot?, hroot]
      | fls =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot ⊢
          simp [barringtonCompileProbeSlot?,
            barringtonCompileTokensSlot?, hroot]
      | neg formula =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          have hoccupied :=
            barringtonProbeOccupiedSlots_correct_context_internal fuel before
              (FormulaCode.Token.neg :: after) formula bitFuel
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hheader)
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hquery :
              barringtonCompileProbeSlot? fuel
                  (FormulaCode.BitOracle.ofList
                    (FormulaCode.encodeTokenStream
                      (before ++ FormulaCode.tokens (.neg formula) ++ after)))
                  bitFuel ⟨before.length, formula.size⟩ target⁻¹ =
                barringtonCompileTokensSlot? fuel
                  (FormulaCode.tokens formula) target⁻¹ := by
            funext querySlot
            simpa [FormulaCode.tokens, List.append_assoc] using
              ih before (FormulaCode.Token.neg :: after) formula target⁻¹
                querySlot
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hheader)
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          simp [FormulaCode.tokens, List.append_assoc] at hquery
          have hoccupied' := hoccupied
          simp [List.append_assoc] at hoccupied'
          simp [barringtonCompileProbeSlot?,
            barringtonCompileTokensSlot?, FormulaCode.tokens,
            BoolFormula.size, List.append_assoc,
            FormulaCode.TokenSegment.dropRoot?, hroot, hquery,
            hoccupied'.2]
      | conj left right =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          have hchildren :=
            FormulaCode.BitOracle.encodedBinaryChildren?_ofList_encodeTokenStream_internal
              before after left right FormulaCode.Token.conj bitFuel
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hheader)
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hchildren' :
              FormulaCode.BitOracle.encodedBinaryChildren?
                (FormulaCode.BitOracle.ofList
                  (FormulaCode.encodeTokenStream
                    (before ++ FormulaCode.tokens (.conj left right) ++
                      after)))
                bitFuel ⟨before.length, left.size + right.size + 1⟩ =
                some (⟨before.length, left.size⟩,
                  ⟨before.length + left.size, right.size⟩) := by
            simpa [FormulaCode.tokens, List.append_assoc] using hchildren
          simp [FormulaCode.tokens, List.append_assoc] at hchildren'
          have hleftQuery :
              barringtonCompileProbeSlot? fuel
                  (FormulaCode.BitOracle.ofList
                    (FormulaCode.encodeTokenStream
                      (before ++ FormulaCode.tokens (.conj left right) ++
                        after)))
                  bitFuel ⟨before.length, left.size⟩
                    (barringtonLeft target) =
                barringtonCompileTokensSlot? fuel
                  (FormulaCode.tokens left) (barringtonLeft target) := by
            funext querySlot
            simpa [FormulaCode.tokens, List.append_assoc] using
              ih before
                (FormulaCode.tokens right ++ FormulaCode.Token.conj :: after)
                left (barringtonLeft target) querySlot
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hheader)
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hrightQuery :
              barringtonCompileProbeSlot? fuel
                  (FormulaCode.BitOracle.ofList
                    (FormulaCode.encodeTokenStream
                      (before ++ FormulaCode.tokens (.conj left right) ++
                        after)))
                  bitFuel ⟨before.length + left.size, right.size⟩
                    (barringtonRight target) =
                barringtonCompileTokensSlot? fuel
                  (FormulaCode.tokens right) (barringtonRight target) := by
            funext querySlot
            simpa [FormulaCode.tokens, List.append_assoc] using
              ih (before ++ FormulaCode.tokens left)
                (FormulaCode.Token.conj :: after) right
                (barringtonRight target) querySlot
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hheader)
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          simp [FormulaCode.tokens, List.append_assoc] at hleftQuery hrightQuery
          simp [barringtonCompileProbeSlot?,
            barringtonCompileTokensSlot?, FormulaCode.tokens,
            BoolFormula.size, List.append_assoc,
            FormulaCode.postfixBinaryChildren?_tokens_assoc_internal,
            hroot, hchildren', hleftQuery, hrightQuery]
      | disj left right =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          have hchildren :=
            FormulaCode.BitOracle.encodedBinaryChildren?_ofList_encodeTokenStream_internal
              before after left right FormulaCode.Token.disj bitFuel
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hheader)
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hchildren' :
              FormulaCode.BitOracle.encodedBinaryChildren?
                (FormulaCode.BitOracle.ofList
                  (FormulaCode.encodeTokenStream
                    (before ++ FormulaCode.tokens (.disj left right) ++
                      after)))
                bitFuel ⟨before.length, left.size + right.size + 1⟩ =
                some (⟨before.length, left.size⟩,
                  ⟨before.length + left.size, right.size⟩) := by
            simpa [FormulaCode.tokens, List.append_assoc] using hchildren
          simp [FormulaCode.tokens, List.append_assoc] at hchildren'
          have hleftOccupied :=
            barringtonProbeOccupiedSlots_correct_context_internal fuel before
              (FormulaCode.tokens right ++ FormulaCode.Token.disj :: after)
              left bitFuel
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hheader)
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hrightOccupied :=
            barringtonProbeOccupiedSlots_correct_context_internal fuel
              (before ++ FormulaCode.tokens left)
              (FormulaCode.Token.disj :: after) right bitFuel
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hheader)
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hleftOccupied' := hleftOccupied
          have hrightOccupied' := hrightOccupied
          simp [List.append_assoc] at hleftOccupied' hrightOccupied'
          have hleftQuery (childTarget : Equiv.Perm (Fin 5)) :
              barringtonCompileProbeSlot? fuel
                  (FormulaCode.BitOracle.ofList
                    (FormulaCode.encodeTokenStream
                      (before ++ FormulaCode.tokens (.disj left right) ++
                        after)))
                  bitFuel ⟨before.length, left.size⟩ childTarget =
                barringtonCompileTokensSlot? fuel
                  (FormulaCode.tokens left) childTarget := by
            funext querySlot
            simpa [FormulaCode.tokens, List.append_assoc] using
              ih before
                (FormulaCode.tokens right ++ FormulaCode.Token.disj :: after)
                left childTarget querySlot
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hheader)
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hrightQuery (childTarget : Equiv.Perm (Fin 5)) :
              barringtonCompileProbeSlot? fuel
                  (FormulaCode.BitOracle.ofList
                    (FormulaCode.encodeTokenStream
                      (before ++ FormulaCode.tokens (.disj left right) ++
                        after)))
                  bitFuel ⟨before.length + left.size, right.size⟩ childTarget =
                barringtonCompileTokensSlot? fuel
                  (FormulaCode.tokens right) childTarget := by
            funext querySlot
            simpa [FormulaCode.tokens, List.append_assoc] using
              ih (before ++ FormulaCode.tokens left)
                (FormulaCode.Token.disj :: after) right childTarget querySlot
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hheader)
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          simp [FormulaCode.tokens, List.append_assoc] at hleftQuery hrightQuery
          simp [barringtonCompileProbeSlot?,
            barringtonCompileTokensSlot?, FormulaCode.tokens,
            BoolFormula.size, List.append_assoc,
            FormulaCode.postfixBinaryChildren?_tokens_assoc_internal,
            hroot, hchildren', hleftOccupied'.2,
            hrightOccupied'.1, hrightOccupied'.2,
            hleftQuery, hrightQuery]

end Complexity
