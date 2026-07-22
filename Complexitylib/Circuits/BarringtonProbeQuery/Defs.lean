/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonTokenQuery.Defs
import Complexitylib.Circuits.FormulaEncoding.ProbeNavigation.Defs

/-!
# Direct Barrington queries through a position-indexed formula-code oracle

These recurrences are the pure semantics of the restartable-probe controller.
Every source-code read is a numeric oracle query. The controller retains only
the current postfix segment and follows one selected base-four address; binary
child spans are recovered by repeated oracle token queries.
-/

namespace Complexity

namespace FormulaCode

namespace BitOracle

/-- Query the root token of a nonempty segment through a bit oracle. -/
def segmentRootToken? (query : BitOracle) (bitFuel : ℕ)
    (segment : TokenSegment) : Option Token := do
  let root ← segment.root?
  tokenValueAt? query bitFuel root

end BitOracle

end FormulaCode

/-- First occupied fixed address computed through source-code probes. -/
def barringtonProbeFirstOccupiedSlot? : ℕ → FormulaCode.BitOracle → ℕ →
    FormulaCode.TokenSegment → Option ℕ
  | 0, query, bitFuel, segment =>
      match FormulaCode.BitOracle.segmentRootToken? query bitFuel segment with
      | some (.var _) | some .tru => some 0
      | _ => none
  | fuel + 1, query, bitFuel, segment =>
      match FormulaCode.BitOracle.segmentRootToken? query bitFuel segment with
      | some (.var _) | some .tru => some 0
      | some .fls => none
      | some .neg =>
          match segment.dropRoot? with
          | none => none
          | some child =>
              some ((barringtonProbeFirstOccupiedSlot?
                fuel query bitFuel child).getD 0)
      | some .conj =>
          match FormulaCode.BitOracle.encodedBinaryChildren?
              query bitFuel segment with
          | none => none
          | some (left, right) =>
              match barringtonProbeFirstOccupiedSlot?
                  fuel query bitFuel left with
              | some slot => some slot
              | none =>
                  (barringtonProbeFirstOccupiedSlot?
                    fuel query bitFuel right).map (4 ^ fuel + ·)
      | some .disj =>
          match FormulaCode.BitOracle.encodedBinaryChildren?
              query bitFuel segment with
          | none => none
          | some (left, _) =>
              some ((barringtonProbeFirstOccupiedSlot?
                fuel query bitFuel left).getD 0)
      | none => none

/-- Last occupied fixed address computed through source-code probes. -/
def barringtonProbeLastOccupiedSlot? : ℕ → FormulaCode.BitOracle → ℕ →
    FormulaCode.TokenSegment → Option ℕ
  | 0, query, bitFuel, segment =>
      match FormulaCode.BitOracle.segmentRootToken? query bitFuel segment with
      | some (.var _) | some .tru => some 0
      | _ => none
  | fuel + 1, query, bitFuel, segment =>
      match FormulaCode.BitOracle.segmentRootToken? query bitFuel segment with
      | some (.var _) | some .tru => some 0
      | some .fls => none
      | some .neg =>
          match segment.dropRoot? with
          | none => none
          | some child =>
              some ((barringtonProbeLastOccupiedSlot?
                fuel query bitFuel child).getD 0)
      | some .conj =>
          match FormulaCode.BitOracle.encodedBinaryChildren?
              query bitFuel segment with
          | none => none
          | some (left, right) =>
              let blockSize := 4 ^ fuel
              match barringtonProbeFirstOccupiedSlot?
                  fuel query bitFuel right with
              | some slot =>
                  some (3 * blockSize + (blockSize - 1 - slot))
              | none =>
                  (barringtonProbeFirstOccupiedSlot?
                    fuel query bitFuel left).map
                      fun slot => 2 * blockSize + (blockSize - 1 - slot)
      | some .disj =>
          match FormulaCode.BitOracle.encodedBinaryChildren?
              query bitFuel segment with
          | none => none
          | some (_, right) =>
              let blockSize := 4 ^ fuel
              let firstRight :=
                (barringtonProbeFirstOccupiedSlot?
                  fuel query bitFuel right).getD 0
              some (3 * blockSize + (blockSize - 1 - firstRight))
      | none => none

/-- Query one fixed-address Barrington instruction through source-code probes. -/
def barringtonCompileProbeSlot? : ℕ → FormulaCode.BitOracle → ℕ →
    FormulaCode.TokenSegment → Equiv.Perm (Fin 5) → ℕ → Option (BPInstr 5)
  | fuel, query, bitFuel, segment, target, slot =>
      match fuel,
          FormulaCode.BitOracle.segmentRootToken? query bitFuel segment with
      | _, some (.var index) =>
          if slot = 0 then some ⟨index, 1, target⟩ else none
      | _, some .tru =>
          if slot = 0 then some (BPInstr.const target) else none
      | _, some .fls => none
      | 0, _ => none
      | fuel + 1, some .neg =>
          match segment.dropRoot? with
          | none => none
          | some child =>
              let blockSize := 4 ^ fuel
              if slot < blockSize then
                barringtonPostMulSlot?
                  (barringtonCompileProbeSlot?
                    fuel query bitFuel child target⁻¹)
                  (barringtonProbeLastOccupiedSlot?
                    fuel query bitFuel child)
                  target slot
              else
                none
      | fuel + 1, some .conj =>
          match FormulaCode.BitOracle.encodedBinaryChildren?
              query bitFuel segment with
          | none => none
          | some (left, right) =>
              let blockSize := 4 ^ fuel
              let leftQuery := barringtonCompileProbeSlot?
                fuel query bitFuel left (barringtonLeft target)
              let rightQuery := barringtonCompileProbeSlot?
                fuel query bitFuel right (barringtonRight target)
              if slot < blockSize then
                leftQuery slot
              else if slot < 2 * blockSize then
                rightQuery (slot - blockSize)
              else if slot < 3 * blockSize then
                barringtonInverseSlot? blockSize leftQuery
                  (slot - 2 * blockSize)
              else if slot < 4 * blockSize then
                barringtonInverseSlot? blockSize rightQuery
                  (slot - 3 * blockSize)
              else
                none
      | fuel + 1, some .disj =>
          match FormulaCode.BitOracle.encodedBinaryChildren?
              query bitFuel segment with
          | none => none
          | some (left, right) =>
              let blockSize := 4 ^ fuel
              let innerTarget := target⁻¹
              let leftTarget := barringtonLeft innerTarget
              let rightTarget := barringtonRight innerTarget
              let leftQuery := barringtonPostMulSlot?
                (barringtonCompileProbeSlot?
                  fuel query bitFuel left leftTarget⁻¹)
                (barringtonProbeLastOccupiedSlot?
                  fuel query bitFuel left) leftTarget
              let rightQuery := barringtonPostMulSlot?
                (barringtonCompileProbeSlot?
                  fuel query bitFuel right rightTarget⁻¹)
                (barringtonProbeLastOccupiedSlot?
                  fuel query bitFuel right) rightTarget
              let commutatorQuery := fun localSlot =>
                if localSlot < blockSize then
                  leftQuery localSlot
                else if localSlot < 2 * blockSize then
                  rightQuery (localSlot - blockSize)
                else if localSlot < 3 * blockSize then
                  barringtonInverseSlot? blockSize leftQuery
                    (localSlot - 2 * blockSize)
                else if localSlot < 4 * blockSize then
                  barringtonInverseSlot? blockSize rightQuery
                    (localSlot - 3 * blockSize)
                else
                  none
              let firstRight :=
                (barringtonProbeFirstOccupiedSlot?
                  fuel query bitFuel right).getD 0
              let commutatorLast :=
                3 * blockSize + (blockSize - 1 - firstRight)
              barringtonPostMulSlot? commutatorQuery
                (some commutatorLast) target slot
      | _, none => none

end Complexity
