/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.KeyedMinimumTournament.Family.Defs
public import Complexitylib.Circuits.KeyedMinimumTournament.Family.Internal

/-!
# Parallel keyed-record circuit families

This module packs a nonempty fixed-width family of key-payload circuits into
the recursive record layout consumed by the verified minimum tournament.
-/


public section

namespace Complexity

namespace Circuit

/-- Packed family evaluation recursively appends every key-payload record. -/
theorem eval_parallelKeyedRecordFamily
    {B : Basis} {inputWidth keyWidth payloadWidth : ℕ}
    [NeZero inputWidth] [NeZero keyWidth]
    (count : ℕ)
    (circuits : Fin (count + 1) →
      Σ internalGates,
        Circuit B inputWidth (keyWidth + payloadWidth) internalGates)
    (input : BitString inputWidth)
    (keys : Fin (count + 1) → BitString keyWidth)
    (payloads : Fin (count + 1) → BitString payloadWidth)
    (heval : ∀ index,
      (circuits index).2.eval input =
        Fin.append (keys index) (payloads index)) :
    (parallelKeyedRecordFamily count circuits).2.eval input =
      BitString.packKeyedRecords count keys payloads :=
  eval_parallelKeyedRecordFamily_internal
    count circuits input keys payloads heval

/-- Packed family size is exactly the sum of the source circuit sizes. -/
@[simp] theorem size_parallelKeyedRecordFamily
    {B : Basis} {inputWidth keyWidth payloadWidth : ℕ}
    [NeZero inputWidth] [NeZero keyWidth]
    (count : ℕ)
    (circuits : Fin (count + 1) →
      Σ internalGates,
        Circuit B inputWidth (keyWidth + payloadWidth) internalGates) :
    (parallelKeyedRecordFamily count circuits).2.size =
      ∑ index, (circuits index).2.size :=
  size_parallelKeyedRecordFamily_internal count circuits

end Circuit

end Complexity
