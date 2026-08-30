/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.KeyedMinimumTournament.Defs
public import Complexitylib.Circuits.KeyedMinimumTournament.Internal

/-!
# Keyed minimum tournaments

This module exposes a sequential circuit tournament that selects one minimum-key
record from any nonempty fixed-width family while retaining its payload.
-/


public section

namespace Complexity

namespace BitString

/-- The recursive record layout is the usual row count times record width. -/
theorem keyedTournamentInputWidth_eq (count recordWidth : ℕ) :
    keyedTournamentInputWidth count recordWidth = (count + 1) * recordWidth :=
  keyedTournamentInputWidth_eq_internal count recordWidth

/-- The tournament winner is one of the supplied key-payload records. -/
theorem exists_unsignedMinimumKeyedRecord_eq
    {keyWidth payloadWidth : ℕ} (count : ℕ)
    (keys : Fin (count + 1) → BitString keyWidth)
    (payloads : Fin (count + 1) → BitString payloadWidth) :
    ∃ index,
      unsignedMinimumKeyedRecord count keys payloads =
        (keys index, payloads index) :=
  exists_unsignedMinimumKeyedRecord_eq_internal count keys payloads

/-- The winning key is no larger than every supplied key. -/
theorem unsignedMinimumKeyedRecord_key_le
    {keyWidth payloadWidth : ℕ} (count : ℕ)
    (keys : Fin (count + 1) → BitString keyWidth)
    (payloads : Fin (count + 1) → BitString payloadWidth)
    (index : Fin (count + 1)) :
    (unsignedMinimumKeyedRecord count keys payloads).1.unsignedValue ≤
      (keys index).unsignedValue :=
  unsignedMinimumKeyedRecord_key_le_internal count keys payloads index

end BitString

namespace Circuit

/-- The tournament returns the semantic left-associated minimum record. -/
@[simp] theorem eval_unsignedKeyedMinTournament
    (keyWidth payloadWidth : ℕ) [NeZero keyWidth]
    (count : ℕ) (keys : Fin (count + 1) → BitString keyWidth)
    (payloads : Fin (count + 1) → BitString payloadWidth) :
    (unsignedKeyedMinTournament keyWidth payloadWidth count).2.eval
        (BitString.packKeyedRecords count keys payloads) =
      let winner :=
        BitString.unsignedMinimumKeyedRecord count keys payloads
      Fin.append winner.1 winner.2 :=
  eval_unsignedKeyedMinTournament_internal
    keyWidth payloadWidth count keys payloads

/-- Exact tournament size: record copies plus one keyed selector per comparison. -/
@[simp] theorem size_unsignedKeyedMinTournament
    (keyWidth payloadWidth : ℕ) [NeZero keyWidth] (count : ℕ) :
    (unsignedKeyedMinTournament keyWidth payloadWidth count).2.size =
      (count + 1) * (keyWidth + payloadWidth) +
        count * (20 * keyWidth + 5 * payloadWidth + 1) :=
  size_unsignedKeyedMinTournament_internal keyWidth payloadWidth count

end Circuit

end Complexity
