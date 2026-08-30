/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.KeyedMinimum

/-!
# Keyed minimum tournaments -- definitions

The tournament consumes `count + 1` key-payload records. Its recursively
appended input layout makes each construction step a literal prefix projection
plus one final-record projection, avoiding arithmetic casts in the circuit DAG.
-/


@[expose] public section

namespace Complexity

namespace BitString

/-- Width of `count + 1` recursively appended fixed-width records. -/
def keyedTournamentInputWidth : ℕ → ℕ → ℕ
  | 0, recordWidth => recordWidth
  | count + 1, recordWidth =>
      keyedTournamentInputWidth count recordWidth + recordWidth

instance instNeZeroKeyedTournamentInputWidth
    (count keyWidth payloadWidth : ℕ) [NeZero keyWidth] :
    NeZero (keyedTournamentInputWidth count (keyWidth + payloadWidth)) :=
  ⟨by
    induction count with
    | zero =>
        simp only [keyedTournamentInputWidth]
        have hkey : 0 < keyWidth := Nat.pos_of_ne_zero (NeZero.ne keyWidth)
        omega
    | succ count ih =>
        simp only [keyedTournamentInputWidth]
        have hprior :
            0 < keyedTournamentInputWidth count (keyWidth + payloadWidth) :=
          Nat.pos_of_ne_zero ih
        omega⟩

/-- Pack `count + 1` key-payload records by recursively appending the last one. -/
def packKeyedRecords {keyWidth payloadWidth : ℕ} :
    (count : ℕ) →
      (Fin (count + 1) → BitString keyWidth) →
      (Fin (count + 1) → BitString payloadWidth) →
      BitString (keyedTournamentInputWidth count (keyWidth + payloadWidth))
  | 0, keys, payloads => Fin.append (keys 0) (payloads 0)
  | count + 1, keys, payloads =>
      Fin.append
        (packKeyedRecords count
          (fun index => keys index.castSucc)
          (fun index => payloads index.castSucc))
        (Fin.append (keys (Fin.last (count + 1)))
          (payloads (Fin.last (count + 1))))

/-- Semantic winner of a left-associated keyed minimum tournament. -/
def unsignedMinimumKeyedRecord {keyWidth payloadWidth : ℕ} :
    (count : ℕ) →
      (Fin (count + 1) → BitString keyWidth) →
      (Fin (count + 1) → BitString payloadWidth) →
      BitString keyWidth × BitString payloadWidth
  | 0, keys, payloads => (keys 0, payloads 0)
  | count + 1, keys, payloads =>
      let prefixWinner := unsignedMinimumKeyedRecord count
        (fun index => keys index.castSucc)
        (fun index => payloads index.castSucc)
      let lastRecord :=
        (keys (Fin.last (count + 1)), payloads (Fin.last (count + 1)))
      if prefixWinner.1.unsignedValue ≤ lastRecord.1.unsignedValue then
        prefixWinner
      else
        lastRecord

end BitString

namespace Circuit

/-- Sequential keyed-minimum tournament over `count + 1` packed records. -/
noncomputable def unsignedKeyedMinTournament
    (keyWidth payloadWidth : ℕ) [NeZero keyWidth] :
    (count : ℕ) →
      Σ internalGates,
        Circuit Basis.andOr2
          (BitString.keyedTournamentInputWidth count
            (keyWidth + payloadWidth))
          (keyWidth + payloadWidth) internalGates
  | 0 => ⟨0, projectInputs (fun input => input)⟩
  | count + 1 =>
      let prior := unsignedKeyedMinTournament keyWidth payloadWidth count
      let priorOnFullInput := prior.2.reindexInputs
        (Fin.castAdd (keyWidth + payloadWidth))
      let lastRecord := projectInputs
        (Fin.natAdd
          (BitString.keyedTournamentInputWidth count
            (keyWidth + payloadWidth)))
      let candidates := priorOnFullInput.parallel lastRecord
      ⟨_, (unsignedKeyedMin keyWidth payloadWidth).compose candidates⟩

end Circuit

end Complexity
