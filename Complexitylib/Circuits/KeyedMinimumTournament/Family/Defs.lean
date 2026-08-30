/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Composition.Defs
public import Complexitylib.Circuits.KeyedMinimumTournament.Defs

/-!
# Parallel keyed-record circuit families -- definitions

A nonempty family of circuits with one fixed key-payload output width is packed
recursively in the exact layout consumed by `unsignedKeyedMinTournament`.
-/


@[expose] public section

namespace Complexity

namespace Circuit

/-- Pack `count + 1` fixed-width record circuits in parallel. -/
noncomputable def parallelKeyedRecordFamily
    {B : Basis} {inputWidth keyWidth payloadWidth : ℕ}
    [NeZero inputWidth] [NeZero keyWidth] :
    (count : ℕ) →
      (Fin (count + 1) →
        Σ internalGates,
          Circuit B inputWidth (keyWidth + payloadWidth) internalGates) →
      Σ internalGates,
        Circuit B inputWidth
          (BitString.keyedTournamentInputWidth count
            (keyWidth + payloadWidth)) internalGates
  | 0, circuits => circuits 0
  | count + 1, circuits =>
      let prior := parallelKeyedRecordFamily count
        (fun index => circuits index.castSucc)
      let last := circuits (Fin.last (count + 1))
      ⟨_, prior.2.parallel last.2⟩

end Circuit

end Complexity
