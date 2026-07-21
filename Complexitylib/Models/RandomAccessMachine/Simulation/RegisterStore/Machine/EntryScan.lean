/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryScan.Defs
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryScan.Internal.Sem
import Complexitylib.Models.TuringMachine.Hoare.Space

/-!
# Bounded sparse-entry scan

This module exposes the complete time-bounded contract for the fixed sparse
store scanner. The runtime entry count is read from a canonical binary tape;
it is not hardwired into the finite controller.
-/

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Scan a runtime-sized sparse store. A successful endpoint contains the
first matching entry's decoded value; a miss certifies that every address was
different. Input, output, and every work tape outside the ten-tape assignment
are preserved exactly. -/
theorem entryScanTM_hoareTime_frame {n : ℕ}
    (tapes : EntryScanTapes n) (store : Store) (queryBits : List Bool)
    (initialWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hready : EntryScanReady tapes.entry (store.flatMap Entry.encode)
      queryBits initialWork initialWork)
    (hcount : (initialWork tapes.count).HasBinaryNat store.length)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (entryScanTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryScanOutcome tapes store queryBits initialWork work ∧
        out = out₀)
      (entryScanTime tapes queryBits store) :=
  entryScanTM_hoareTime_frame_internal tapes store queryBits initialWork
    inp₀ out₀ hready hcount hinput houtput

/-- The bounded scanner preserves one-way output safety. -/
theorem entryScanTM_isTransducer {n : ℕ} (tapes : EntryScanTapes n) :
    (entryScanTM tapes).IsTransducer := by
  intro state iHead wHeads oHead
  rcases state with phase | nested
  · cases phase <;> cases oHead <;>
      simp [entryScanTM, TM.allReadBack, TM.allIdle, TM.idleDir] <;>
      split <;> simp
  · rcases nested with body | pred
    · simp only [entryScanTM]
      split
      · split <;> cases oHead <;> simp [TM.allReadBack, TM.idleDir]
      · exact entryScanStepTM_isTransducer tapes.entry body iHead wHeads oHead
    · simp only [entryScanTM]
      split
      · cases oHead <;> simp [TM.allReadBack, TM.idleDir]
      · exact TM.binaryPredTM_isTransducer tapes.count pred iHead wHeads oHead

/-- Coarse all-prefix auxiliary-space envelope for the bounded scan. -/
theorem entryScanTM_prefix_withinAuxSpace {n : ℕ}
    (tapes : EntryScanTapes n) (store : Store) (queryBits : List Bool)
    (inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n (entryScanTM tapes).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (entryScanTM tapes).reachesIn time start current)
    (htime : time ≤ entryScanTime tapes queryBits store) :
    current.WithinAuxSpace inputLength
      (initialSpace + entryScanTime tapes queryBits store) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

end Machine

end RegisterStore

end RAM

end Complexity
