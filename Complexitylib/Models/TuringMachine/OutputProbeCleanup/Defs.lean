/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbe.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BlankWorkPrefixMany.Defs

/-!
# Restartable output-probe cleanup -- definitions

The retargeted probe owns `n` source scratch tapes, one query countdown, and
one captured-bit tape. Cleanup adds one reusable zero counter and one preserved
binary limit, rewinds the input, and blanks the source scratch/capture tapes.
-/

namespace Complexity

namespace TM

/-- Embed one source work index in the full cleanup frame. -/
def outputProbeCleanupSourceIdx {n : ℕ} (idx : Fin n) : Fin (n + 4) :=
  ⟨idx, by omega⟩

/-- Physical query-countdown index. -/
def outputProbeCleanupCountdownIdx (n : ℕ) : Fin (n + 4) :=
  ⟨n, by omega⟩

/-- Physical captured-bit index. -/
def outputProbeCleanupCaptureIdx (n : ℕ) : Fin (n + 4) :=
  ⟨n + 1, by omega⟩

/-- Reusable zero counter used by sparse-prefix cleanup. -/
def outputProbeCleanupCounterIdx (n : ℕ) : Fin (n + 4) :=
  ⟨n + 2, by omega⟩

/-- Preserved binary cleanup limit. -/
def outputProbeCleanupLimitIdx (n : ℕ) : Fin (n + 4) :=
  ⟨n + 3, by omega⟩

/-- Source scratch tapes followed by the captured-bit tape. -/
def outputProbeCleanupTargets (n : ℕ) : List (Fin (n + 4)) :=
  List.ofFn outputProbeCleanupSourceIdx ++ [outputProbeCleanupCaptureIdx n]

/-- Literal input tape after rewinding to the first ordinary cell. -/
def outputProbeRewoundInput (tape : Tape) : Tape where
  head := 1
  cells := tape.cells

/-- Rewind the shared input, then reset every dirty probe-owned work tape. -/
def outputProbeCleanupTM (n : ℕ) : TM (n + 4) :=
  seqTM rewindInputTM
    (rewindBlankWorkPrefixManyTM (outputProbeCleanupCounterIdx n)
      (outputProbeCleanupLimitIdx n) (outputProbeCleanupTargets n))

/-- Exact cleanup runtime. -/
def outputProbeCleanupTime (n inputHeadBound limit : ℕ)
    (headBound : Fin (n + 4) → ℕ) : ℕ :=
  inputHeadBound + 2 + 1 +
    rewindBlankWorkPrefixManyTime headBound limit
      (outputProbeCleanupTargets n)

/-- All-prefix cleanup space envelope. -/
def outputProbeCleanupSpace (n initialSpace limit : ℕ)
    (headBound : Fin (n + 4) → ℕ) : ℕ :=
  max initialSpace
    (rewindBlankWorkPrefixManySpace initialSpace headBound limit
      (outputProbeCleanupTargets n))

end TM

end Complexity
