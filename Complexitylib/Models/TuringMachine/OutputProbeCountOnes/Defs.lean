/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeScan.Defs
import Complexitylib.Models.TuringMachine.Registers.RegisterOps
import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc.Defs

/-!
# Counting one bits through dynamically indexed output probes -- definitions

The serializer's first pass scans an oracle-defined occupancy bit at every
fixed address and counts the true results. This module supplies the generic
machine layer: zero leaves a canonical binary count unchanged, while one
increments it before the enclosing probe scan advances its address.
-/

namespace Complexity

namespace TM

/-- Stable outer controller frame after processing one queried bit. -/
def outputProbeCountOnesOuterExtrasAfter (n : ℕ)
    {controllerTapes : ℕ} (countIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (count : ℕ) (bit : Bool) :
    Fin (0 + outputProbeControllerTapes n + controllerTapes) → Tape :=
  if bit then
    Function.update outerExtras
      (outputProbeIndexedControllerIdx n countIdx)
      (outputProbeCounterTape (count + 1))
  else
    outerExtras

/-- One occupancy-counting iteration before the enclosing loop increments its
address: query, reset the latch, and conditionally increment the count. -/
def outputProbeCountOnesBodyTM (tm : TM n) (controllerTapes : ℕ)
    (addressIdx scratchIdx countIdx : Fin controllerTapes) :
    TM (0 + outputProbeControllerTapes n + controllerTapes) :=
  outputProbeIndexedResetDispatchTM tm controllerTapes addressIdx scratchIdx
    skipTM (binarySuccTM (outputProbeIndexedControllerIdx n countIdx))

/-- Scan consecutive source-output bits and count the ones in a canonical
binary controller register. -/
def outputProbeCountOnesTM (tm : TM n) (controllerTapes : ℕ)
    (addressIdx scratchIdx limitIdx countIdx : Fin controllerTapes) :
    TM (0 + outputProbeControllerTapes n + controllerTapes) :=
  binaryForTM
    (outputProbeCountOnesBodyTM tm controllerTapes addressIdx scratchIdx
      countIdx)
    (outputProbeIndexedControllerIdx n addressIdx)
    (outputProbeIndexedControllerIdx n limitIdx)

end TM

end Complexity
