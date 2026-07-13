/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.Unrolling.Amplification
import Complexitylib.Models.TuringMachine.Repetition.Defs

/-!
# Probabilistic semantics of circuit amplification

This module is the dependency boundary between circuit unrolling and finite
probability. The circuit layer counts true verdict wires with `Fin.countP`;
the randomized-complexity layer interprets the same vector as independent
choice blocks and hence as `blockEventCount` and `blockMajority`.
-/

namespace Complexity

namespace CircuitUnrolling

/-- Counting canonical circuit verdicts is exactly counting accepting blocks
in the compact repetition seed. -/
theorem finCountP_canonicalAcceptanceBits_eq_blockEventCount
    (tm : NTM k) (runs T : ℕ) (x : BitString n)
    (seed : BitString (runs * T)) :
    Fin.countP (canonicalAcceptanceBits tm runs T x seed) =
      blockEventCount (NTM.repeatAcceptEvent tm x.toList T) seed := by
  rw [finCountP_eq_popCount]
  unfold popCount blockEventCount
  congr 1
  ext j
  simp [canonicalAcceptanceBits, parallelAcceptanceBits, boundedAcceptanceBit,
    NTM.repeatAcceptEvent]
  have hchoices : parallelChoiceBlocks runs T seed j =
      blocksEquiv runs T seed j := by
    funext t
    simp
  rw [hchoices]

/-- The circuit encoder's at-least threshold is the randomized layer's strict
block-majority predicate. -/
theorem canonicalThresholdValue_eq_blockMajority
    (tm : NTM k) (runs T : ℕ) (x : BitString n)
    (seed : BitString (runs * T)) :
    decide (strictMajorityThreshold runs ≤
      Fin.countP (canonicalAcceptanceBits tm runs T x seed)) =
        blockMajority (NTM.repeatAcceptEvent tm x.toList T) seed := by
  rw [finCountP_canonicalAcceptanceBits_eq_blockEventCount]
  simp only [strictMajorityThreshold, blockMajority]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  omega

/-- The canonical typed amplification circuit computes exactly the compact
seed's block-majority acceptance predicate. -/
theorem canonicalAmplifiedAcceptanceCircuit_eval_eq_blockMajority
    (tm : NTM k) (runs T n : ℕ) [NeZero (runs * T + n)]
    (seed : BitString (runs * T)) (x : BitString n) :
    ((canonicalAmplifiedAcceptanceCircuit tm runs T n).eval
      (Fin.append seed x)) 0 =
        blockMajority (NTM.repeatAcceptEvent tm x.toList T) seed := by
  rw [canonicalAmplifiedAcceptanceCircuit_eval]
  exact canonicalThresholdValue_eq_blockMajority tm runs T x seed

end CircuitUnrolling

end Complexity
