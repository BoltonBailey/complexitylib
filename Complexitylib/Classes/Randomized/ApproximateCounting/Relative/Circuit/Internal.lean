/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.ApproximateCounting.Relative.Circuit.Defs
import Complexitylib.Classes.Randomized.ApproximateCounting.Relative

/-!
# Circuit interface for relative approximate counting -- proof internals
-/


public section

namespace Complexity

namespace ApproximateCounting

namespace Relative

theorem badSeedEvent_eq_failureEvent_internal
    {inputWidth outputWidth domainWidth internalGates precision failureBits : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    {setOfInput : BitString inputWidth → Finset (BitString domainWidth)}
    {circuit : Circuit Basis.andOr2
      (seedWidth domainWidth precision failureBits + inputWidth)
      outputWidth internalGates}
    (himplements : CircuitImplements precision failureBits setOfInput circuit)
    (input : BitString inputWidth) :
    Circuit.badSeedEvent circuit (OutputIsAccurate precision setOfInput) input =
      failureEvent precision failureBits (setOfInput input) := by
  ext seed
  rw [Circuit.mem_badSeedEvent_iff]
  simp [OutputIsAccurate, failureEvent, successEvent,
    himplements seed input]

theorem eventProb_badSeedEvent_le_two_pow_internal
    {inputWidth outputWidth domainWidth internalGates precision failureBits : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    {setOfInput : BitString inputWidth → Finset (BitString domainWidth)}
    {circuit : Circuit Basis.andOr2
      (seedWidth domainWidth precision failureBits + inputWidth)
      outputWidth internalGates}
    (hprecision : 0 < precision)
    (himplements : CircuitImplements precision failureBits setOfInput circuit)
    (input : BitString inputWidth) :
    eventProb
        (Circuit.badSeedEvent circuit
          (OutputIsAccurate precision setOfInput) input) ≤
      1 / (2 : ℚ) ^ failureBits := by
  rw [badSeedEvent_eq_failureEvent_internal himplements input]
  exact eventProb_failureEvent_le_two_pow (setOfInput input) hprecision

theorem exists_hardwired_accurate_circuit_internal
    {inputWidth outputWidth domainWidth internalGates precision : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    {setOfInput : BitString inputWidth → Finset (BitString domainWidth)}
    {circuit : Circuit Basis.andOr2
      (seedWidth domainWidth precision (inputWidth + 1) + inputWidth)
      outputWidth internalGates}
    (hprecision : 0 < precision)
    (himplements :
      CircuitImplements precision (inputWidth + 1) setOfInput circuit) :
    ∃ fixed : Circuit Basis.andOr2 inputWidth outputWidth internalGates,
      (∀ input, OutputIsAccurate precision setOfInput input
        (fixed.eval input)) ∧
        fixed.size = circuit.size := by
  apply Circuit.exists_hardwired_correct_circuit circuit
    (OutputIsAccurate precision setOfInput)
  intro input
  exact eventProb_badSeedEvent_le_two_pow_internal
    hprecision himplements input

end Relative

end ApproximateCounting

end Complexity
