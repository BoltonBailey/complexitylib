/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.ApproximateCounting.Relative.Circuit.Defs
import Complexitylib.Classes.Randomized.ApproximateCounting.Relative.Circuit.Internal

/-!
# Circuit interface for relative approximate counting

Any circuit computing the amplified hashing estimator inherits its exact
finite failure bound. This is the bridge used before nonuniform seed fixing.
-/


public section

namespace Complexity

namespace ApproximateCounting

namespace Relative

/-- Circuit failure seeds coincide exactly with the estimator's semantic
failure event. -/
theorem badSeedEvent_eq_failureEvent
    {inputWidth outputWidth domainWidth internalGates precision failureBits : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    {setOfInput : BitString inputWidth → Finset (BitString domainWidth)}
    {circuit : Circuit Basis.andOr2
      (seedWidth domainWidth precision failureBits + inputWidth)
      outputWidth internalGates}
    (himplements : CircuitImplements precision failureBits setOfInput circuit)
    (input : BitString inputWidth) :
    Circuit.badSeedEvent circuit (OutputIsAccurate precision setOfInput) input =
      failureEvent precision failureBits (setOfInput input) :=
  badSeedEvent_eq_failureEvent_internal himplements input

/-- Every fixed ordinary input inherits failure probability at most
`2^-failureBits` from the semantic hashing estimator. -/
theorem eventProb_badSeedEvent_le_two_pow
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
      1 / (2 : ℚ) ^ failureBits :=
  eventProb_badSeedEvent_le_two_pow_internal
    hprecision himplements input

/-- Choosing failure exponent `inputWidth + 1` leaves one seed that is
accurate for every ordinary input; hardwiring it preserves exact circuit
size. -/
theorem exists_hardwired_accurate_circuit
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
        fixed.size = circuit.size :=
  exists_hardwired_accurate_circuit_internal hprecision himplements

end Relative

end ApproximateCounting

end Complexity
