/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.ApproximateCounting.Relative.Defs
public import Complexitylib.Classes.Randomized.CircuitHardwiring
public import Complexitylib.Circuits.BinaryComparison.Defs

/-!
# Circuit interface for relative approximate counting -- definitions

This module states the semantic boundary between the finite hashing estimator
and a randomized multi-output circuit. Random bits occupy the input prefix, as
required by the library's generic hardwiring theorem.
-/


@[expose] public section

namespace Complexity

namespace ApproximateCounting

namespace Relative

/-- A circuit output relatively approximates the cardinality selected by one
ordinary input. -/
def OutputIsAccurate {inputWidth outputWidth domainWidth : ℕ}
    (precision : ℕ)
    (setOfInput : BitString inputWidth → Finset (BitString domainWidth))
    (input : BitString inputWidth) (output : BitString outputWidth) : Prop :=
  IsRelativeApproximation precision (setOfInput input).card
    output.unsignedValue

instance {inputWidth outputWidth domainWidth : ℕ}
    (precision : ℕ)
    (setOfInput : BitString inputWidth → Finset (BitString domainWidth))
    (input : BitString inputWidth) (output : BitString outputWidth) :
    Decidable (OutputIsAccurate precision setOfInput input output) := by
  unfold OutputIsAccurate
  infer_instance

/-- Exact semantic implementation of the amplified hashing estimate by a
random-seed-prefix circuit. -/
def CircuitImplements {inputWidth outputWidth domainWidth internalGates : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (precision failureBits : ℕ)
    (setOfInput : BitString inputWidth → Finset (BitString domainWidth))
    (circuit : Circuit Basis.andOr2
      (seedWidth domainWidth precision failureBits + inputWidth)
      outputWidth internalGates) : Prop :=
  ∀ seed input,
    (circuit.eval (Fin.append seed input)).unsignedValue =
      hashingEstimate precision failureBits (setOfInput input) seed

end Relative

end ApproximateCounting

end Complexity
