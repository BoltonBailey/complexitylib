/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.ApproximateCounting.Relative.Circuit.Defs
public import Complexitylib.Circuits.OracleInlining.Adaptive.Defs

/-!
# Oracle programs for relative approximate counting -- definitions

This layer states when a fixed-round Boolean-oracle circuit program computes
the amplified hashing estimator. The oracle language and the construction of
the program remain parameters at this semantic boundary.
-/


@[expose] public section

namespace Complexity

private instance neZero_seed_add_input (seedWidth inputWidth : ℕ)
    [NeZero inputWidth] : NeZero (seedWidth + inputWidth) :=
  ⟨by have := NeZero.ne inputWidth; omega⟩

namespace ApproximateCounting

namespace Relative

/-- Exact semantic implementation of the amplified hashing estimator by a
fixed-round oracle circuit program. -/
def OracleProgramImplements
    {inputWidth outputWidth domainWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (precision failureBits : ℕ)
    (setOfInput : BitString inputWidth → Finset (BitString domainWidth))
    (program : AdaptiveOracleProgram
      (seedWidth domainWidth precision failureBits + inputWidth)
      outputWidth rounds)
    (oracle : BooleanOracle) : Prop :=
  ∀ seed input,
    (program.eval oracle (Fin.append seed input)).unsignedValue =
      hashingEstimate precision failureBits (setOfInput input) seed

end Relative

end ApproximateCounting

end Complexity
