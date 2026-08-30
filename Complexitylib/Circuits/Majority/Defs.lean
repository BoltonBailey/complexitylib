/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Threshold.Defs

/-!
# Strict-majority circuits -- definitions

The raw construction specializes the unary threshold compiler to the smallest
integer strictly larger than half the input count. Primary input `i` is used
directly as referenced wire `i`.
-/


@[expose] public section

namespace Complexity

namespace CircuitCode

/-- Smallest integer count constituting a strict majority. -/
def strictMajorityThreshold (inputCount : ℕ) : ℕ :=
  inputCount / 2 + 1

/-- Raw fan-in-two circuit testing whether its primary inputs contain a strict
majority of true bits. -/
def strictMajorityRawCircuit (inputCount : ℕ) : RawCircuit :=
  Threshold.compileRaw inputCount (strictMajorityThreshold inputCount)
    (fun i : Fin inputCount => i.val)

end CircuitCode

end Complexity
