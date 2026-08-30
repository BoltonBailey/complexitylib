/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Majority.Defs
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.GoodString.Defs

/-!
# Good-string circuit bridge -- definitions

This layer records the exact upper bound obtained by packing one small circuit
per tuple position and composing their outputs with the verified strict-majority
circuit.
-/


@[expose] public section

namespace Complexity

namespace AntiChecker

/-- Size bound for the strict-majority composition of `arity` single-output
circuits, each of size at most `threshold`. -/
def survivorTupleMajoritySizeBound (arity threshold : ℕ) : ℕ :=
  arity * threshold +
    (3 + 2 * arity * CircuitCode.strictMajorityThreshold arity)

end AntiChecker

end Complexity
