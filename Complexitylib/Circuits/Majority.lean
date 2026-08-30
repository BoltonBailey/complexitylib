/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.ToCircuit
public import Complexitylib.Circuits.Majority.Defs
public import Complexitylib.Circuits.Majority.Internal

/-!
# Strict-majority circuits

This module packages the unary threshold fragment as a typed fan-in-two
AND/OR circuit. On `n` inputs it uses exactly
`3 + 2 * n * (n / 2 + 1)` gates and returns true exactly when strictly more
than half of its inputs are true.
-/


public section

namespace Complexity

namespace CircuitCode

/-- A strict-majority threshold never exceeds a positive input count. -/
theorem strictMajorityThreshold_le (inputCount : ℕ) [NeZero inputCount] :
    strictMajorityThreshold inputCount ≤ inputCount :=
  strictMajorityThreshold_le_internal inputCount

/-- Exact raw gate count for the strict-majority construction. -/
@[simp] theorem length_strictMajorityRawCircuit (inputCount : ℕ) :
    (strictMajorityRawCircuit inputCount).length =
      3 + 2 * inputCount * strictMajorityThreshold inputCount :=
  length_strictMajorityRawCircuit_internal inputCount

/-- The raw strict-majority construction is a valid single-output circuit at
every positive input arity. -/
theorem strictMajorityRawCircuit_wellFormed (inputCount : ℕ)
    [NeZero inputCount] :
    (strictMajorityRawCircuit inputCount).WellFormed inputCount :=
  strictMajorityRawCircuit_wellFormed_internal inputCount

end CircuitCode

namespace Circuit

/-- Typed fan-in-two strict-majority circuit reconstructed from the verified
raw threshold fragment. -/
noncomputable def strictMajority (inputCount : ℕ) [NeZero inputCount] :
    Circuit Basis.andOr2 inputCount 1
      ((CircuitCode.strictMajorityRawCircuit inputCount).length - 1) :=
  (CircuitCode.strictMajorityRawCircuit inputCount).toCircuit inputCount
    (CircuitCode.strictMajorityRawCircuit_wellFormed_internal inputCount)

/-- Exact size of the typed strict-majority circuit. -/
@[simp] theorem size_strictMajority (inputCount : ℕ) [NeZero inputCount] :
    (strictMajority inputCount).size =
      3 + 2 * inputCount * CircuitCode.strictMajorityThreshold inputCount := by
  rw [strictMajority, CircuitCode.RawCircuit.size_toCircuit,
    CircuitCode.length_strictMajorityRawCircuit_internal]

/-- The typed circuit returns the unary-count strict-majority predicate. -/
theorem eval_strictMajority (inputCount : ℕ) [NeZero inputCount]
    (input : BitString inputCount) :
    ((strictMajority inputCount).eval input) 0 =
      decide (CircuitCode.strictMajorityThreshold inputCount ≤
        Fin.countP input) := by
  have hbridge := CircuitCode.RawCircuit.eval?_toCircuit inputCount
    (CircuitCode.strictMajorityRawCircuit inputCount)
    (CircuitCode.strictMajorityRawCircuit_wellFormed_internal inputCount)
    input
  rw [CircuitCode.eval?_strictMajorityRawCircuit_internal] at hbridge
  exact (Option.some.inj hbridge).symm

end Circuit

end Complexity
