/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Extraction.Defs
public import Complexitylib.Metacomplexity.MCSP.Defs

/-!
# Finite circuit-code enumeration -- definitions

This layer gives the Anti-Checker Lemma's survivor count a canonical finite
domain. It enumerates every bit string up to the polynomial encoding bound,
then filters for canonical, well-formed circuit descriptions whose decoded
gate count is within the requested threshold.
-/


@[expose] public section

namespace Complexity

namespace AntiChecker

/-- Every Boolean string of exactly `length` bits. -/
def codesOfLength (length : ℕ) : Finset (List Bool) :=
  (Finset.univ : Finset (BitString length)).image BitString.toList

/-- Every Boolean string of length at most `bound`. -/
def codesUpTo (bound : ℕ) : Finset (List Bool) :=
  (Finset.range (bound + 1)).biUnion codesOfLength

/-- Uniform encoding-length bound for circuits at one input arity and size
threshold. -/
def codeLengthBound (arity threshold : ℕ) : ℕ :=
  1 + threshold * (2 * (arity + threshold) + 6)

/-- A canonical code for a well-formed circuit at the supplied arity whose
decoded gate count is within the threshold. -/
def IsSmallCircuitCode (arity threshold : ℕ) (code : List Bool) : Prop :=
  match CircuitCode.RawCircuit.decode? code with
  | none => False
  | some circuit =>
      circuit.WellFormed arity ∧ circuit.length ≤ threshold

instance (arity threshold : ℕ) (code : List Bool) :
    Decidable (IsSmallCircuitCode arity threshold code) := by
  unfold IsSmallCircuitCode
  cases CircuitCode.RawCircuit.decode? code <;> infer_instance

/-- All canonical small-circuit codes inside the uniform encoding-length
bound. -/
def candidateCodes (arity threshold : ℕ) : Finset (List Bool) :=
  (codesUpTo (codeLengthBound arity threshold)).filter
    (IsSmallCircuitCode arity threshold)

end AntiChecker

end Complexity
