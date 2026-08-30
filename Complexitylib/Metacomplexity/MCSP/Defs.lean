/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AndOrNot
public import Complexitylib.Circuits.BitString
public import Complexitylib.Circuits.Family.Defs
public import Complexitylib.Encoding.BinaryNat
public import Complexitylib.Encoding.Pairing

/-!
# Minimum Circuit Size Problem -- definitions

This definitions layer gives MCSP a total, canonical input format and pins its
semantics to Complexitylib's exact fan-in-two circuit convention. An instance
stores an arity `n`, a typed `2^n`-entry truth table, and a size threshold.
Truth-table position `k` denotes the input whose variable `j` is bit `j` of
`k`, so variables are enumerated in little-endian order.

Positive arities use `Basis.andOr2`: primary inputs and negation flags are
free, while every internal and output gate is counted. The circuit type
intentionally has no zero-input member. Following `CircuitFamily.size`, the
unique zero-input answer is therefore stored directly and assigned size zero.

The codec is total. It rejects malformed pairing, noncanonical binary natural
fields, a truth table of the wrong length, and trailing data. Malformed strings
are outside `MCSP`.
-/


@[expose] public section

namespace Complexity

namespace MCSP

/-- A well-formed MCSP instance with a structurally exact truth-table length. -/
structure Instance where
  /-- Number of inputs of the represented Boolean function. -/
  arity : ℕ
  /-- Function values in increasing little-endian input-index order. -/
  table : BitString (2 ^ arity)
  /-- Maximum allowed circuit size. -/
  threshold : ℕ

namespace Instance

/-- Truth-table bits as their canonical variable-length machine payload. -/
def tableBits (inst : Instance) : List Bool :=
  inst.table.toList

/-- Interpret an input as its little-endian truth-table index. -/
def inputIndex {arity : ℕ} (input : BitString arity) : Fin (2 ^ arity) :=
  ⟨Nat.fromBitsLE input.toList, by
    simpa using Nat.fromBitsLE_lt_pow_length input.toList⟩

/-- Decode a truth-table index as its fixed-width little-endian input. -/
def inputOfIndex {arity : ℕ} (index : Fin (2 ^ arity)) : BitString arity :=
  BitString.ofList (Nat.toBitsLE arity index.val) (Nat.length_toBitsLE arity index.val)

/-- The Boolean function denoted by an instance's truth table. -/
def function (inst : Instance) : BitString inst.arity → Bool :=
  fun input => inst.table (inputIndex input)

/-- Package a Boolean function as its exact canonical truth table at a chosen
MCSP threshold. -/
def ofFunction (arity threshold : ℕ) (f : BitString arity → Bool) :
    Instance where
  arity := arity
  table := fun index => f (inputOfIndex index)
  threshold := threshold

/-- Replace only the size threshold of an instance. -/
def withThreshold (inst : Instance) (threshold : ℕ) : Instance :=
  { inst with threshold }

/-- Canonically encode arity, threshold, and the exact truth-table payload.

The natural fields use minimal little-endian binary and the two nested pairs
make both field boundaries self-delimiting. -/
def encode (inst : Instance) : List Bool :=
  pair (BinaryNatCode.encode inst.arity)
    (pair (BinaryNatCode.encode inst.threshold) inst.tableBits)

/-- Decode exactly one canonical MCSP instance.

Every failure mode returns `none`, including a truth-table payload whose
length differs from `2^arity`. -/
def decode? (bits : List Bool) : Option Instance := do
  let (arityBits, rest) ← unpair? bits
  let (thresholdBits, tableBits) ← unpair? rest
  let arity ← BinaryNatCode.decode? arityBits
  let threshold ← BinaryNatCode.decode? thresholdBits
  if htable : tableBits.length = 2 ^ arity then
    some
      { arity
        table := BitString.ofList tableBits htable
        threshold }
  else
    none

/-- Minimum circuit size under the library's total MCSP convention.

At positive arity this is exactly `Circuit.sizeComplexity Basis.andOr2`. At
arity zero it is zero, matching the explicit-bit convention used by
`CircuitFamily`. -/
noncomputable def minimumSize (inst : Instance) : ℕ :=
  if harity : inst.arity = 0 then
    0
  else
    letI : NeZero inst.arity := ⟨harity⟩
    Circuit.sizeComplexity Basis.andOr2 inst.function

/-- A direct circuit-witness formulation of an MCSP yes-instance.

For positive arity this asks for a typed circuit no larger than the threshold.
At arity zero the separately stored answer has size zero, so every natural
threshold accepts it. -/
def HasCircuitAtMost (inst : Instance) : Prop :=
  if harity : inst.arity = 0 then
    True
  else
    letI : NeZero inst.arity := ⟨harity⟩
    ∃ (internalGates : ℕ)
        (circuit : Circuit Basis.andOr2 inst.arity 1 internalGates),
      circuit.size ≤ inst.threshold ∧ circuit.Computes inst.function

end Instance

end MCSP

/-- The total Minimum Circuit Size Problem over canonical encoded instances.

Malformed strings are no-instances. Positive-arity size uses
`Basis.andOr2`; zero arity uses the explicit size-zero convention documented
on `MCSP.Instance.minimumSize`. -/
def MCSP : Set (List Bool) :=
  {bits | match MCSP.Instance.decode? bits with
    | some inst => inst.HasCircuitAtMost
    | none => False}

end Complexity
