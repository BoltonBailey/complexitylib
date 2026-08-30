/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Gap.Slice.Defs
public import Mathlib.Data.Nat.Log

/-!
# Raw truth-table MCSP -- definitions

Hardness-magnification papers conventionally give MCSP only the `N = 2^n`
truth-table bits and fix the circuit-size threshold externally. The canonical
`MCSP.Instance` codec instead stores arity and threshold metadata. This module
defines the raw convention and total maps between the two representations.

A raw string is well formed exactly when its length is a power of two. Its
arity is recovered by base-two logarithm. Malformed lengths are outside both
sides of every raw gap problem; no arbitrary threshold or arity is assigned to
them.
-/


@[expose] public section

namespace Complexity

namespace MCSP

/-- A list is a raw truth table when its length is exactly `2^arity` for some
arity. In particular, the empty list is not a raw truth table. -/
def IsRawTruthTable (bits : List Bool) : Prop :=
  ∃ arity, bits.length = 2 ^ arity

/-- Recover the arity of a prospective raw truth table from its length. -/
def rawArity (bits : List Bool) : ℕ :=
  Nat.log 2 bits.length

/-- Decode a raw truth table at an externally supplied arity-indexed threshold.

The decoder succeeds only at exact power-of-two lengths. -/
def rawDecode? (threshold : ℕ → ℕ) (bits : List Bool) : Option Instance :=
  let arity := rawArity bits
  if htable : bits.length = 2 ^ arity then
    some
      { arity
        table := BitString.ofList bits htable
        threshold := threshold arity }
  else
    none

/-- Raw `MCSP[threshold]`: the input contains only its truth-table bits. -/
def rawAtThreshold (threshold : ℕ → ℕ) : Language :=
  {bits | match rawDecode? threshold bits with
    | some inst => inst.HasCircuitAtMost
    | none => False}

/-- Add canonical arity and threshold metadata to a raw truth table. Malformed
raw strings are sent to the empty, noncanonical code. -/
def rawToCanonical (threshold : ℕ → ℕ) (bits : List Bool) : List Bool :=
  match rawDecode? threshold bits with
  | some inst => inst.encode
  | none => []

/-- Erase arity and threshold metadata from a canonical MCSP code. Malformed
canonical strings are sent to the empty, malformed raw string. -/
def canonicalToRaw (bits : List Bool) : List Bool :=
  match Instance.decode? bits with
  | some inst => inst.tableBits
  | none => []

end MCSP

namespace GapMCSP

/-- Yes side of raw `GapMCSP[s_yes,s_no]`. -/
def rawSliceYesLanguage (parameters : SliceParameters) : Language :=
  MCSP.rawAtThreshold parameters.yesThreshold

/-- No side of raw `GapMCSP[s_yes,s_no]`. The input has no encoded threshold;
the no cutoff is supplied entirely by the problem parameters. -/
def rawSliceNoLanguage (parameters : SliceParameters) : Language :=
  {bits | match MCSP.rawDecode? parameters.yesThreshold bits with
    | some inst => parameters.noThreshold inst.arity < inst.minimumSize
    | none => False}

end GapMCSP

end Complexity
