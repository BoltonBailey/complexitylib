/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.BinaryComparison
public import Complexitylib.Circuits.Composition.Defs
public import Complexitylib.Circuits.InputProjection.Defs
public import Complexitylib.Circuits.InputReindexing.Defs
public import Complexitylib.Circuits.Multiplexer.Defs

/-!
# Keyed unsigned minimum -- definitions

A keyed selector compares two little-endian keys and returns the winning key
together with its payload. Inputs are packed record-first: left key, left
payload, right key, then right payload.
-/


@[expose] public section

namespace Complexity

namespace BitString

/-- Canonical record-first input order for keyed minimum selection. -/
def keyedMinimumInput {keyWidth payloadWidth : ℕ}
    (leftKey : BitString keyWidth) (leftPayload : BitString payloadWidth)
    (rightKey : BitString keyWidth) (rightPayload : BitString payloadWidth) :
    BitString ((keyWidth + payloadWidth) + (keyWidth + payloadWidth)) :=
  Fin.append (Fin.append leftKey leftPayload)
    (Fin.append rightKey rightPayload)

/-- Select the record with smaller unsigned key, choosing the left record on ties. -/
def unsignedKeyedMin {keyWidth payloadWidth : ℕ}
    (leftKey : BitString keyWidth) (leftPayload : BitString payloadWidth)
    (rightKey : BitString keyWidth) (rightPayload : BitString payloadWidth) :
    BitString (keyWidth + payloadWidth) :=
  if leftKey.unsignedValue ≤ rightKey.unsignedValue then
    Fin.append leftKey leftPayload
  else
    Fin.append rightKey rightPayload

end BitString

namespace Circuit

/-- Embed the two key blocks from record-first input into comparator order. -/
def keyedMinimumComparisonInput (keyWidth payloadWidth : ℕ) :
    Fin (keyWidth + keyWidth) →
      Fin ((keyWidth + payloadWidth) + (keyWidth + payloadWidth)) :=
  Fin.addCases
    (fun key =>
      Fin.castAdd (keyWidth + payloadWidth) (Fin.castAdd payloadWidth key))
    (fun key =>
      Fin.natAdd (keyWidth + payloadWidth) (Fin.castAdd payloadWidth key))

/-- Key comparison followed by an unchanged copy of both complete records. -/
noncomputable def unsignedLEWithKeyedPayload
    (keyWidth payloadWidth : ℕ) [NeZero keyWidth] :
    Circuit Basis.andOr2
      ((keyWidth + payloadWidth) + (keyWidth + payloadWidth))
      (1 + ((keyWidth + payloadWidth) + (keyWidth + payloadWidth)))
      ((CircuitCode.unsignedLERawCircuit keyWidth).length - 1) :=
  ((unsignedLE keyWidth).reindexInputs
      (keyedMinimumComparisonInput keyWidth payloadWidth)).parallel
    (projectInputs (fun input => input))

/-- Fan-in-two circuit selecting the record with minimum unsigned key. -/
noncomputable def unsignedKeyedMin
    (keyWidth payloadWidth : ℕ) [NeZero keyWidth] :
    Circuit Basis.andOr2
      ((keyWidth + payloadWidth) + (keyWidth + payloadWidth))
      (keyWidth + payloadWidth)
      (((CircuitCode.unsignedLERawCircuit keyWidth).length - 1) +
        (1 + ((keyWidth + payloadWidth) + (keyWidth + payloadWidth))) +
        ((keyWidth + payloadWidth) + (keyWidth + payloadWidth))) :=
  (multiplexer (keyWidth + payloadWidth)).compose
    (unsignedLEWithKeyedPayload keyWidth payloadWidth)

end Circuit

end Complexity
