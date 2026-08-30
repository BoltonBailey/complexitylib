/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AndOrNot
public import Complexitylib.Circuits.BitString
public import Complexitylib.Encoding.BinaryNat
public import Complexitylib.Encoding.Pairing

/-!
# Succinct MCSP -- definitions

`SuccinctMCSP` replaces a complete truth table by a finite list of sampled
input/output constraints. The list may repeat an input, so contradictory
constraints are represented rather than ruled out by syntax. An instance is
accepted exactly when one circuit within its threshold matches every sample.

The codec is total and canonical. Each typed sample is framed separately,
the sample count is explicit, and decoding rejects wrong-width inputs,
non-singleton outputs, missing samples, trailing samples, noncanonical natural
fields, and malformed pairing.

Positive arities use `Basis.andOr2`. Since the circuit type has no zero-input
member, a zero-arity witness is an explicitly chosen constant bit of size zero.
Thus contradictory zero-arity samples are rejected while every consistent list
is accepted at every natural threshold.
-/


@[expose] public section

namespace Complexity

namespace SuccinctMCSP

/-- One typed input/output constraint for an `arity`-input Boolean function. -/
structure Sample (arity : ℕ) where
  /-- Input on which the candidate circuit is constrained. -/
  input : BitString arity
  /-- Required output on `input`. -/
  output : Bool

namespace Sample

/-- Package one evaluation of a Boolean function as a sample. -/
def ofFunction {arity : ℕ} (f : BitString arity → Bool)
    (input : BitString arity) : Sample arity where
  input := input
  output := f input

/-- A sample is satisfied when the function has its required output. -/
def MatchesFunction {arity : ℕ} (sample : Sample arity)
    (f : BitString arity → Bool) : Prop :=
  f sample.input = sample.output

/-- Canonically encode a sample as a framed input and singleton output. -/
def encode {arity : ℕ} (sample : Sample arity) : List Bool :=
  pair sample.input.toList [sample.output]

/-- Decode exactly one sample at the supplied arity. -/
def decode? (arity : ℕ) (bits : List Bool) : Option (Sample arity) := do
  let (inputBits, outputBits) ← unpair? bits
  if hinput : inputBits.length = arity then
    match outputBits with
    | [output] =>
        some
          { input := BitString.ofList inputBits hinput
            output }
    | _ => none
  else
    none

end Sample

/-- Canonically encode a list of samples as a right-nested sequence of pairs. -/
def encodeSamples {arity : ℕ} : List (Sample arity) → List Bool
  | [] => []
  | sample :: samples => pair sample.encode (encodeSamples samples)

/-- Decode exactly `count` right-nested samples and reject all trailing data. -/
def decodeSamples? (arity : ℕ) :
    (count : ℕ) → List Bool → Option (List (Sample arity))
  | 0, [] => some []
  | 0, _ :: _ => none
  | count + 1, bits => do
      let (sampleBits, rest) ← unpair? bits
      let sample ← Sample.decode? arity sampleBits
      let samples ← decodeSamples? arity count rest
      some (sample :: samples)

/-- A sampled circuit-minimization instance. Repeated inputs are permitted. -/
structure Instance where
  /-- Number of input bits in every sample. -/
  arity : ℕ
  /-- Finite list of constraints; repetitions and contradictions are retained. -/
  samples : List (Sample arity)
  /-- Maximum allowed circuit size. -/
  threshold : ℕ

namespace Instance

/-- Build the sampled constraints induced by a function on a chosen input list. -/
def ofInputs {arity : ℕ} (threshold : ℕ)
    (f : BitString arity → Bool) (inputs : List (BitString arity)) : Instance where
  arity := arity
  samples := inputs.map (Sample.ofFunction f)
  threshold := threshold

/-- Every sample in the instance is satisfied by the supplied function. -/
def SamplesFunction (inst : Instance)
    (f : BitString inst.arity → Bool) : Prop :=
  ∀ sample ∈ inst.samples, sample.MatchesFunction f

/-- Canonically encode arity, threshold, count, and the framed sample payload. -/
def encode (inst : Instance) : List Bool :=
  pair (BinaryNatCode.encode inst.arity)
    (pair (BinaryNatCode.encode inst.threshold)
      (pair (BinaryNatCode.encode inst.samples.length)
        (encodeSamples inst.samples)))

/-- Decode exactly one canonical sampled instance. -/
def decode? (bits : List Bool) : Option Instance := do
  let (arityBits, rest) ← unpair? bits
  let (thresholdBits, rest) ← unpair? rest
  let (countBits, sampleBits) ← unpair? rest
  let arity ← BinaryNatCode.decode? arityBits
  let threshold ← BinaryNatCode.decode? thresholdBits
  let count ← BinaryNatCode.decode? countBits
  let samples ← decodeSamples? arity count sampleBits
  some
    { arity
      samples
      threshold }

/-- A direct typed witness formulation of sampled circuit minimization.

At positive arity the witness is a fan-in-two circuit matching every listed
constraint. At arity zero the witness is an explicit constant output bit of
size zero. -/
def HasCircuitAtMost (inst : Instance) : Prop :=
  if harity : inst.arity = 0 then
    ∃ output : Bool, inst.SamplesFunction (fun _ => output)
  else
    letI : NeZero inst.arity := ⟨harity⟩
    ∃ (internalGates : ℕ)
        (circuit : Circuit Basis.andOr2 inst.arity 1 internalGates),
      circuit.size ≤ inst.threshold ∧
        inst.SamplesFunction (fun input => circuit.eval input 0)

end Instance

end SuccinctMCSP

/-- Total succinct MCSP over canonical sampled-instance codes.

Malformed strings are no-instances. -/
def SuccinctMCSP : Set (List Bool) :=
  {bits | match SuccinctMCSP.Instance.decode? bits with
    | some inst => inst.HasCircuitAtMost
    | none => False}

end Complexity
