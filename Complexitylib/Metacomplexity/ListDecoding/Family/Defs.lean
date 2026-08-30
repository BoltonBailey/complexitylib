/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Batteries.Data.BitVec.Lemmas
public import Complexitylib.Encoding.BinaryNat
public import Complexitylib.Encoding.Pairing
public import Complexitylib.Metacomplexity.ListDecoding.Defs
public import Complexitylib.Models.TuringMachine.OutputSemantics.Defs

/-!
# Uniform families of finite Boolean list codes -- definitions

Hirahara's reconstruction needs more than a single semantic code. The code is
indexed by message length and inverse accuracy, its truth-table length and
decoder list size obey polynomial bounds, and one uniform machine computes
each encoder or full decoder across every parameter choice.

This definitions layer keeps those three obligations separate so an explicit
algebraic construction can discharge them independently.
-/


@[expose] public section

namespace Complexity

/-- A family of Boolean list codes indexed by message length and inverse
accuracy. Codeword coordinates are Boolean strings of a family-specified
length. -/
structure BooleanListCodeFamily where
  /-- Number of input bits addressing one codeword coordinate. -/
  coordinateLength : ℕ → ℕ → ℕ
  /-- Number of indexed candidates returned by the decoder. -/
  listSize : ℕ → ℕ → ℕ
  /-- The semantic code at each message length and inverse accuracy. -/
  code : ∀ messageLength inverseAccuracy,
    BooleanListCode messageLength (listSize messageLength inverseAccuracy)
      (Fin (coordinateLength messageLength inverseAccuracy) → Bool)

namespace BooleanListCodeFamily

/-- Canonical little-endian truth-table order on a Boolean cube. -/
def truthTableBits {coordinateLength : ℕ}
    (word : (Fin coordinateLength → Bool) → Bool) : List Bool :=
  List.ofFn fun index : Fin (2 ^ coordinateLength) =>
    word (BitVec.ofFin index).getLsb

/-- Canonically framed input to a uniform encoder machine. -/
def encoderInput (messageLength inverseAccuracy : ℕ)
    (message : Fin messageLength → Bool) : List Bool :=
  pair (BinaryNatCode.encode messageLength) <|
    pair (BinaryNatCode.encode inverseAccuracy) (List.ofFn message)

/-- Canonical full truth table output of a family encoder. -/
def encoderOutput (family : BooleanListCodeFamily)
    (messageLength inverseAccuracy : ℕ)
    (message : Fin messageLength → Bool) : List Bool :=
  truthTableBits ((family.code messageLength inverseAccuracy).encode message)

/-- Canonically framed input to a uniform full-list decoder machine. -/
def decoderInput (family : BooleanListCodeFamily)
    (messageLength inverseAccuracy : ℕ)
    (received :
      (Fin (family.coordinateLength messageLength inverseAccuracy) → Bool) →
        Bool) : List Bool :=
  pair (BinaryNatCode.encode messageLength) <|
    pair (BinaryNatCode.encode inverseAccuracy) (truthTableBits received)

/-- Canonical concatenation of every indexed decoder output. -/
def decoderOutput (family : BooleanListCodeFamily)
    (messageLength inverseAccuracy : ℕ)
    (received :
      (Fin (family.coordinateLength messageLength inverseAccuracy) → Bool) →
        Bool) : List Bool :=
  (List.ofFn fun index : Fin (family.listSize messageLength inverseAccuracy) =>
    List.ofFn ((family.code messageLength inverseAccuracy).decode received index)).flatten

/-- Semantic list decoding at radius `1/2 - 1/q`, where `q` is the inverse
accuracy parameter. The lower bound `2 ≤ q` keeps the radius nonnegative. -/
def IsListDecodableAtInverseAccuracy (family : BooleanListCodeFamily) : Prop :=
  ∀ messageLength inverseAccuracy, 2 ≤ inverseAccuracy →
    (family.code messageLength inverseAccuracy).IsListDecodableAt
      (1 / 2 - 1 / (inverseAccuracy : ℚ))

/-- Concrete polynomial parameter bounds for a list-code family. Bounding
`2^coordinateLength` directly captures the content of
`coordinateLength = O(log(messageLength / epsilon))` without hiding a choice
of multivariate asymptotic convention. -/
structure PolynomialParameterBounds (family : BooleanListCodeFamily) where
  /-- Multiplicative constant for full codeword length. -/
  codewordConstant : ℕ
  /-- Polynomial degree for full codeword length. -/
  codewordDegree : ℕ
  /-- Multiplicative constant for decoder list size. -/
  listConstant : ℕ
  /-- Polynomial degree for decoder list size. -/
  listDegree : ℕ
  /-- The full truth table has polynomial length in message length and inverse
  accuracy. -/
  codewordLength_le : ∀ messageLength inverseAccuracy,
    2 ^ family.coordinateLength messageLength inverseAccuracy ≤
      codewordConstant *
        (messageLength + inverseAccuracy + 1) ^ codewordDegree
  /-- The decoder returns polynomially many candidates in inverse accuracy. -/
  listSize_le : ∀ messageLength inverseAccuracy,
    family.listSize messageLength inverseAccuracy ≤
      listConstant * (inverseAccuracy + 1) ^ listDegree

/-- Uniform machine realization of a list-code family. A single encoder and a
single full-list decoder handle every parameter choice; only their inputs vary.
The time bounds are polynomial in the numeric parameters, matching unary
parameterization even though the canonical framing stores the numbers in
binary. -/
structure UniformPolynomialTimeRealization (family : BooleanListCodeFamily) where
  /-- Work-tape count of the uniform encoder. -/
  encoderTapes : ℕ
  /-- Work-tape count of the uniform full-list decoder. -/
  decoderTapes : ℕ
  /-- One encoder machine for the entire family. -/
  encoderMachine : TM encoderTapes
  /-- One full-list decoder machine for the entire family. -/
  decoderMachine : TM decoderTapes
  /-- Pointwise encoder clock. -/
  encoderTime : ℕ → ℕ → ℕ
  /-- Pointwise decoder clock. -/
  decoderTime : ℕ → ℕ → ℕ
  /-- Uniform encoder correctness on every canonical family input. -/
  encoder_correct : ∀ messageLength inverseAccuracy message,
    encoderMachine.ProducesInTime
      (encoderInput messageLength inverseAccuracy message)
      (family.encoderOutput messageLength inverseAccuracy message)
      (encoderTime messageLength inverseAccuracy)
  /-- Uniform full-list decoder correctness on every received word. -/
  decoder_correct : ∀ messageLength inverseAccuracy received,
    decoderMachine.ProducesInTime
      (family.decoderInput messageLength inverseAccuracy received)
      (family.decoderOutput messageLength inverseAccuracy received)
      (decoderTime messageLength inverseAccuracy)
  /-- Shared polynomial-time multiplicative constant. -/
  timeConstant : ℕ
  /-- Shared polynomial-time degree. -/
  timeDegree : ℕ
  /-- Encoder time is polynomial in message length and inverse accuracy. -/
  encoderTime_le : ∀ messageLength inverseAccuracy,
    encoderTime messageLength inverseAccuracy ≤
      timeConstant * (messageLength + inverseAccuracy + 1) ^ timeDegree
  /-- Full-list decoder time is polynomial in the same parameters. -/
  decoderTime_le : ∀ messageLength inverseAccuracy,
    decoderTime messageLength inverseAccuracy ≤
      timeConstant * (messageLength + inverseAccuracy + 1) ^ timeDegree

end BooleanListCodeFamily

end Complexity
