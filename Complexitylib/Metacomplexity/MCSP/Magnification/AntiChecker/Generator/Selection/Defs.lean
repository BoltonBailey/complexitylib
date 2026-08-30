/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Composition.Defs
public import Complexitylib.Circuits.InputSources.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Circuit.Defs

/-!
# Circuit-level anti-checker selection rounds -- definitions

A selection round receives the target truth table followed by an already
selected prefix of labeled samples. For each fixed candidate input, a circuit
hardwires that input, reads its label from the truth table, evaluates the
appropriate approximate counter on the extended prefix, and carries the
labeled candidate beside the resulting counter key.
-/


@[expose] public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- Input width for one circuit-level selection round: the truth table followed
by a row-major packed prefix of labeled samples. -/
def selectionRoundInputWidth (arity prefixLength : ℕ) : ℕ :=
  2 ^ arity + prefixLength * (arity + 1)

instance (arity prefixLength : ℕ) :
    NeZero (selectionRoundInputWidth arity prefixLength) :=
  ⟨by simp only [selectionRoundInputWidth]; positivity⟩

/-- Canonical input to one circuit-level selection round. -/
def selectionRoundInput {arity prefixLength : ℕ}
    (table : BitString (2 ^ arity))
    (packedPrefix : BitString (prefixLength * (arity + 1))) :
    BitString (selectionRoundInputWidth arity prefixLength) :=
  Fin.append table packedPrefix

/-- The labeled sample represented by one fixed candidate and the candidate's
truth-table bit. -/
def candidateSample {arity : ℕ} (candidate : Fin (2 ^ arity))
    (table : BitString (2 ^ arity)) : SuccinctMCSP.Sample arity where
  input := MCSP.Instance.inputOfIndex candidate
  output := table candidate

/-- Counter input obtained by prepending one fixed candidate to the previously
selected labeled prefix. -/
def candidateLabeledSamples {arity prefixLength : ℕ}
    (candidate : Fin (2 ^ arity)) (table : BitString (2 ^ arity))
    (packedPrefix : BitString (prefixLength * (arity + 1))) :
    Fin (prefixLength + 1) → SuccinctMCSP.Sample arity :=
  Fin.cons (candidateSample candidate table)
    (unpackLabeledSamples packedPrefix)

/-- Fixed-width payload carrying a candidate input followed by its target
label. -/
def candidateSampleBits {arity : ℕ} (candidate : Fin (2 ^ arity))
    (table : BitString (2 ^ arity)) : BitString (arity + 1) :=
  Fin.lastCases (table candidate) (MCSP.Instance.inputOfIndex candidate)

/-- Mixed constants and live inputs supplying the counter for one fixed
candidate. -/
def candidateCounterSources (arity prefixLength : ℕ)
    (candidate : Fin (2 ^ arity)) :
    Fin ((prefixLength + 1) * (arity + 1)) →
      Circuit.InputSource (selectionRoundInputWidth arity prefixLength) :=
  fun coordinate =>
    let position := finProdFinEquiv.symm coordinate
    Fin.cases
      (Fin.lastCases
        (.input (Fin.castAdd (prefixLength * (arity + 1)) candidate))
        (fun inputCoordinate =>
          .constant (MCSP.Instance.inputOfIndex candidate inputCoordinate))
        position.2)
      (fun prefixRow =>
        .input (Fin.natAdd (2 ^ arity)
          (finProdFinEquiv (prefixRow, position.2))))
      position.1

/-- Mixed constants and one live truth-table bit carrying the labeled
candidate as a selector payload. -/
def candidateSampleSources (arity prefixLength : ℕ)
    (candidate : Fin (2 ^ arity)) :
    Fin (arity + 1) →
      Circuit.InputSource (selectionRoundInputWidth arity prefixLength) :=
  fun coordinate =>
    Fin.lastCases
      (.input (Fin.castAdd (prefixLength * (arity + 1)) candidate))
      (fun inputCoordinate =>
        .constant (MCSP.Instance.inputOfIndex candidate inputCoordinate))
      coordinate

/-- Materialize the labeled extended prefix expected by one counter circuit. -/
def candidateCounterInputCircuit (arity prefixLength : ℕ)
    (candidate : Fin (2 ^ arity)) :
    Circuit Basis.andOr2 (selectionRoundInputWidth arity prefixLength)
      ((prefixLength + 1) * (arity + 1)) 0 :=
  Circuit.inputSources (candidateCounterSources arity prefixLength candidate)

/-- Materialize the labeled candidate payload. -/
def candidateSampleCircuit (arity prefixLength : ℕ)
    (candidate : Fin (2 ^ arity)) :
    Circuit Basis.andOr2 (selectionRoundInputWidth arity prefixLength)
      (arity + 1) 0 :=
  Circuit.inputSources (candidateSampleSources arity prefixLength candidate)

/-- Evaluate one approximate counter on a fixed candidate and carry the
candidate's labeled sample beside the counter output. -/
def candidateCounterRecordCircuit
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength)
    (candidate : Fin (2 ^ arity)) :
    Σ internalGates,
      Circuit Basis.andOr2 (selectionRoundInputWidth arity prefixLength)
        (counterOutputWidth beta arity + (arity + 1)) internalGates :=
  ⟨_,
    (counter.circuit.compose
      (candidateCounterInputCircuit arity prefixLength candidate)).parallel
      (candidateSampleCircuit arity prefixLength candidate)⟩

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
