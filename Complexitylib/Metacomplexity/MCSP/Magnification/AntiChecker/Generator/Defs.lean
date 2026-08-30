/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Parameters.Defs

/-!
# Typed Anti-Checker Lemma generators -- definitions

An Anti-Checker Lemma generator is a multi-output circuit whose input is an
`n`-variable truth table and whose packed output contains exactly the selected
number of `n`-bit sample points. Its semantic contract is universal in the
input truth table: whenever the represented function is hard at the large
threshold, the printed points anti-check it at the smaller threshold.
-/


@[expose] public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- Read one fixed-width sample from a row-major packed bit string. -/
def unpackSample {count arity : ℕ} (output : BitString (count * arity))
    (sample : Fin count) : BitString arity :=
  fun coordinate => output (finProdFinEquiv (sample, coordinate))

/-- Split a packed output into its ordered list of fixed-width samples. -/
def unpackSamples {count arity : ℕ}
    (output : BitString (count * arity)) : List (BitString arity) :=
  List.ofFn (unpackSample output)

/-- Canonical little-endian truth-table input expected by the generator. -/
def truthTable {arity : ℕ} (target : BitString arity → Bool) :
    BitString (2 ^ arity) :=
  (MCSP.Instance.ofFunction arity 0 target).table

/-- The target has no circuit at the large threshold. -/
def IsHardAt {arity : ℕ} (beta : PositiveRationalScale)
    (target : BitString arity → Bool) : Prop :=
  ¬ MCSP.Instance.HasCircuitAtMost
    (MCSP.Instance.ofFunction arity (hardThreshold beta arity) target)

/-- A typed multi-output circuit with the exact input width, output width, and
rounded size bound from the Anti-Checker Lemma. -/
structure Generator (overhead : ℕ) (beta : PositiveRationalScale)
    (arity : ℕ) [NeZero arity] where
  /-- Number of internal gates in the generator circuit. -/
  internalGates : ℕ
  /-- Circuit mapping a truth table to the packed sample inputs. -/
  circuit : Circuit Basis.andOr2 (2 ^ arity)
    (outputBitCount beta arity) internalGates
  /-- Published ceiling-rounded size bound. -/
  size_le : circuit.size ≤ generatorSizeBound overhead beta arity

namespace Generator

/-- Run the generator on a packed truth table and unpack its sample inputs. -/
def inputs {overhead arity : ℕ} {beta : PositiveRationalScale}
    [NeZero arity] (generator : Generator overhead beta arity)
    (table : BitString (2 ^ arity)) : List (BitString arity) :=
  unpackSamples (generator.circuit.eval table)

/-- Run the generator on the canonical truth table of a target function. -/
def inputsFor {overhead arity : ℕ} {beta : PositiveRationalScale}
    [NeZero arity] (generator : Generator overhead beta arity)
    (target : BitString arity → Bool) : List (BitString arity) :=
  generator.inputs (truthTable target)

/-- The generator prints an anti-checker for every target hard at the large
threshold. -/
def IsCorrect {overhead arity : ℕ} {beta : PositiveRationalScale}
    [NeZero arity] (generator : Generator overhead beta arity) : Prop :=
  ∀ target, IsHardAt beta target →
    Complexity.AntiChecker.IsFor target (smallThreshold beta arity)
      (generator.inputsFor target)

end Generator

/-- A total arity-indexed assertion that handles the circuit model's positive
input and output arity requirements explicitly. -/
def ExistsCorrectGeneratorAt (overhead : ℕ)
    (beta : PositiveRationalScale) (arity : ℕ) : Prop :=
  if harity : arity = 0 then
    False
  else
    letI : NeZero arity := ⟨harity⟩
    ∃ generator : Generator overhead beta arity, generator.IsCorrect

/-- Quantifier structure of the Anti-Checker Lemma's conclusion: one natural
overhead constant works for every sufficiently small positive `beta` and all
sufficiently large truth-table arities. -/
def HasGenerators : Prop :=
  ∃ overhead : ℕ,
    ∀ᶠ beta in PositiveRationalScale.atZeroFromPositive,
      ∀ᶠ arity in Filter.atTop,
        ExistsCorrectGeneratorAt overhead beta arity

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
