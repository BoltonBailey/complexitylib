/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Codec.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Relation.Defs

/-!
# Fixed-width anti-checker counter domains -- definitions

Affine hashing acts directly on the fixed-width binary descriptions of valid
bounded circuits. Each survivor has one canonical word, with no delimiter,
parser branch, or padding multiplicity.
-/


@[expose] public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- Fixed cube dimension for circuit descriptions at one arity and gate
threshold. -/
def candidateCodeWidth (arity threshold : ℕ) : ℕ :=
  CircuitCode.FixedWidth.codeWidth arity threshold

instance (arity threshold : ℕ) : NeZero (candidateCodeWidth arity threshold) :=
  inferInstanceAs
    (NeZero (CircuitCode.FixedWidth.codeWidth arity threshold))

/-- One fixed-width word decodes to a valid description matching every labeled
sample. Malformed count words and invalid descriptions are rejected. -/
def EncodedDescriptionMatchesLabeledSamples {count arity threshold : ℕ}
    (samples : Fin count → SuccinctMCSP.Sample arity)
    (encoded : BitString (candidateCodeWidth arity threshold)) : Prop :=
  match CircuitCode.FixedWidth.Description.decode? encoded with
  | none => False
  | some description =>
      description.WellFormed ∧
        ∀ sample,
          description.toRawCircuit.eval? (samples sample).input.toList =
            some (samples sample).output

instance {count arity threshold : ℕ}
    (samples : Fin count → SuccinctMCSP.Sample arity)
    (encoded : BitString (candidateCodeWidth arity threshold)) :
    Decidable (EncodedDescriptionMatchesLabeledSamples samples encoded) := by
  unfold EncodedDescriptionMatchesLabeledSamples
  cases CircuitCode.FixedWidth.Description.decode? encoded <;>
    infer_instance

/-- Canonical fixed-width words that decode to valid descriptions surviving a
labeled sample vector. -/
def encodedCandidateLabeledSurvivorCodes {count : ℕ}
    (arity threshold : ℕ)
    (samples : Fin count → SuccinctMCSP.Sample arity) :
    Finset (BitString (candidateCodeWidth arity threshold)) :=
  Finset.univ.filter (EncodedDescriptionMatchesLabeledSamples samples)

/-- The fixed-width survivor set associated with a packed labeled-sample
input. -/
def encodedSurvivorSet {count : ℕ} (arity threshold : ℕ)
    (input : BitString (count * (arity + 1))) :
    Finset (BitString (candidateCodeWidth arity threshold)) :=
  encodedCandidateLabeledSurvivorCodes arity threshold
    (unpackLabeledSamples input)

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
