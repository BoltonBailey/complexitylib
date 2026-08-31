/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Enumeration.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Relation.Defs

/-!
# Fixed-width anti-checker counter domains -- definitions

Affine hashing acts on a Boolean cube of fixed dimension, while canonical
circuit codes have every length up to `AntiChecker.codeLengthBound`. We embed
each bounded code into a fixed-width string consisting of a one-hot length
block followed by its contents padded with zeroes.
-/


@[expose] public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- Width of the fixed Boolean cube used to represent bounded circuit codes.
The first `bound + 1` bits identify the code length, and the last `bound` bits
hold its zero-padded contents. -/
def boundedCodeWidth (bound : ℕ) : ℕ :=
  (bound + 1) + bound

instance (bound : ℕ) : NeZero (boundedCodeWidth bound) :=
  ⟨by simp [boundedCodeWidth]⟩

/-- Encode a variable-length Boolean code by a one-hot length block followed
by a zero-padded content block. Codes longer than `bound` are truncated only
to make the function total; the counter domain uses it solely on bounded
canonical codes. -/
def encodeBoundedCode (bound : ℕ) (code : List Bool) :
    BitString (boundedCodeWidth bound) :=
  Fin.append
    (fun length : Fin (bound + 1) =>
      decide (length.val = min code.length bound))
    (fun index : Fin bound => (code[index.val]?).getD false)

/-- Fixed cube dimension for canonical circuit codes at one arity and size
threshold. -/
def candidateCodeWidth (arity threshold : ℕ) : ℕ :=
  boundedCodeWidth (AntiChecker.codeLengthBound arity threshold)

instance (arity threshold : ℕ) : NeZero (candidateCodeWidth arity threshold) :=
  inferInstanceAs (NeZero (boundedCodeWidth
    (AntiChecker.codeLengthBound arity threshold)))

/-- Fixed-width encodings of the canonical circuit codes surviving a labeled
sample vector. -/
def encodedCandidateLabeledSurvivorCodes {count : ℕ}
    (arity threshold : ℕ)
    (samples : Fin count → SuccinctMCSP.Sample arity) :
    Finset (BitString (candidateCodeWidth arity threshold)) :=
  (candidateLabeledSurvivorCodes arity threshold samples).image
    (encodeBoundedCode (AntiChecker.codeLengthBound arity threshold))

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
