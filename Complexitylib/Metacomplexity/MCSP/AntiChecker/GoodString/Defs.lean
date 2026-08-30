/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.FiniteCounting
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Selection.Defs

/-!
# Good-string combinatorics -- definitions

The good-string argument studies tuples drawn from the circuit descriptions
surviving a sample prefix. An input catches a tuple when at least half of its
entries disagree with the target there.
-/


@[expose] public section

namespace Complexity

namespace AntiChecker

/-- Circuit codes surviving the canonical sample prefix, regarded as a finite
type. -/
abbrev SurvivorCode {arity : ℕ} (target : BitString arity → Bool)
    (threshold : ℕ) (inputs : List (BitString arity)) :=
  ↑(ConsistentCodes target inputs (candidateCodes arity threshold))

/-- The Boolean output of a surviving circuit code on one input. The default
branch is unreachable for survivor codes: candidate membership guarantees a
canonical well-formed circuit at the declared arity. -/
def survivorCodeOutput {arity : ℕ} (target : BitString arity → Bool)
    (threshold : ℕ) (inputs : List (BitString arity))
    (code : SurvivorCode target threshold inputs)
    (input : BitString arity) : Bool :=
  (CircuitCode.evalCode arity code.1 input.toList).getD false

/-- A survivor tuple computes the target by taking the strict majority of its
pointwise circuit outputs. -/
def SurvivorTupleMajorityComputes {arity : ℕ}
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity))
    (tuple : Fin arity → SurvivorCode target threshold inputs) : Prop :=
  ∀ input,
    majority
        (fun i => survivorCodeOutput target threshold inputs (tuple i) input) =
      target input

/-- Current survivors that disagree with the target at one possible next
input. -/
def disagreeingSurvivors {arity : ℕ}
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity)) (input : BitString arity) :
    Finset (SurvivorCode target threshold inputs) :=
  Finset.univ.filter
    (fun code => ¬ CodeAgreesAt target code.1 input)

/-- Number of positions in a survivor tuple whose circuits agree with the
target at one input. -/
def survivorTupleAgreementCount {arity : ℕ}
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity)) (input : BitString arity)
    (tuple : Fin arity → SurvivorCode target threshold inputs) : ℕ :=
  (Finset.univ.filter
    (fun i => CodeAgreesAt target (tuple i).1 input)).card

/-- An input catches a survivor tuple when at least the ceiling of half of its
entries disagree with the target. -/
def IsSurvivorTupleCaughtAt {arity : ℕ}
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity)) (input : BitString arity)
    (tuple : Fin arity → SurvivorCode target threshold inputs) : Prop :=
  tupleEventCount (disagreeingSurvivors target threshold inputs input) tuple ∈
    Finset.Icc (arity - arity / 2) arity

instance {arity : ℕ} (target : BitString arity → Bool)
    (threshold : ℕ) (inputs : List (BitString arity))
    (input : BitString arity)
    (tuple : Fin arity → SurvivorCode target threshold inputs) :
    Decidable
      (IsSurvivorTupleCaughtAt target threshold inputs input tuple) := by
  unfold IsSurvivorTupleCaughtAt
  infer_instance

/-- Survivor tuples caught by one possible next input. -/
def caughtSurvivorTuples {arity : ℕ}
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity)) (input : BitString arity) :
    Finset (Fin arity → SurvivorCode target threshold inputs) :=
  Finset.univ.filter
    (IsSurvivorTupleCaughtAt target threshold inputs input)

/-- Every survivor tuple is caught by some input. Circuit hardness will supply
this premise by ruling out a majority circuit for the tuple. -/
def EverySurvivorTupleCaught {arity : ℕ}
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity)) : Prop :=
  ∀ tuple : Fin arity → SurvivorCode target threshold inputs,
    ∃ input, IsSurvivorTupleCaughtAt target threshold inputs input tuple

end AntiChecker

end Complexity
