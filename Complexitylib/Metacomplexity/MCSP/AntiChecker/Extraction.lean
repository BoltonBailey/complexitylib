/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Extraction.Defs
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Extraction.Internal

/-!
# Finite anti-checker extraction

This module exposes the finite survivor-set argument behind anti-checker
extraction. Starting from a finite set of circuit codes, one records the codes
consistent with all samples chosen so far. If every original code fails on
some input, at most one chosen failure input per code empties the survivor
set. If the original codes cover all circuits below a threshold, the resulting
input list is an anti-checker and its canonical SuccinctMCSP instance rejects.

The construction is intentionally conditional on a finite covering code set.
Building and bounding that set is a separate quantitative step.
-/


public section

namespace Complexity

namespace AntiChecker

/-- List consistency is pointwise agreement at every member. -/
theorem consistentCode_iff_forall_mem {arity : ℕ}
    (target : BitString arity → Bool) (inputs : List (BitString arity))
    (code : List Bool) :
    ConsistentCode target inputs code ↔
      ∀ input ∈ inputs, CodeAgreesAt target code input :=
  consistentCode_iff_forall_mem_internal target inputs code

/-- Membership in the survivor set splits into original membership and sample
consistency. -/
theorem mem_consistentCodes_iff {arity : ℕ}
    (target : BitString arity → Bool) (inputs : List (BitString arity))
    (codes : Finset (List Bool)) (code : List Bool) :
    code ∈ ConsistentCodes target inputs codes ↔
      code ∈ codes ∧ ConsistentCode target inputs code :=
  mem_consistentCodes_iff_internal target inputs codes code

/-- With no samples, every original candidate survives. -/
theorem consistentCodes_nil {arity : ℕ}
    (target : BitString arity → Bool) (codes : Finset (List Bool)) :
    ConsistentCodes target [] codes = codes :=
  consistentCodes_nil_internal target codes

/-- Adding one sample filters the previous survivor set by agreement there. -/
theorem consistentCodes_cons {arity : ℕ}
    (target : BitString arity → Bool) (input : BitString arity)
    (inputs : List (BitString arity)) (codes : Finset (List Bool)) :
    ConsistentCodes target (input :: inputs) codes =
      (ConsistentCodes target inputs codes).filter
        (CodeAgreesAt target · input) :=
  consistentCodes_cons_internal target input inputs codes

/-- Adding samples can only remove surviving candidate codes. -/
theorem ConsistentCodes.samples_anti {arity : ℕ}
    {target : BitString arity → Bool}
    {first second : List (BitString arity)}
    {codes : Finset (List Bool)}
    (hsub : ∀ input ∈ first, input ∈ second) :
    ConsistentCodes target second codes ⊆
      ConsistentCodes target first codes :=
  consistentCodes_samples_anti_internal hsub

/-- If every finite candidate fails somewhere, at most one failure input per
candidate empties the survivor set. -/
theorem exists_inputs_consistentCodes_eq_empty {arity : ℕ}
    (target : BitString arity → Bool) (codes : Finset (List Bool))
    (hfail : AllFailSomewhere target codes) :
    ∃ inputs : List (BitString arity),
      inputs.length ≤ codes.card ∧
        ConsistentCodes target inputs codes = ∅ :=
  exists_inputs_consistentCodes_eq_empty_internal target codes hfail

/-- Emptying a code set that covers every small typed circuit produces an
anti-checker for the target. -/
theorem IsFor.of_consistentCodes_eq_empty {arity threshold : ℕ}
    [NeZero arity] (target : BitString arity → Bool)
    (inputs : List (BitString arity)) (codes : Finset (List Bool))
    (hcovers : CoversThreshold (arity := arity) threshold codes)
    (hempty : ConsistentCodes target inputs codes = ∅) :
    IsFor target threshold inputs :=
  isFor_of_consistentCodes_eq_empty_internal
    target inputs codes hcovers hempty

/-- Finite extraction theorem: a covering set whose candidates all fail yields
an anti-checker no longer than the candidate set. -/
theorem exists_isFor_length_le_card {arity threshold : ℕ}
    [NeZero arity] (target : BitString arity → Bool)
    (codes : Finset (List Bool))
    (hcovers : CoversThreshold (arity := arity) threshold codes)
    (hfail : AllFailSomewhere target codes) :
    ∃ inputs : List (BitString arity),
      inputs.length ≤ codes.card ∧ IsFor target threshold inputs :=
  exists_isFor_length_le_card_internal target codes hcovers hfail

/-- The canonical SuccinctMCSP instance induced by the extracted anti-checker
is a no-instance. -/
theorem exists_encode_not_mem_length_le_card {arity threshold : ℕ}
    [NeZero arity] (target : BitString arity → Bool)
    (codes : Finset (List Bool))
    (hcovers : CoversThreshold (arity := arity) threshold codes)
    (hfail : AllFailSomewhere target codes) :
    ∃ inputs : List (BitString arity),
      inputs.length ≤ codes.card ∧
        (SuccinctMCSP.Instance.ofInputs threshold target inputs).encode ∉
          Complexity.SuccinctMCSP :=
  exists_encode_not_mem_length_le_card_internal
    target codes hcovers hfail

end AntiChecker

end Complexity
