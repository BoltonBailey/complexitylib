/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Counting.Defs
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Counting.Internal

/-!
# Anti-checker survivor counts

The constructive Anti-Checker Lemma builds a sample prefix while estimating
the number of encoded small circuits still consistent with its target labels.
This module exposes that exact finite count, its monotonicity under adding
samples, and its specialization to the canonical bounded circuit enumeration.

For canonical candidates, reaching zero survivors is exactly the anti-checker
condition. Approximate counters can therefore target this quantity without any
gap between encoded-circuit and typed-circuit semantics.
-/


public section

namespace Complexity

namespace AntiChecker

/-- Before any samples are chosen, every candidate code survives. -/
theorem survivorCount_nil {arity : ℕ}
    (target : BitString arity → Bool) (codes : Finset (List Bool)) :
    survivorCount target [] codes = codes.card :=
  survivorCount_nil_internal target codes

/-- Adding one input counts the previous survivors that agree with its target
label. -/
theorem survivorCount_cons {arity : ℕ}
    (target : BitString arity → Bool) (input : BitString arity)
    (inputs : List (BitString arity)) (codes : Finset (List Bool)) :
    survivorCount target (input :: inputs) codes =
      ((ConsistentCodes target inputs codes).filter
        (CodeAgreesAt target · input)).card :=
  survivorCount_cons_internal target input inputs codes

/-- A survivor count never exceeds the original candidate-set size. -/
theorem survivorCount_le_card {arity : ℕ}
    (target : BitString arity → Bool)
    (inputs : List (BitString arity)) (codes : Finset (List Bool)) :
    survivorCount target inputs codes ≤ codes.card :=
  survivorCount_le_card_internal target inputs codes

/-- Adding possible samples can only decrease the survivor count. -/
theorem survivorCount_samples_anti {arity : ℕ}
    {target : BitString arity → Bool}
    {first second : List (BitString arity)}
    {codes : Finset (List Bool)}
    (hsub : ∀ input ∈ first, input ∈ second) :
    survivorCount target second codes ≤
      survivorCount target first codes :=
  survivorCount_samples_anti_internal hsub

/-- A survivor count is zero exactly when its survivor set is empty. -/
theorem survivorCount_eq_zero_iff {arity : ℕ}
    (target : BitString arity → Bool)
    (inputs : List (BitString arity)) (codes : Finset (List Bool)) :
    survivorCount target inputs codes = 0 ↔
      ConsistentCodes target inputs codes = ∅ :=
  survivorCount_eq_zero_iff_internal target inputs codes

/-- The initial canonical survivor count is the size of the bounded circuit
enumeration. -/
theorem candidateSurvivorCount_nil {arity threshold : ℕ}
    (target : BitString arity → Bool) :
    candidateSurvivorCount target threshold [] =
      (candidateCodes arity threshold).card :=
  candidateSurvivorCount_nil_internal target

/-- Adding one input to the canonical sample prefix filters precisely the
previous canonical survivors. -/
theorem candidateSurvivorCount_cons {arity threshold : ℕ}
    (target : BitString arity → Bool) (input : BitString arity)
    (inputs : List (BitString arity)) :
    candidateSurvivorCount target threshold (input :: inputs) =
      ((ConsistentCodes target inputs (candidateCodes arity threshold)).filter
        (CodeAgreesAt target · input)).card :=
  candidateSurvivorCount_cons_internal target input inputs

/-- Canonical survivors are bounded by the canonical candidate domain. -/
theorem candidateSurvivorCount_le_card {arity threshold : ℕ}
    (target : BitString arity → Bool)
    (inputs : List (BitString arity)) :
    candidateSurvivorCount target threshold inputs ≤
      (candidateCodes arity threshold).card :=
  candidateSurvivorCount_le_card_internal target inputs

/-- Adding possible samples can only decrease the canonical survivor count. -/
theorem candidateSurvivorCount_samples_anti {arity threshold : ℕ}
    {target : BitString arity → Bool}
    {first second : List (BitString arity)}
    (hsub : ∀ input ∈ first, input ∈ second) :
    candidateSurvivorCount target threshold second ≤
      candidateSurvivorCount target threshold first :=
  candidateSurvivorCount_samples_anti_internal hsub

/-- For the canonical candidate domain, zero survivors is exactly the typed
anti-checker condition. -/
theorem candidateSurvivorCount_eq_zero_iff_isFor
    {arity threshold : ℕ} [NeZero arity]
    (target : BitString arity → Bool) (inputs : List (BitString arity)) :
    candidateSurvivorCount target threshold inputs = 0 ↔
      IsFor target threshold inputs :=
  candidateSurvivorCount_eq_zero_iff_isFor_internal target inputs

end AntiChecker

end Complexity
