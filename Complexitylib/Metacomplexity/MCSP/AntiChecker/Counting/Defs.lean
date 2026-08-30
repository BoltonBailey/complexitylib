/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Enumeration.Defs

/-!
# Anti-checker survivor counts -- definitions

This layer names the exact finite count estimated in the constructive
Anti-Checker Lemma: the number of candidate circuit descriptions consistent
with all target-labelled inputs chosen so far.
-/


@[expose] public section

namespace Complexity

namespace AntiChecker

/-- Number of codes from a finite domain that remain consistent with all
sampled target values. -/
def survivorCount {arity : ℕ} (target : BitString arity → Bool)
    (inputs : List (BitString arity)) (codes : Finset (List Bool)) : ℕ :=
  (ConsistentCodes target inputs codes).card

/-- Survivor count specialized to the canonical enumeration of circuits
within a size threshold. -/
def candidateSurvivorCount {arity : ℕ}
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity)) : ℕ :=
  survivorCount target inputs (candidateCodes arity threshold)

end AntiChecker

end Complexity
