/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Conversion.Defs
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Enumeration.Defs

/-!
# Fixed-width circuit-candidate enumeration -- definitions

This module gives the existing canonical small-circuit code set a finite type
view. The proof layer identifies it exactly with valid fixed-width circuit
descriptions at the same arity and gate threshold.
-/


@[expose] public section

namespace Complexity

namespace AntiChecker

/-- Canonical variable-length circuit codes in the existing finite candidate
set, viewed as a finite type. -/
def CandidateCode (arity threshold : Nat) :=
  ↑(candidateCodes arity threshold)

instance (arity threshold : Nat) :
    Fintype (CandidateCode arity threshold) :=
  inferInstanceAs (Fintype (↑(candidateCodes arity threshold)))

instance (arity threshold : Nat) :
    DecidableEq (CandidateCode arity threshold) :=
  inferInstanceAs (DecidableEq (↑(candidateCodes arity threshold)))

end AntiChecker

end Complexity
