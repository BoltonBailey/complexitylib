/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Enumeration.FixedWidth.Defs
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Enumeration.FixedWidth.Internal

/-!
# Fixed-width circuit-candidate enumeration

Canonical small-circuit codes and valid fixed-width descriptions enumerate
exactly the same bounded well-formed raw circuits. Consequently, replacing the
variable-length survivor domain preserves its cardinality exactly.
-/


public section

namespace Complexity

namespace AntiChecker

/-- Canonical variable-length candidates are in exact correspondence with
valid fixed-width circuit descriptions. -/
noncomputable def candidateCodeFixedWidthEquiv (arity threshold : Nat) :
    CandidateCode arity threshold ≃
      CircuitCode.FixedWidth.ValidDescription arity threshold :=
  candidateCodeFixedWidthEquivInternal arity threshold

/-- A candidate code decodes to the raw circuit represented by its associated
fixed-width description. -/
theorem decode_candidateCodeFixedWidthEquiv
    {arity threshold : Nat} (code : CandidateCode arity threshold) :
    CircuitCode.RawCircuit.decode? code.val =
      some
        (CircuitCode.FixedWidth.Description.toRawCircuit
          (candidateCodeFixedWidthEquiv arity threshold code).val) :=
  decode_candidateCodeFixedWidthEquiv_internal code

/-- Mapping a valid fixed-width description back to the canonical candidate
domain returns the raw encoding of its represented circuit. -/
theorem candidateCodeFixedWidthEquiv_symm_val
    {arity threshold : Nat}
    (description : CircuitCode.FixedWidth.ValidDescription arity threshold) :
    ((candidateCodeFixedWidthEquiv arity threshold).symm description).val =
      description.val.toRawCircuit.encode :=
  candidateCodeFixedWidthEquiv_symm_val_internal description

/-- The fixed-width valid-description type has exactly as many members as the
canonical variable-length candidate-code set. -/
theorem card_validDescription_eq_candidateCodes (arity threshold : Nat) :
    Fintype.card
        (CircuitCode.FixedWidth.ValidDescription arity threshold) =
      (candidateCodes arity threshold).card :=
  card_validDescription_eq_candidateCodes_internal arity threshold

end AntiChecker

end Complexity
