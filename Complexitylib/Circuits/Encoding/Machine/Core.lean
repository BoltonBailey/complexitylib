/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.Encoding.Machine.Core.Defs
import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Hoare

/-!
# Verified streaming serialized-circuit evaluator core

This module exposes the audited staged-tape contract for the executable
three-work-tape circuit-family evaluator. It realizes the public tagged-family
semantics after defaulting malformed encodings to the machine's zero verdict,
and runs within a concrete quadratic bound.

## Main result

- `evalFamilyCoreTM_hoareTime` proves total defaulted-verdict agreement in time
  `20 * (|code| + |input| + 1)^2`.
-/

namespace Complexity

namespace CircuitCode

namespace Machine

/-- The streaming core evaluates every staged tagged-family code within the
uniform quadratic budget. Malformed codes halt with the explicit zero verdict. -/
theorem evalFamilyCoreTM_hoareTime (codeBits inputBits : List Bool)
    (initialInput : Tape) :
    evalFamilyCoreTM.HoareTime
      (FamilyCorePre codeBits inputBits initialInput)
      (FamilyCorePost codeBits inputBits initialInput)
      (evalFamilyCoreTime codeBits.length inputBits.length) :=
  Internal.evalFamilyCoreTM_hoareTime_internal codeBits inputBits initialInput

end Machine

end CircuitCode

end Complexity
