/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Sequence.Semantics.Defs
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Sequence.Semantics.Internal

/-!
# Sequential fixed-width evaluation semantics

Compiled encoded-evaluation prefixes run successfully on valid descriptions
and agree, slot output by slot output, with direct evaluation of the padded raw
circuit on the same sample input.
-/


public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace Description

namespace EvaluationSequence

/-- A valid description's compiled prefix and padded raw prefix evaluate in
lockstep with corresponding gate outputs. -/
noncomputable def prefixResult {inputWidth gateBound : Nat}
    {description : Description inputWidth gateBound}
    (hdescription : description.WellFormed)
    (input : BitString inputWidth) (count : Nat)
    (hcount : count ≤ gateBound) :
    PrefixResult description input count hcount :=
  prefixResultInternal hdescription input count hcount

end EvaluationSequence

end Description

end FixedWidth

end CircuitCode

end Complexity
